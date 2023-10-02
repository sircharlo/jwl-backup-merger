#!/usr/bin/python
from argparse import ArgumentParser
from datetime import datetime
from dateutil import tz
from glob import glob
from math import ceil
from numpy import isnan
from os import path, makedirs, listdir, rename, remove
from shutil import copy2, make_archive, unpack_archive, rmtree
from time import time
from tqdm import tqdm

import pandas as pd
import sqlite3

parser = ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
parser.add_argument("--folder", type=str, help="Folder containing JWL files to merge")
parser.add_argument("--file", type=str, help="JWL file to merge", action="append")
args = parser.parse_args()


if args.folder is not None and not path.exists(args.folder):
    print(f"Folder not found: {args.folder}\nPlease validate the path.")
    exit()

if args.file:
    for file_path in args.file:
        if not path.isfile(file_path):
            print(f"File not found: {file_path}\nPlease validate the path.")
            exit()

if args.file and len(args.file) == 1 and args.folder is None:
    print(
        "Error: --file cannot be used on its own without --folder or at least one other --file ; you can't merge a file with itself!"
    )
    exit()


class JwlBackupProcessor:
    def __init__(self):
        self.app_name = "jw-backup-merger"
        self.debug = args.debug
        self.merged_tables = {}
        self.primary_keys = {}
        self.foreign_keys = {}
        self.fk_constraints = {}
        self.files_to_include_in_archive = []
        self.start_time = 0

        self.working_folder = path.join(".", "working")
        self.jwl_output_folder = path.join(".", "merged")
        self.merged_db_path = path.join(self.working_folder, "merged.db")

        self.output = {"info": [], "errors": []}

    def get_primary_key_names(self, temp_db, source_cursor):
        for table_name in self.get_tables(temp_db):
            source_cursor.execute(
                f"SELECT l.name FROM pragma_table_info('{table_name}') as l WHERE l.pk <>0;"
            )
            primary_key_fetcher = source_cursor.fetchall()
            if table_name not in self.primary_keys:
                self.primary_keys[table_name] = []
            if len(primary_key_fetcher) > 0:
                for primary_key_row in primary_key_fetcher:
                    primary_key = list(primary_key_row)[0]
                    if primary_key and primary_key not in self.primary_keys[table_name]:
                        self.primary_keys[table_name].append(primary_key)

    def get_foreign_key_names(self, temp_db, source_cursor):
        for table_name in self.get_tables(temp_db):
            source_cursor.execute(
                f"SELECT * FROM pragma_foreign_key_list('{table_name}');"
            )
            fk_constraint_fetcher = source_cursor.fetchall()
            if len(fk_constraint_fetcher) > 0:
                for constraints in fk_constraint_fetcher:
                    from_table = list(constraints)[2]
                    pk = list(constraints)[4]
                    to_table = table_name
                    fk = list(constraints)[3]
                    if fk:
                        if from_table not in self.fk_constraints:
                            self.fk_constraints[from_table] = {}
                        if pk not in self.fk_constraints[from_table]:
                            self.fk_constraints[from_table][pk] = set()
                        self.fk_constraints[from_table][pk].add((to_table, fk))
                        if to_table not in self.foreign_keys:
                            self.foreign_keys[to_table] = []
                        if fk not in self.foreign_keys[to_table]:
                            self.foreign_keys[to_table].append(fk)

    def process_databases(self, database_files):
        self.start_time = time()
        opened_dbs = []
        indices = []
        triggers = []
        for file_path in tqdm(database_files, desc="Loading databases into memory"):
            temp_db = sqlite3.connect(file_path)
            opened_dbs.append(temp_db)
            source_cursor = temp_db.cursor()
            self.get_primary_key_names(temp_db, source_cursor)
            self.get_foreign_key_names(temp_db, source_cursor)
            floor = self.get_primary_key_floor()
            for table in self.get_tables(temp_db):
                self.load_table_into_df(temp_db, table, floor)
            source_cursor.execute(
                "SELECT DISTINCT sql FROM sqlite_master WHERE type='index';"
            )
            indices.extend([row[0] for row in source_cursor.fetchall() if row[0]])
            source_cursor.execute(
                "SELECT DISTINCT sql FROM sqlite_master WHERE type='trigger';"
            )
            triggers.extend([row[0] for row in source_cursor.fetchall() if row[0]])

        unique_indices = set()
        for value in indices:
            cleaned_index = " ".join(value.split())
            unique_indices.add(cleaned_index)
        indices = list(unique_indices)

        unique_triggers = set()
        for value in triggers:
            cleaned_trigger = " ".join(value.split())
            unique_triggers.add(cleaned_trigger)
        triggers = list(unique_triggers)

        # Remove tables that are no longer present in latest schema (2023.09.21: v14)
        v14_tables = [
            "BlockRange",
            "Bookmark",
            "grdb_migrations",
            "IndependentMedia",
            "InputField",
            "LastModified",
            "Location",
            "Note",
            "PlaylistItem",
            "PlaylistItemAccuracy",
            "PlaylistItemIndependentMediaMap",
            "PlaylistItemLocationMap",
            "PlaylistItemMarker",
            "PlaylistItemMarkerBibleVerseMap",
            "PlaylistItemMarkerParagraphMap",
            "Tag",
            "TagMap",
            "UserMark",
        ]
        obsolete_tables = [
            value for value in self.merged_tables if value not in v14_tables
        ]
        for obsolete_table in tqdm(
            obsolete_tables,
            desc="Removing obsolete tables",
            disable=len(obsolete_tables) == 0,
        ):
            if self.debug:
                self.merged_tables[obsolete_table].to_csv(
                    path.join(
                        self.working_folder,
                        f"removed-obsolete-table-{obsolete_table}.csv",
                    ),
                )
            if obsolete_table in self.merged_tables:
                self.merged_tables.pop(obsolete_table)
            if obsolete_table in self.primary_keys:
                self.primary_keys.pop(obsolete_table)
            if obsolete_table in self.foreign_keys:
                self.foreign_keys.pop(obsolete_table)
            if obsolete_table in self.fk_constraints:
                self.fk_constraints.pop(obsolete_table)

        # Reorder tables to facilitate processing, since some tables depend on others
        table_order = [
            "Location",
            "IndependentMedia",
            "UserMark",
            "Note",
            "Bookmark",
            "PlaylistItemAccuracy",
            "PlaylistItem",
            "Tag",
        ]
        for table in table_order[::-1]:
            if table in self.merged_tables:
                popped_table = self.merged_tables.pop(table)
                self.merged_tables = {
                    table: popped_table,
                    **self.merged_tables,
                }

        if self.debug:
            for table_name in tqdm(
                self.merged_tables.keys(),
                desc="Outputting concatenated tables to CSV for debugging",
            ):
                self.merged_tables[table_name].to_csv(
                    path.join(self.working_folder, f"concat-{table_name}.csv"),
                )
        print()

        for table_name in tqdm(
            self.merged_tables.keys(),
            desc=f"Removing identical entries from concatenated tables",
        ):
            if len(list(self.merged_tables[table_name].columns)) == 1:
                unique_subset = self.merged_tables[table_name].columns.to_list()
                current_table_pk_name = self.merged_tables[table_name].columns[0]
            else:
                current_table_pk_name = self.primary_keys[table_name][0]
                unique_subset = [
                    x
                    for x in self.merged_tables[table_name].columns
                    if x != current_table_pk_name
                    and not (table_name == "Location" and x == "Title")
                ]
            grouped = (
                self.merged_tables[table_name]
                .groupby(unique_subset)[current_table_pk_name]
                .apply(list)
            )
            filtered_grouped = grouped[grouped.apply(len) > 1]
            desired_result = {values[0]: values[1:] for values in filtered_grouped}
            replacement_dict = {}
            for orig, duplicate_values in desired_result.items():
                for duplicate_value in duplicate_values:
                    replacement_dict[duplicate_value] = orig
            self.update_primary_and_foreign_keys(
                table_name, current_table_pk_name, replacement_dict
            )
            if self.debug:
                self.merged_tables[table_name].to_csv(
                    path.join(
                        self.working_folder, f"deduplicated-1st-pass-{table_name}.csv"
                    ),
                )

        unique_constraints_requiring_attention = {
            "Location": [
                [
                    "BookNumber",
                    "ChapterNumber",
                    "KeySymbol",
                    "MepsLanguage",
                    "Type",
                ],
                [
                    "KeySymbol",
                    "IssueTagNumber",
                    "MepsLanguage",
                    "DocumentId",
                    "Track",
                    "Type",
                ],
            ],
            "Bookmark": [["PublicationLocationId", "Slot"]],
            "InputField": [["LocationId", "TextTag"]],
            "Note": [
                ["Guid"],
                ["LocationId", "Title", "Content", "BlockType", "BlockIdentifier"],
            ],
            "UserMark": [["UserMarkGuid"]],
            "TagMap": [
                ["TagId", "NoteId"],
                ["TagId", "LocationId"],
                ["TagId", "PlaylistItemId"],
            ],
        }
        text_values_to_merge = {
            "Bookmark": ["Title", "Snippet"],
            "InputField": ["Value"],
            "Note": ["Title", "Content"],
        }
        for table, subsets in tqdm(
            unique_constraints_requiring_attention.items(),
            desc="Reworking data and merging obvious duplicates",
        ):
            if table in self.merged_tables:
                for subset in subsets:
                    if table == "Note":
                        self.merged_tables[table].sort_values(
                            "LastModified", ascending=False, inplace=True
                        )
                    elif table == "TagMap":
                        self.merged_tables[table].sort_values(
                            "Position", ascending=False, inplace=True
                        )
                    else:
                        self.merged_tables[table].sort_values(subset, inplace=True)
                    mask = (
                        ~self.merged_tables[table][subset]
                        .apply(lambda x: x == "")
                        .any(axis=1)
                    )
                    duplicate_values_mask = self.merged_tables[table][mask].duplicated(
                        subset=subset, keep=False
                    )
                    duplicates = self.merged_tables[table][mask][duplicate_values_mask]
                    primary_key = self.primary_keys[table][0]
                    # TODO: find a better way to handle this, using groupby instead?
                    collision_replacement_dict = {}
                    for _, row in duplicates.iterrows():
                        primary_key_value = row[self.primary_keys[table][0]]
                        key = tuple(row[subset])

                        if key not in collision_replacement_dict:
                            collision_replacement_dict[key] = [primary_key_value]
                        else:
                            collision_replacement_dict[key].append(primary_key_value)
                    collision_replacement_dict = {
                        v[0]: v[1:] for v in collision_replacement_dict.values()
                    }
                    collision_pair_replacement_dict = {}
                    for key, values in collision_replacement_dict.items():
                        for value in values:
                            if key != value:
                                collision_pair_replacement_dict[value] = key
                    if len(collision_pair_replacement_dict.keys()) == 0:
                        continue
                    if table in text_values_to_merge.keys():
                        for (
                            old_primary_key,
                            new_primary_key,
                        ) in collision_pair_replacement_dict.items():
                            old_row = self.merged_tables[table].loc[
                                self.merged_tables[table][primary_key]
                                == old_primary_key
                            ]
                            old_row_index = old_row.index[0]
                            new_row = self.merged_tables[table].loc[
                                self.merged_tables[table][primary_key]
                                == new_primary_key
                            ]
                            new_row_index = new_row.index[0]
                            for text_column in text_values_to_merge[table]:
                                old_row_text_value = old_row[text_column].values[0]
                                new_row_text_value = new_row[text_column].values[0]
                                if (
                                    len(old_row_text_value) > 0
                                    and old_row_text_value.strip()
                                    != new_row_text_value.strip()
                                ):
                                    if old_row_text_value in new_row_text_value:
                                        new_value = new_row_text_value
                                    else:
                                        new_value = self.inline_diff(
                                            old_row_text_value, new_row_text_value
                                        )
                                    self.merged_tables[table].at[
                                        new_row_index, text_column
                                    ] = new_value
                            self.merged_tables[table].drop(
                                index=old_row_index, inplace=True
                            )
                    else:
                        self.update_primary_key(
                            table, primary_key, collision_pair_replacement_dict
                        )

                    self.update_foreign_keys(
                        table, primary_key, collision_pair_replacement_dict
                    )

        # Remove orphan locations
        filter_condition = None
        for table, field in self.fk_constraints["Location"]["LocationId"]:
            # Initialize a temporary condition for the current key
            temp_condition = ~self.merged_tables["Location"]["LocationId"].isin(
                self.merged_tables[table][field]
            )
            if filter_condition is None:
                filter_condition = temp_condition
            else:
                filter_condition &= temp_condition

        orphan_locations = self.merged_tables["Location"][filter_condition]
        for index, row in tqdm(
            orphan_locations.iterrows(),
            desc="Removing locations that are no longer referenced anywhere",
            disable=len(orphan_locations) == 0,
        ):
            self.merged_tables["Location"].drop(index, inplace=True)

        # Remove notes that are empty and aren't referenced by TagMap table
        if "Note" in self.merged_tables:
            empty_notes = self.merged_tables["Note"][
                (
                    self.merged_tables["Note"]["Title"].isnull()
                    | (self.merged_tables["Note"]["Title"] == "")
                )
                & (
                    self.merged_tables["Note"]["Content"].isnull()
                    | (self.merged_tables["Note"]["Content"] == "")
                )
            ]
            untagged_empty_notes = empty_notes[
                ~empty_notes["NoteId"].isin(self.merged_tables["TagMap"]["NoteId"])
            ]
            for index, row in tqdm(
                untagged_empty_notes.iterrows(),
                desc="Removing untagged and empty notes",
                disable=len(untagged_empty_notes) == 0,
            ):
                self.merged_tables["Note"].drop(index, inplace=True)
                # Remove references in other tables to this note
                self.remove_foreign_key_value(
                    "Note",
                    self.primary_keys["Note"][0],
                    row[self.primary_keys["Note"][0]],
                )

        # Remove entries from IndependentMedia that aren't referenced by PlaylistItemIndependentMediaMap table
        if (
            "IndependentMedia" in self.merged_tables
            and "PlaylistItemIndependentMediaMap" in self.merged_tables
        ):
            orphan_independent_media = self.merged_tables["IndependentMedia"][
                ~self.merged_tables["IndependentMedia"]["IndependentMediaId"].isin(
                    self.merged_tables["PlaylistItemIndependentMediaMap"][
                        "IndependentMediaId"
                    ]
                )
            ]
            for index, row in tqdm(
                orphan_independent_media.iterrows(),
                desc="Removing references to unneeded media",
                disable=len(orphan_independent_media) == 0,
            ):
                self.merged_tables["IndependentMedia"].drop(index, inplace=True)
                # Remove references in other tables to this note
                self.remove_foreign_key_value(
                    "IndependentMedia",
                    self.primary_keys["IndependentMedia"][0],
                    row[self.primary_keys["IndependentMedia"][0]],
                )

        # Remove entries in UserMark if their LocationId does not exist in Location table
        if "UserMark" in self.merged_tables:
            usermarks_and_locations = self.merged_tables["UserMark"].merge(
                self.merged_tables["Location"][["LocationId"]],
                on="LocationId",
                how="left",
                indicator=True,
            )
            orphan_usermarks_length = len(
                usermarks_and_locations[usermarks_and_locations["_merge"] != "both"]
            )
            if orphan_usermarks_length > 0:
                progress_bar = tqdm(
                    total=orphan_usermarks_length,
                    desc="Removing overlapping highlights",
                )
                self.merged_tables["UserMark"] = usermarks_and_locations[
                    usermarks_and_locations["_merge"] == "both"
                ].drop(columns=["_merge"])
                progress_bar.update(orphan_usermarks_length)
                progress_bar.close()

        # Remove entries from BlockRange that aren't referenced by UserMark table
        if "BlockRange" in self.merged_tables:
            blockranges_and_usermarks = self.merged_tables["BlockRange"].merge(
                self.merged_tables["UserMark"][["UserMarkId"]],
                on="UserMarkId",
                how="left",
                indicator=True,
            )
            orphan_blockranges_length = len(
                blockranges_and_usermarks[blockranges_and_usermarks["_merge"] != "both"]
            )
            if orphan_blockranges_length > 0:
                progress_bar = tqdm(
                    total=orphan_blockranges_length,
                    desc="Removing references to deleted highlights",
                )
                self.merged_tables["BlockRange"] = blockranges_and_usermarks[
                    blockranges_and_usermarks["_merge"] == "both"
                ].drop(columns=["_merge"])
                progress_bar.update(orphan_blockranges_length)
                progress_bar.close()

        # TODO: Flesh out the overlapping highlights removal to include note merging when necessary
        # merged_br_df = pd.merge(
        #     self.merged_tables["BlockRange"],
        #     self.merged_tables["UserMark"],
        #     on="UserMarkId",
        # )
        # mask = merged_br_df.duplicated(
        #     subset=["LocationId", "Identifier", "StartToken", "EndToken"], keep="first"
        # )
        # overlapping_block_range_ids = merged_br_df.loc[mask, "BlockRangeId"].tolist()
        # overlapping_usermark_ids = merged_br_df.loc[mask, "UserMarkId"].tolist()
        # number_of_overlapping_ranges = max(
        #     len(overlapping_block_range_ids), len(overlapping_usermark_ids)
        # )
        # if number_of_overlapping_ranges > 0:
        #     progress_bar = tqdm(
        #         total=number_of_overlapping_ranges,
        #         desc="Removing overlapping highlights",
        #     )
        #     self.merged_tables["BlockRange"] = self.merged_tables["BlockRange"][
        #         ~self.merged_tables["BlockRange"]["BlockRangeId"].isin(
        #             overlapping_block_range_ids
        #         )
        #     ]
        #     self.merged_tables["UserMark"] = self.merged_tables["UserMark"][
        #         ~self.merged_tables["UserMark"]["UserMarkId"].isin(
        #             overlapping_usermark_ids
        #         )
        #     ]
        #     progress_bar.update(number_of_overlapping_ranges)
        #     progress_bar.close()

        if "TagMap" in self.merged_tables:
            tag_map_len = len(self.merged_tables["TagMap"])
            self.merged_tables["TagMap"].sort_values(
                ["TagId", "Position"], inplace=True
            )
            progress_bar = tqdm(
                total=tag_map_len,
                desc="Renumbering tagged items",
            )
            self.merged_tables["TagMap"]["Position"] = (
                self.merged_tables["TagMap"].groupby("TagId").cumcount()
            )
            progress_bar.update(tag_map_len)
            progress_bar.close()

        print()

        for table in tqdm(self.merged_tables, desc="Re-indexing all tables"):
            if (
                table not in self.primary_keys
                or len(list(self.merged_tables[table].columns)) == 1
                or len(self.primary_keys[table]) > 1
            ):
                continue
            self.merged_tables[table].reset_index(drop=True, inplace=True)
            new_pk_dict = {
                row[self.primary_keys[table][0]]: index + 1
                for index, row in self.merged_tables[table].iterrows()
            }
            self.update_primary_and_foreign_keys(
                table,
                self.primary_keys[table][0],
                new_pk_dict,
            )

        for opened_db in opened_dbs:
            opened_db.close()

        try:
            independent_media_files = (
                self.merged_tables["IndependentMedia"]["FilePath"].dropna().tolist()
            )
        except KeyError:
            independent_media_files = []
        try:
            playlist_item_files = (
                self.merged_tables["PlaylistItem"]["ThumbnailFilePath"]
                .dropna()
                .tolist()
            )
        except KeyError:
            playlist_item_files = []
        self.files_to_include_in_archive = list(
            set(independent_media_files + playlist_item_files)
        )

        self.save_merged_tables(indices, triggers)

    def inline_diff(self, a, b):
        import difflib

        matcher = difflib.SequenceMatcher(None, a, b)

        def process_tag(tag, i1, i2, j1, j2):
            if tag == "replace":
                return "{" + matcher.a[i1:i2] + " -> " + matcher.b[j1:j2] + "}"
            if tag == "delete":
                return "{- " + matcher.a[i1:i2] + "}"
            if tag == "equal":
                return matcher.a[i1:i2]
            if tag == "insert":
                return "{+ " + matcher.b[j1:j2] + "}"
            assert False, "Unknown tag %r" % tag

        return "".join(process_tag(*t) for t in matcher.get_opcodes())

    def update_primary_and_foreign_keys(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
    ):
        self.update_foreign_keys(
            origin_table,
            origin_primary_key,
            replacement_dict,
        )
        self.update_primary_key(
            origin_table,
            origin_primary_key,
            replacement_dict,
        )

    def update_primary_key(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
    ):
        # Update primary key
        self.merged_tables[origin_table][origin_primary_key] = self.merged_tables[
            origin_table
        ][origin_primary_key].map(lambda x: replacement_dict.get(x, x))
        subset = list(self.merged_tables[origin_table].columns)
        if origin_table == "Location":
            subset.remove("Title")
            self.merged_tables[origin_table].sort_values(
                "Title", ascending=False, inplace=True
            )
        # Drop duplicates resulting from primary key change
        self.merged_tables[origin_table].drop_duplicates(
            subset=subset, ignore_index=True, inplace=True
        )

    def update_foreign_keys(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
    ):
        if origin_table in self.fk_constraints:
            for rel_table, fk in self.fk_constraints[origin_table][origin_primary_key]:
                if rel_table in self.merged_tables:
                    # Update foreign key
                    self.merged_tables[rel_table][fk] = self.merged_tables[rel_table][
                        fk
                    ].map(lambda x: replacement_dict.get(x, x))
                    # Drop duplicates resulting from foreign key change
                    self.merged_tables[rel_table].drop_duplicates(
                        ignore_index=True, inplace=True
                    )

    def remove_foreign_key_value(self, table, foreign_key, value):
        if table in self.fk_constraints:
            for rel_table, fk in self.fk_constraints[table][foreign_key]:
                rows_to_remove = self.merged_tables[rel_table][
                    self.merged_tables[rel_table][fk] == value
                ]
                if len(rows_to_remove) > 0:
                    self.merged_tables[rel_table].drop(
                        rows_to_remove.index,
                        inplace=True,
                    )

    def get_tables(self, db):
        cursor = db.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
        return [table[0] for table in cursor.fetchall()]

    def get_primary_key_floor(self):
        floor = 0
        incrementor = 1000000
        for table_name, table_data in self.merged_tables.items():
            if table_name in self.primary_keys and len(table_data.columns) != 1:
                max_value = table_data[self.primary_keys[table_name][0]].max()
                if not isnan(max_value):
                    floor = max(floor, ceil(max_value / incrementor) * incrementor)
        return floor

    def load_table_into_df(self, db, table_name, floor):
        new_table = pd.read_sql(f"SELECT * FROM {table_name}", db)
        foreign_key_list = [
            value for values_list in self.foreign_keys.values() for value in values_list
        ]
        primary_key_list = [
            values[0]
            for values in self.primary_keys.values()
            if values and values[0].endswith("Id")
        ]
        key_list = sorted(list(set(primary_key_list + foreign_key_list)))
        if table_name not in self.merged_tables:
            self.merged_tables[table_name] = new_table
        else:
            if len(list(new_table.columns)) != 1:
                for column in new_table.columns:
                    if column in key_list and len(new_table[column]) > 0:
                        new_table[column] = new_table[column].apply(
                            lambda x: x + floor if isinstance(x, (int, float)) else x
                        )
            self.merged_tables[table_name] = pd.concat(
                [self.merged_tables[table_name], new_table],
                ignore_index=True,
            )
            self.merged_tables[table_name].reset_index(drop=True, inplace=True)

        # Make sure that some needed values in Note table are not empty
        if table_name == "Note":
            if "Created" not in self.merged_tables[table_name]:
                self.merged_tables[table_name]["Created"] = self.merged_tables[
                    table_name
                ]["LastModified"]
            self.merged_tables[table_name]["LastModified"] = (
                self.merged_tables[table_name]["LastModified"]
                .fillna(self.merged_tables[table_name]["Created"])
                .fillna(datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"))
            )
            self.merged_tables[table_name]["Created"] = (
                self.merged_tables[table_name]["Created"]
                .fillna(self.merged_tables[table_name]["LastModified"])
                .fillna(datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"))
            )

        # Remove columns no longer used in certain tables in latest schema (v14)
        obsolete_columns_per_table = {
            "PlaylistItem": [
                "AccuracyStatement",
                "StartTimeOffsetTicks",
                "EndTimeOffsetTicks",
                "ThumbnailFilename",
                "PlaylistMediaId",
            ],
            "Tag": ["ImageFilename"],
        }
        for table_to_check, obsolete_columns in obsolete_columns_per_table.items():
            if table_name == table_to_check:
                for column in obsolete_columns:
                    if column in self.merged_tables[table_name].columns:
                        self.merged_tables[table_name].drop(
                            column, axis=1, inplace=True
                        )
        self.merged_tables[table_name].fillna("", inplace=True)

    def save_merged_tables(self, indices, triggers):
        makedirs(self.working_folder, exist_ok=True)

        conn_merged = sqlite3.connect(self.merged_db_path)
        dest_cursor = conn_merged.cursor()

        dest_cursor.execute("SELECT name FROM sqlite_master WHERE type='trigger';")
        trigger_names = dest_cursor.fetchall()

        for trigger_name in trigger_names:
            trigger_name = trigger_name[0]
            dest_cursor.execute(f"DROP TRIGGER IF EXISTS {trigger_name};")
        conn_merged.commit()

        dest_cursor.execute("SELECT name FROM sqlite_master WHERE type='index';")
        index_names = dest_cursor.fetchall()

        for index_name in index_names:
            index_name = index_name[0]
            if not index_name.startswith("sqlite_"):
                dest_cursor.execute(f"DROP INDEX IF EXISTS {index_name};")
        conn_merged.commit()

        for table_name in tqdm(
            self.merged_tables.keys(),
            desc="Emptying existing database",
        ):
            dest_cursor.execute(f"DELETE FROM {table_name};")
            conn_merged.commit()

        dest_cursor.execute(
            "INSERT OR REPLACE INTO LastModified (LastModified) VALUES (strftime('%Y-%m-%dT%H:%M:%SZ', 'now'));"
        )

        for index_sql in indices:
            dest_cursor.execute(index_sql)

        for trigger_sql in triggers:
            dest_cursor.execute(trigger_sql)

        conn_merged.commit()
        dest_cursor.execute("VACUUM")
        conn_merged.commit()
        for table_name, table_data in tqdm(
            self.merged_tables.items(), desc="Inserting fresh data into database"
        ):
            if table_name == "LastModified":
                continue

            insert_sql = f"INSERT INTO {table_name} ({', '.join(table_data.columns)}) VALUES ({', '.join(['?'] * len(table_data.columns))})"
            rows_to_insert = []

            for row in table_data.values:
                cleaned_row = [
                    None
                    if cell == ""
                    and not any(keyword in col_name for keyword in ["Text", "Value"])
                    else (int(cell) if str(cell).isnumeric() else cell)
                    for col_name, cell in zip(table_data.columns, row)
                ]
                rows_to_insert.append(tuple(cleaned_row))

            try:
                dest_cursor.executemany(insert_sql, rows_to_insert)
                if self.debug:
                    self.output["info"].append(
                        (table_name, insert_sql, rows_to_insert, "NO ERROR!")
                    )
            except Exception as e:
                self.output["errors"].append((table_name, insert_sql, e))
            if self.debug or len(self.output["errors"]) > 0:
                try:
                    table_data.to_csv(
                        path.join(
                            self.working_folder,
                            f"final_{table_name}.csv",
                        )
                    )
                except Exception:
                    print(f"Could not save {table_name}.csv; continuing...")

        conn_merged.commit()

        print()

        if self.debug and len(self.output["info"]) > 0:
            print("Check the log file for debug info.")
            print()
            with open(
                path.join(self.working_folder, "info.txt"), "w", encoding="utf-8"
            ) as f:
                for error in self.output["info"]:
                    f.write(str(error) + "\n")

        if len(self.output["errors"]) > 0:
            print("Errors encountered!")
            if self.debug:
                print("Check the log file.")
                print()
                with open(
                    path.join(self.working_folder, "errors.txt"),
                    "w",
                    encoding="utf-8",
                ) as f:
                    for error in self.output["errors"]:
                        f.write(str(error) + "\n")
            else:
                print(self.output["errors"])

        dest_cursor.execute("VACUUM")
        conn_merged.commit()
        conn_merged.close()

    def createJwlFile(self):
        merged_dir = path.join(self.working_folder, "merged")
        manifest_file_path = path.join(merged_dir, "manifest.json")
        all_unzip_folder_names = list(
            directory
            for directory in listdir(self.working_folder)
            if directory != "merged"
            and path.isdir(path.join(self.working_folder, directory))
        )
        first_jwl_unzip_folder_name = all_unzip_folder_names[0]
        first_jwl_unzip_folder_path = path.join(
            self.working_folder, first_jwl_unzip_folder_name
        )

        makedirs(merged_dir, exist_ok=True)

        for file_name in tqdm(
            listdir(first_jwl_unzip_folder_path), desc="Adding base files to archive"
        ):
            if file_name.endswith(".png") or file_name.endswith(".json"):
                copy2(path.join(first_jwl_unzip_folder_path, file_name), merged_dir)
        for i in range(len(self.files_to_include_in_archive)):
            if not path.exists(self.files_to_include_in_archive[i]):
                file_path = glob(
                    path.join(
                        self.working_folder, "**", self.files_to_include_in_archive[i]
                    ),
                    recursive=True,
                )
                if file_path:
                    self.files_to_include_in_archive[i] = path.join(
                        path.dirname(file_path[0]),
                        self.files_to_include_in_archive[i],
                    )

        for file_to_include_in_archive in tqdm(
            self.files_to_include_in_archive,
            desc="Adding additional media files to archive",
            disable=len(self.files_to_include_in_archive) == 0,
        ):
            if file_to_include_in_archive != path.join(
                merged_dir, path.basename(file_to_include_in_archive)
            ):
                copy2(file_to_include_in_archive, merged_dir)

        import json

        with open(manifest_file_path, "r") as file:
            manifest_data = json.load(file)

        database_file_path = path.join(
            merged_dir, manifest_data["userDataBackup"]["databaseName"]
        )
        copy2(
            self.merged_db_path,
            database_file_path,
        )

        current_datetime = datetime.now()
        formatted_date = current_datetime.astimezone(tz.gettz("US/Eastern")).strftime(
            "%Y-%m-%dT%H:%M:%S%z"
        )
        manifest_data["creationDate"] = formatted_date

        name_timestamp = current_datetime.strftime("%Y-%m-%d-%H%M%S")
        merged_file_name = f"UserdataBackup_{name_timestamp}_{self.app_name}.jwlibrary"

        manifest_data["name"] = self.app_name

        userDataBackup = {
            "lastModifiedDate": formatted_date,
            "hash": self.calculate_sha256(database_file_path),
            "databaseName": manifest_data["userDataBackup"]["databaseName"],
            "schemaVersion": manifest_data["userDataBackup"]["schemaVersion"],
            "deviceName": self.app_name,
        }
        manifest_data["userDataBackup"] = userDataBackup

        with open(manifest_file_path, "w") as file:
            json.dump(manifest_data, file, indent=2)

        makedirs(self.jwl_output_folder, exist_ok=True)

        make_archive(
            path.join(self.jwl_output_folder, merged_file_name),
            "zip",
            merged_dir,
        )

        output_jwl_file_path = path.abspath(
            path.join(self.jwl_output_folder, merged_file_name)
        )
        rename(
            output_jwl_file_path + ".zip",
            output_jwl_file_path,
        )

        processor.cleanTempFiles()

        print()
        end_time = time()
        execution_time = end_time - self.start_time
        print(f"Work completed in {round(execution_time, 1)} seconds.")

        print()
        print("Successfully created JW Library backup containing all merged user data!")
        print()
        print("Find it here:\n- ", output_jwl_file_path)
        print()
        return output_jwl_file_path

    def cleanTempFiles(self, force=False):
        if force or (not self.debug and len(self.output["errors"]) == 0):
            if path.isdir(self.working_folder):
                rmtree(self.working_folder)
            print()
            print("Cleaned up working directory!")

    def unzipFile(self, file_path):
        basename = path.splitext(path.basename(file_path))[0]
        unzipPath = path.join(self.working_folder, basename)
        unpack_archive(file_path, extract_dir=unzipPath, format="zip")
        return unzipPath

    def getFirstDBFile(self, unzipPath):
        db_files = glob(unzipPath + "/*.db")
        if db_files:
            return db_files[0]
        else:
            return None

    def getJwlFiles(self):
        file_paths = []
        if args.file is not None or args.folder is not None:
            if args.file:
                file_paths.extend(args.file)
            if args.folder:
                for file in listdir(args.folder):
                    if not file.lower().endswith(".jwlibrary"):
                        continue
                    file_paths.append(path.join(args.folder, file))
        else:
            import tkinter as tk
            from tkinter import filedialog

            root = tk.Tk()
            root.withdraw()
            while len(file_paths) < 2:
                file_path = filedialog.askopenfilename(
                    filetypes=[("JW Library backups", "*.jwlibrary")],
                    title="Select one or more JW Library backups",
                    multiple=True,
                )
                if not file_path:
                    break
                file_paths.extend(file_path)
        if not file_paths or len(file_paths) == 1:
            print("Not enough JW Library backups found to work with!")
            print()
            if len(file_paths) > 0:
                print("Provided arguments:")
                print(
                    "\n".join(
                        ["- " + path for path in [args.file, args.folder] if path]
                    )
                )
            exit()
        processor.cleanTempFiles(force=True)
        print(
            "JW Library backup files to be merged:\n"
            + "\n".join(["- " + file_path for file_path in file_paths])
        )
        print()
        if path.exists(self.merged_db_path):
            remove(self.merged_db_path)
        db_paths = []
        for file_path in tqdm(file_paths, desc="Extracting databases"):
            db_path = self.getFirstDBFile(self.unzipFile(file_path))
            copy2(db_path, self.merged_db_path)
            db_paths.append(db_path)
        return db_paths

    def calculate_sha256(self, file_path):
        import hashlib

        hash_sha256 = hashlib.sha256()
        with open(file_path, "rb") as file:
            for chunk in iter(lambda: file.read(4096), b""):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()


if __name__ == "__main__":
    processor = JwlBackupProcessor()
    selected_paths = processor.getJwlFiles()
    processor.process_databases(selected_paths)
    processor.createJwlFile()
