#!/usr/bin/python
import argparse
from datetime import datetime
from dateutil import tz
import difflib
import glob
import hashlib
import json
import math
import os
import pandas as pd
import shutil
import sqlite3
import time
from tqdm import tqdm
from zipfile import ZipFile

start_time = time.time()

parser = argparse.ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
parser.add_argument("--folder", type=str, help="Folder containing JWL files to merge")
parser.add_argument("--file", type=str, help="JWL file to merge", action="append")
args = parser.parse_args()


if args.folder and not os.path.exists(args.folder):
    print(f"Folder not found: {args.folder}\nPlease validate the path.")
    exit()

if args.file:
    for file_path in args.file:
        if not os.path.exists(file_path) or not os.path.isfile(file_path):
            print(f"File not found: {file_path}\nPlease validate the path.")
            exit()

if args.file and len(args.file) == 1 and args.folder is None:
    print(
        "Error: --file cannot be used on its own without another --file or --folder; you can't merge a file with itself!"
    )
    exit()


class DatabaseProcessor:
    def __init__(self):
        self.app_name = "jw-backup-merger"
        self.debug = args.debug
        self.merged_tables = {}
        self.primary_keys = {}
        self.foreign_keys = {}
        self.fk_constraints = {}
        self.files_to_include_in_archive = []

        self.working_folder = os.path.join(".", "working")
        self.jwl_output_folder = os.path.join(".", "merged")
        self.merged_db_path = os.path.join(self.working_folder, "merged.db")

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
                            self.fk_constraints[from_table][pk] = []
                        self.fk_constraints[from_table][pk].append((to_table, fk))
                        if to_table not in self.foreign_keys:
                            self.foreign_keys[to_table] = []
                        self.foreign_keys[to_table].append(fk)

    def process_databases(self, database_files):
        source_cursor = None
        opened_dbs = []
        for file_path in tqdm(database_files, desc="Loading databases into memory"):
            temp_db = sqlite3.connect(file_path)
            opened_dbs.append(temp_db)
            if source_cursor is None:
                source_cursor = temp_db.cursor()
                self.get_primary_key_names(temp_db, source_cursor)
                self.get_foreign_key_names(temp_db, source_cursor)
            floor = self.get_primary_key_floor()
            for table in self.get_tables(temp_db):
                self.load_table_into_df(temp_db, table, floor)

        # Reorder tables to facilitate processing, since some tables depend on others
        table_order = [
            "Location",
            "IndependentMedia",
            "UserMark",
            "Note",
            "Bookmark",
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
                desc="Outputting concatenated tables to Excel for debugging",
            ):
                self.merged_tables[table_name].to_excel(
                    os.path.join(self.working_folder, f"concat-{table_name}.xlsx"),
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
                print("Saving deduplicated table to Excel:", table_name)
                self.merged_tables[table_name].to_excel(
                    os.path.join(
                        self.working_folder, f"deduplicated-1st-pass-{table_name}.xlsx"
                    ),
                )

        # De-duplicate entries
        unique_constraints_requiring_attention = {
            "Location": [
                [
                    "BookNumber",
                    "ChapterNumber",
                    "DocumentId",
                    "Track",
                    "IssueTagNumber",
                    "KeySymbol",
                    "MepsLanguage",
                    "Type",
                ]
            ],
            "Bookmark": [["PublicationLocationId", "Slot"]],
            "InputField": [["LocationId", "TextTag"]],
            "Note": [
                ["Guid"],
                ["LocationId", "Title", "Content", "BlockType", "BlockIdentifier"],
            ],
            "UserMark": [["UserMarkGuid"]],
            "BlockRange": [
                ["BlockType", "Identifier", "StartToken", "EndToken", "UserMarkId"]
            ],
            "TagMap": [
                ["TagId", "NoteId"],
                ["TagId", "LocationId"],
                ["TagId", "PlaylistItemId"],
                ["TagId", "Position"],
            ],
        }
        text_values_to_merge = {
            "Bookmark": ["Title", "Snippet"],
            "InputField": ["Value"],
            "Note": ["Title", "Content"],
        }
        for table, subsets in tqdm(
            unique_constraints_requiring_attention.items(),
            desc="Reworking data and merging duplicates",
        ):
            if table in self.merged_tables:
                for subset in subsets:
                    if table == "Note":
                        self.merged_tables[table].sort_values(
                            "LastModified", ascending=False, inplace=True
                        )
                    duplicate_values_mask = self.merged_tables[table].duplicated(
                        subset=subset, keep=False
                    )
                    duplicates = self.merged_tables[table][duplicate_values_mask]
                    if table == "TagMap":
                        mask = (
                            self.merged_tables[table][subset[0]].notna()
                            & (self.merged_tables[table][subset[0]] != "")
                            & self.merged_tables[table][subset[1]].notna()
                            & (self.merged_tables[table][subset[1]] != "")
                        )
                        duplicate_values_mask = self.merged_tables[table][
                            mask
                        ].duplicated(subset=subset, keep=False)
                        duplicates = self.merged_tables[table][mask][
                            duplicate_values_mask
                        ]
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
                                    and not new_row_text_value.strip()
                                    == old_row_text_value.strip()
                                ):
                                    differ = difflib.Differ()
                                    diff = differ.compare(
                                        old_row_text_value.splitlines(),
                                        new_row_text_value.splitlines(),
                                    )
                                    self.merged_tables[table].at[
                                        new_row_index, text_column
                                    ] = "\n".join(diff)
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

        # Remove empty notes that aren't referenced by TagMap table
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

        # Remove entries from BlockRange that aren't referenced by UserMark table
        if "BlockRange" in self.merged_tables:
            orphan_blockrange = self.merged_tables["BlockRange"][
                ~self.merged_tables["BlockRange"]["UserMarkId"].isin(
                    self.merged_tables["UserMark"]["UserMarkId"]
                )
            ]
            for index, row in tqdm(
                orphan_blockrange.iterrows(),
                desc="Removing references to obsolete highlights",
                disable=len(orphan_blockrange) == 0,
            ):
                self.merged_tables["BlockRange"].drop(index, inplace=True)
                # Remove references in other tables to this
                self.remove_foreign_key_value(
                    "BlockRange",
                    self.primary_keys["BlockRange"][0],
                    row[self.primary_keys["BlockRange"][0]],
                )

        # # Remove special conflicting entries from TagMap and UserMark
        ignore_dict = {
            "TagMap": "Position",
            "UserMark": "ColorIndex",
            "Location": "Title",
        }
        for table, ignore_column in tqdm(
            ignore_dict.items(),
            desc="Removing duplicate entries for highlights, tags, and locations",
        ):
            self.merged_tables[table].drop_duplicates(
                ignore_index=True,
                inplace=True,
                subset=[
                    elem
                    for elem in self.merged_tables[table].columns
                    if elem != ignore_column
                ],
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
            desc="Removing unneeded locations",
            disable=len(orphan_locations) == 0,
        ):
            self.merged_tables["Location"].drop(index, inplace=True)

        print()
        # Finally, reindex all tables
        for table in tqdm(self.merged_tables, desc="Re-indexing entries in all tables"):
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

        source_cursor.execute(
            "SELECT name, tbl_name, sql FROM sqlite_master WHERE type='index';"
        )
        indices_fetcher = source_cursor.fetchall()

        source_cursor.execute(
            "SELECT name, tbl_name, sql FROM sqlite_master WHERE type='trigger';"
        )
        triggers_fetcher = source_cursor.fetchall()

        indices = []
        triggers = []
        for index_info in indices_fetcher:
            index_name, table_name, index_sql = index_info
            indices.append(index_sql)
        for trigger_info in triggers_fetcher:
            trigger_name, table_name, trigger_sql = trigger_info
            triggers.append(trigger_sql)
        indices = [x for x in list(set(indices)) if x]
        triggers = [x for x in list(set(triggers)) if x]

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
        # Drop duplicates resulting from primary key change
        self.merged_tables[origin_table].drop_duplicates(
            ignore_index=True, inplace=True
        )

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
        table_query = "SELECT name FROM sqlite_master WHERE type='table';"
        cursor = db.cursor()
        cursor.execute(table_query)
        return [table[0] for table in cursor.fetchall()]

    def get_primary_key_floor(self):
        highest_value = None
        floor = 0
        incrementer = 100000
        for table_name in self.merged_tables.keys():
            if (
                table_name in self.primary_keys
                and len(list(self.merged_tables[table_name].columns)) != 1
            ):
                max_value = self.merged_tables[table_name][
                    self.primary_keys[table_name][0]
                ].max()
                if highest_value is None or max_value > highest_value:
                    highest_value = max_value
                    floor = math.ceil(highest_value / incrementer) * incrementer
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
        self.merged_tables[table_name].fillna("", inplace=True)

    def save_merged_tables(self, indices, triggers):
        os.makedirs(self.working_folder, exist_ok=True)

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
            if self.debug:
                try:
                    table_data.to_excel(
                        os.path.join(
                            self.working_folder,
                            f"{datetime.now().strftime('%Y-%m-%d-%H%M%S') }_{table_name}.xlsx",
                        )
                    )
                except:
                    print(f"Could not save {table_name}.xlsx; continuing...")
            insert_sql = f"INSERT INTO {table_name} ({', '.join(table_data.columns)}) VALUES ({', '.join(['?'] * len(table_data.columns))})"
            rows_to_insert = [
                tuple(
                    [
                        None
                        if cell == ""
                        and not (
                            "Text" in table_data.columns[i]
                            or "Value" in table_data.columns[i]
                        )
                        else int(cell)
                        if str(cell).isnumeric()
                        else cell
                        for i, cell in enumerate(row)
                    ]
                )
                for row in table_data.values
            ]
            for index, row in enumerate(rows_to_insert):
                if table_name == "LastModified":
                    continue
                try:
                    dest_cursor.execute(insert_sql, row)
                    if self.debug:
                        self.output["info"].append(
                            (
                                table_name,
                                insert_sql,
                                rows_to_insert[index],
                                "NO ERROR!",
                            )
                        )
                except Exception as e:
                    self.output["errors"].append(
                        (table_name, insert_sql, rows_to_insert[index], e)
                    )
            conn_merged.commit()
        print()

        if self.debug and len(self.output["info"]) > 0:
            print("Check the log file for debug info.")
            print()
            with open(
                os.path.join(self.working_folder, "info.txt"), "w", encoding="utf-8"
            ) as f:
                for error in self.output["info"]:
                    f.write(str(error) + "\n")

        if len(self.output["errors"]) > 0:
            print("Errors encountered!")
            if self.debug:
                print("Check the log file.")
                print()
                with open(
                    os.path.join(self.working_folder, "errors.txt"),
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
        merged_dir = os.path.join(self.working_folder, "merged")
        manifest_file_path = os.path.join(merged_dir, "manifest.json")
        all_unzip_folder_names = list(
            directory
            for directory in os.listdir(self.working_folder)
            if directory != "merged"
            and os.path.isdir(os.path.join(self.working_folder, directory))
        )
        first_jwl_unzip_folder_name = all_unzip_folder_names[0]
        first_jwl_unzip_folder_path = os.path.join(
            self.working_folder, first_jwl_unzip_folder_name
        )

        if not os.path.exists(merged_dir):
            os.mkdir(merged_dir)

        for file_name in tqdm(
            os.listdir(first_jwl_unzip_folder_path), desc="Adding base files to archive"
        ):
            if file_name.endswith(".png") or file_name.endswith(".json"):
                shutil.copy2(
                    os.path.join(first_jwl_unzip_folder_path, file_name), merged_dir
                )
        for i in range(len(self.files_to_include_in_archive)):
            if not os.path.exists(self.files_to_include_in_archive[i]):
                file_path = glob.glob(
                    os.path.join(
                        self.working_folder, "**", self.files_to_include_in_archive[i]
                    ),
                    recursive=True,
                )
                if file_path:
                    self.files_to_include_in_archive[i] = os.path.join(
                        os.path.dirname(file_path[0]),
                        self.files_to_include_in_archive[i],
                    )

        for file_to_include_in_archive in tqdm(
            self.files_to_include_in_archive,
            desc="Adding additional media files to archive",
            disable=len(self.files_to_include_in_archive) == 0,
        ):
            if file_to_include_in_archive != os.path.join(
                merged_dir, os.path.basename(file_to_include_in_archive)
            ):
                shutil.copy2(file_to_include_in_archive, merged_dir)

        with open(manifest_file_path, "r") as file:
            manifest_data = json.load(file)

        database_file_path = os.path.join(
            merged_dir, manifest_data["userDataBackup"]["databaseName"]
        )
        shutil.copy2(
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

        manifest_data["name"] = merged_file_name

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

        if not os.path.exists(self.jwl_output_folder):
            os.mkdir(self.jwl_output_folder)

        shutil.make_archive(
            os.path.join(self.jwl_output_folder, merged_file_name),
            "zip",
            merged_dir,
        )

        output_jwl_file_path = os.path.abspath(
            os.path.join(self.jwl_output_folder, merged_file_name)
        )
        os.rename(
            output_jwl_file_path + ".zip",
            output_jwl_file_path,
        )

        processor.cleanTempFiles()

        print()
        end_time = time.time()
        execution_time = end_time - start_time
        print(f"Work completed in {round(execution_time, 1)} seconds.")

        print()
        print(
            "Successfully created JW Library backup file containing all merged user data!"
        )
        print()
        print("Find it here:\n- ", output_jwl_file_path)
        print()
        return output_jwl_file_path

    def cleanTempFiles(self):
        if not self.debug:
            if os.path.exists(self.working_folder):
                shutil.rmtree(self.working_folder)
            print()
            print("Cleaned up temporary files!")

    def unzipFile(self, file_path):
        basename = os.path.basename(file_path)
        basename = os.path.splitext(basename)[0]
        unzipPath = os.path.join(self.working_folder, basename)
        with ZipFile(file_path, "r") as zip:
            zip.extractall(path=unzipPath)
        return unzipPath

    def getFirstDBFile(self, unzipPath):
        db_files = glob.glob(unzipPath + "/*.db")
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
                for file in os.listdir(args.folder):
                    if not file.lower().endswith(".jwlibrary"):
                        continue
                    file_paths.append(os.path.join(args.folder, file))
        else:
            import tkinter as tk
            from tkinter import filedialog

            root = tk.Tk()
            root.withdraw()
            while len(file_paths) < 2:
                file_path = filedialog.askopenfilename(
                    filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")],
                    title="Select one or more backup files",
                    multiple=True,
                )
                if not file_path:
                    break
                file_paths.extend(file_path)
        if not file_paths or len(file_paths) == 1:
            print("Not enough .JWLIBRARY files found to work with!")
            print()
            if len(file_paths) > 0:
                print("Provided arguments:")
                print(
                    "\n".join(
                        ["- " + path for path in [args.file, args.folder] if path]
                    )
                )
            exit()
        print(
            "JW Library backup files to be merged:\n"
            + "\n".join(["- " + file_path for file_path in file_paths])
        )
        print()
        if os.path.exists(self.merged_db_path):
            os.remove(self.merged_db_path)
        db_paths = []
        for file_path in tqdm(file_paths, desc="Extracting databases"):
            db_path = self.extractDatabase(file_path)
            if not os.path.exists(self.merged_db_path):
                shutil.copy2(db_path, self.merged_db_path)
            db_paths.append(db_path)
        return db_paths

    def extractDatabase(self, file_path):
        unzip_path = self.unzipFile(file_path)
        return self.getFirstDBFile(unzip_path)

    def calculate_sha256(self, file_path):
        hash_sha256 = hashlib.sha256()
        with open(file_path, "rb") as file:
            for chunk in iter(lambda: file.read(4096), b""):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()

    def process_multiple_databases(self, file_paths):
        self.process_databases(file_paths)
        self.createJwlFile()


if __name__ == "__main__":
    processor = DatabaseProcessor()
    selected_paths = processor.getJwlFiles()
    processor.process_multiple_databases(selected_paths)
