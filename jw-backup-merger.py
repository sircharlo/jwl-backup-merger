#!/usr/bin/python

import argparse
from datetime import datetime
from dateutil import tz
import difflib
import glob
import hashlib
import json
import os
import pandas as pd
import random
import shutil
import sqlite3
import tkinter as tk
from tkinter import filedialog
from tqdm import tqdm
from zipfile import ZipFile

parser = argparse.ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
args = parser.parse_args()


class DatabaseProcessor:
    def __init__(self):
        self.app_name = "jw-backup-merger"
        self.debug = args.debug
        self.dataframes = {}
        self.primary_keys = {}
        self.fk_constraints = {}
        self.db = {}
        self.files_to_include_in_archive = []

        self.working_folder = os.path.join(".", "working")
        self.jwl_output_folder = os.path.join(".", "merged")
        self.merged_db_path = os.path.join(self.working_folder, "merged.db")

        self.output = {"info": [], "errors": []}

    def get_primary_key_names(self, source_cursor):
        for table_name in self.dataframes["a"].keys():
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

    def get_foreign_key_names(self, source_cursor):
        for table_name in self.dataframes["a"].keys():
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

    def process_databases(self, file_a, file_b):
        self.db["a"] = sqlite3.connect(file_a)
        self.db["b"] = sqlite3.connect(file_b)

        for dataframe_letter in ["a", "b"]:
            for table in self.get_tables(self.db[dataframe_letter]):
                self.load_table_into_df(
                    self.db[dataframe_letter], table, dataframe_letter
                )

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
        for dataframe in self.dataframes:
            for table in table_order[::-1]:
                popped_table = self.dataframes[dataframe].pop(table)
                self.dataframes[dataframe] = {
                    table: popped_table,
                    **self.dataframes[dataframe],
                }

        source_cursor = next(iter(self.db.values())).cursor()

        self.get_primary_key_names(source_cursor)

        self.get_foreign_key_names(source_cursor)

        conflicting_entries_by_dataset = {}
        print()
        for table in tqdm(self.dataframes["a"].keys(), desc=f"Analyzing tables"):
            if table == "LastModified":
                continue
            concatenated_entries = pd.concat(
                [self.dataframes["b"][table], self.dataframes["a"][table]],
                ignore_index=True,
            )

            if concatenated_entries.shape[0] == 0:
                continue

            subset_columns = concatenated_entries.columns

            common_entries = concatenated_entries[
                concatenated_entries.duplicated(subset=subset_columns, keep="first")
            ]

            for dataframe_letter in ["a", "b"]:
                if dataframe_letter not in conflicting_entries_by_dataset:
                    conflicting_entries_by_dataset[dataframe_letter] = {}
                dataset_comparer = pd.concat(
                    [common_entries, self.dataframes[dataframe_letter][table]],
                    ignore_index=True,
                )
                dataset_comparer.drop_duplicates(
                    subset=subset_columns, inplace=True, ignore_index=True, keep=False
                )
                conflicting_entries_by_dataset[dataframe_letter][
                    table
                ] = dataset_comparer

            if "merged" not in self.dataframes:
                self.dataframes["merged"] = {}
            self.dataframes["merged"][table] = common_entries.copy()
        # Perform the initial concatenation
        for dataframe_letter in conflicting_entries_by_dataset:
            for table in tqdm(
                conflicting_entries_by_dataset[dataframe_letter],
                desc="Concatenating tables from " + dataframe_letter,
            ):
                starting_pks = self.get_safe_pk_starting_point_from_merged_table(table)
                if len(self.primary_keys[table]) == 1:
                    for primary_key in self.primary_keys[table]:
                        dict_of_new_values = {}
                        if starting_pks[primary_key] is not None:
                            for index, value in enumerate(
                                conflicting_entries_by_dataset[dataframe_letter][table][
                                    primary_key
                                ],
                                start=starting_pks[primary_key],
                            ):
                                if str(value).replace(".", "").isnumeric():
                                    dict_of_new_values[value] = index
                        dict_of_new_values = {
                            key: value
                            for key, value in dict_of_new_values.items()
                            if key != value
                        }
                        if len(dict_of_new_values) == 0:
                            continue

                        self.update_primary_and_foreign_keys(
                            table,
                            primary_key,
                            dict_of_new_values,
                            dataframe_letter,
                        )

                self.dataframes["merged"][table] = pd.concat(
                    [
                        self.dataframes["merged"][table],
                        conflicting_entries_by_dataset[dataframe_letter][table],
                    ],
                    ignore_index=True,
                )

        # Process duplicated entries, first pass: automatically merge when no conflict is found
        unique_constraints = {
            "Location": [
                [
                    "BookNumber",
                    "ChapterNumber",
                    "KeySymbol",
                    "MepsLanguage",
                    "Type",
                    "IssueTagNumber",
                    "DocumentId",
                    "Track",
                ],
            ],
            "InputField": [["TextTag", "Value"]],
            "IndependentMedia": [["FilePath"]],
            "Bookmark": [["PublicationLocationId", "Slot", "Title", "Snippet"]],
            "UserMark": [
                ["ColorIndex", "LocationId", "StyleIndex", "UserMarkGuid", "Version"],
            ],
            "BlockRange": [
                ["BlockType", "Identifier", "StartToken", "EndToken", "UserMarkId"]
            ],
            "Note": [
                [
                    "Guid",
                    "UserMarkId",
                    "LocationId",
                    "Title",
                    "Content",
                    "BlockType",
                    "BlockIdentifier",
                ],
            ],
            "PlaylistItemAccuracy": [["Description"]],
            "PlaylistItemMarker": [["PlaylistItemId", "StartTimeTick"]],
            "Tag": [["Type", "Name"]],
        }
        for table, subsets in tqdm(
            unique_constraints.items(), desc="Reworking data in line with constraints"
        ):
            if table in self.dataframes["merged"]:
                for subset in subsets:
                    duplicate_values_mask = self.dataframes["merged"][table].duplicated(
                        subset=subset, keep=False
                    )
                    duplicates = self.dataframes["merged"][table][duplicate_values_mask]
                    primary_key = self.primary_keys[table][0]
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

                    self.update_primary_and_foreign_keys(
                        table, primary_key, collision_pair_replacement_dict
                    )

        for table in tqdm(
            self.dataframes["merged"],
            desc="Removing duplicates we've identified so far",
        ):
            self.dataframes["merged"][table].drop_duplicates(
                ignore_index=True, inplace=True
            )

        # Process duplicated entries, second pass: conflict is found, manual intervention might be required
        unique_constraints_requiring_attention = {
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
            desc="Reworking data in line with even more constraints",
        ):
            if table in self.dataframes["merged"]:
                for subset in subsets:
                    if table == "Note":
                        self.dataframes["merged"][table].sort_values(
                            "LastModified", ascending=False, inplace=True
                        )
                    duplicate_values_mask = self.dataframes["merged"][table].duplicated(
                        subset=subset, keep=False
                    )
                    duplicates = self.dataframes["merged"][table][duplicate_values_mask]
                    if table == "TagMap":
                        mask = (
                            self.dataframes["merged"][table][subset[0]].notna()
                            & (self.dataframes["merged"][table][subset[0]] != "")
                            & self.dataframes["merged"][table][subset[1]].notna()
                            & (self.dataframes["merged"][table][subset[1]] != "")
                        )
                        duplicate_values_mask = self.dataframes["merged"][table][
                            mask
                        ].duplicated(subset=subset, keep=False)
                        duplicates = self.dataframes["merged"][table][mask][
                            duplicate_values_mask
                        ]
                    primary_key = self.primary_keys[table][0]
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
                            old_row = self.dataframes["merged"][table].loc[
                                self.dataframes["merged"][table][primary_key]
                                == old_primary_key
                            ]
                            old_row_index = old_row.index[0]
                            new_row = self.dataframes["merged"][table].loc[
                                self.dataframes["merged"][table][primary_key]
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
                                    self.dataframes["merged"][table].at[
                                        new_row_index, text_column
                                    ] = "\n".join(diff)
                            self.dataframes["merged"][table].drop(
                                index=old_row_index, inplace=True
                            )
                    else:
                        self.update_primary_key(
                            table, primary_key, collision_pair_replacement_dict
                        )

                    self.update_foreign_keys(
                        table, primary_key, collision_pair_replacement_dict
                    )

        # Now, final cleanup times!
        # First, remove empty notes
        empty_notes = self.dataframes["merged"]["Note"][
            (
                self.dataframes["merged"]["Note"]["Title"].isnull()
                | (self.dataframes["merged"]["Note"]["Title"] == "")
            )
            & (
                self.dataframes["merged"]["Note"]["Content"].isnull()
                | (self.dataframes["merged"]["Note"]["Content"] == "")
            )
        ]
        for index, row in tqdm(empty_notes.iterrows(), desc="Removing empty notes"):
            self.dataframes["merged"]["Note"].drop(index, inplace=True)
            # Remove references in other tables to this note
            self.remove_foreign_key_value(
                "Note", self.primary_keys["Note"][0], row[self.primary_keys["Note"][0]]
            )

        # Remove entries from IndependentMedia that aren't referenced by PlaylistItemIndependentMediaMap table
        if "IndependentMedia" in self.dataframes["merged"]:
            orphan_independent_media = self.dataframes["merged"]["IndependentMedia"][
                ~self.dataframes["merged"]["IndependentMedia"][
                    "IndependentMediaId"
                ].isin(
                    self.dataframes["merged"]["PlaylistItemIndependentMediaMap"][
                        "IndependentMediaId"
                    ]
                )
            ]
            for index, row in tqdm(
                orphan_independent_media.iterrows(),
                desc="Removing references to unneeded media",
            ):
                self.dataframes["merged"]["IndependentMedia"].drop(index, inplace=True)
                # Remove references in other tables to this note
                self.remove_foreign_key_value(
                    "IndependentMedia",
                    self.primary_keys["IndependentMedia"][0],
                    row[self.primary_keys["IndependentMedia"][0]],
                )

        # Remove entries from BlockRange that aren't referenced by UserMark table
        if "BlockRange" in self.dataframes["merged"]:
            orphan_blockrange = self.dataframes["merged"]["BlockRange"][
                ~self.dataframes["merged"]["BlockRange"]["UserMarkId"].isin(
                    self.dataframes["merged"]["UserMark"]["UserMarkId"]
                )
            ]
            for index, row in tqdm(
                orphan_blockrange.iterrows(),
                desc="Removing references to obsolete highlights",
            ):
                self.dataframes["merged"]["BlockRange"].drop(index, inplace=True)
                # Remove references in other tables to this
                self.remove_foreign_key_value(
                    "BlockRange",
                    self.primary_keys["BlockRange"][0],
                    row[self.primary_keys["BlockRange"][0]],
                )

        # Remove special conflicting entries from TagMap and UserMark
        ignore_list = ["ColorIndex", "Position", "Title"]
        for table in tqdm(
            ["TagMap", "UserMark", "Location"], desc="Removing conflicting entries"
        ):
            self.dataframes["merged"][table].drop_duplicates(
                ignore_index=True,
                inplace=True,
                subset=[
                    elem
                    for elem in self.dataframes["merged"][table].columns
                    if elem not in ignore_list
                ],
            )

        # Finally, reindex all tables
        for table in tqdm(self.dataframes["merged"], desc="Re-indexing tables"):
            if len(self.primary_keys[table]) > 1:
                continue
            self.dataframes["merged"][table].reset_index(drop=True, inplace=True)
            new_pk_dict = {
                row[self.primary_keys[table][0]]: index + 1
                for index, row in self.dataframes["merged"][table].iterrows()
                if row[self.primary_keys[table][0]] != index + 1
                and str(row[self.primary_keys[table][0]]).replace(".", "").isnumeric()
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

        try:
            independent_media_files = (
                self.dataframes["merged"]["IndependentMedia"]["FilePath"]
                .dropna()
                .tolist()
            )
        except KeyError:
            independent_media_files = []
        try:
            playlist_item_files = (
                self.dataframes["merged"]["PlaylistItem"]["ThumbnailFilePath"]
                .dropna()
                .tolist()
            )
        except KeyError:
            playlist_item_files = []
        self.files_to_include_in_archive = list(
            set(independent_media_files + playlist_item_files)
        )

        self.save_merged_tables(indices, triggers)

        for dataframe in self.db.values():
            dataframe.close()

    def update_primary_key(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
        additional_dataframe_letter=None,
    ):
        # Update primary key
        self.dataframes["merged"][origin_table][origin_primary_key].replace(
            replacement_dict, inplace=True
        )
        # Drop duplicates resulting from primary key change
        self.dataframes["merged"][origin_table].drop_duplicates(
            ignore_index=True, inplace=True
        )
        if additional_dataframe_letter:
            self.dataframes[additional_dataframe_letter][origin_table][
                origin_primary_key
            ].replace(replacement_dict, inplace=True)
            self.dataframes[additional_dataframe_letter][origin_table].drop_duplicates(
                ignore_index=True, inplace=True
            )

    def update_primary_and_foreign_keys(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
        additional_dataframe_letter=None,
    ):
        self.update_primary_key(
            origin_table,
            origin_primary_key,
            replacement_dict,
            additional_dataframe_letter,
        )
        self.update_foreign_keys(
            origin_table,
            origin_primary_key,
            replacement_dict,
            additional_dataframe_letter,
        )

    def update_foreign_keys(
        self,
        origin_table,
        origin_primary_key,
        replacement_dict,
        additional_dataframe_letter=None,
    ):
        if origin_table in self.fk_constraints:
            for rel_table, fk in self.fk_constraints[origin_table][origin_primary_key]:
                if rel_table in self.dataframes["merged"]:
                    # Update foreign key
                    self.dataframes["merged"][rel_table][fk].replace(
                        replacement_dict, inplace=True
                    )
                    # Drop duplicates resulting from foreign key change
                    self.dataframes["merged"][rel_table].drop_duplicates(
                        ignore_index=True, inplace=True
                    )
                if (
                    additional_dataframe_letter
                    and rel_table in self.dataframes[additional_dataframe_letter]
                ):
                    self.dataframes[additional_dataframe_letter][rel_table][fk].replace(
                        replacement_dict, inplace=True
                    )
                    # Drop duplicates resulting from foreign key change
                    self.dataframes[additional_dataframe_letter][
                        rel_table
                    ].drop_duplicates(ignore_index=True, inplace=True)

    def remove_foreign_key_value(self, table, foreign_key, value):
        if table in self.fk_constraints:
            for rel_table, fk in self.fk_constraints[table][foreign_key]:
                rows_to_remove = self.dataframes["merged"][rel_table][
                    self.dataframes["merged"][rel_table][fk] == value
                ]
                if len(rows_to_remove) > 0:
                    self.dataframes["merged"][rel_table].drop(
                        rows_to_remove.index,
                        inplace=True,
                    )

    def get_safe_pk_starting_point_from_merged_table(self, table_name):
        randomizer = random.randint(100000, 1000000)
        if table_name not in self.primary_keys:
            return None
        highest_pks = None
        for key in self.primary_keys[table_name]:
            highest_pk = None
            if not self.dataframes["merged"][table_name][key].empty:
                highest_pk_lookup = max(self.dataframes["merged"][table_name][key])
                if str(highest_pk_lookup).replace(".", "").isnumeric() and (
                    not str(highest_pk).isnumeric() or highest_pk_lookup > highest_pk
                ):
                    highest_pk = max(highest_pk_lookup * randomizer, randomizer)
            if highest_pks is None:
                highest_pks = {}
            if highest_pk is None or highest_pk == 0:
                highest_pk = randomizer
            highest_pks[key] = highest_pk
        return highest_pks

    def get_tables(self, db):
        table_query = "SELECT name FROM sqlite_master WHERE type='table';"
        cursor = db.cursor()
        cursor.execute(table_query)
        return [table[0] for table in cursor.fetchall()]

    def load_table_into_df(self, db, table_name, destination_letter):
        if not destination_letter in self.dataframes:
            self.dataframes[destination_letter] = {}
        self.dataframes[destination_letter][table_name] = pd.read_sql_query(
            f"SELECT * FROM {table_name}", db
        )
        self.dataframes[destination_letter][table_name].fillna("", inplace=True)

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
            self.dataframes["merged"].keys(),
            desc="Deleting all data from existing database",
        ):
            dest_cursor.execute(f"DELETE FROM {table_name};")
            conn_merged.commit()

        for index_sql in indices:
            dest_cursor.execute(index_sql)

        for trigger_sql in triggers:
            dest_cursor.execute(trigger_sql)

        conn_merged.commit()
        dest_cursor.execute("VACUUM")
        conn_merged.commit()
        for table_name, table_data in tqdm(
            self.dataframes["merged"].items(), desc="Inserting merged data into tables"
        ):
            if self.debug:
                try:
                    table_data.to_excel(
                        os.path.join(self.working_folder, f"{table_name}.xlsx")
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
                if table_name != "LastModified":
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

    def createJwlFile(self, final=False):
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
            os.listdir(first_jwl_unzip_folder_path), desc="Copying base files"
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
            self.files_to_include_in_archive, desc="Copying additional media files"
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
            os.path.join(".", self.jwl_output_folder, merged_file_name),
            "zip",
            merged_dir,
        )

        output_jwl_file_path = os.path.join(
            ".", self.jwl_output_folder, merged_file_name
        )
        os.rename(
            output_jwl_file_path + ".zip",
            output_jwl_file_path,
        )

        if final:
            print()
            print("Created JWL file! Full path:", output_jwl_file_path)

        return output_jwl_file_path

    def cleanTempFiles(self):
        if not self.debug:
            if os.path.exists(self.working_folder):
                shutil.rmtree(self.working_folder)
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
        root = tk.Tk()
        root.withdraw()
        file_paths = []
        while len(file_paths) < 2:
            file_path = filedialog.askopenfilename(
                filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")],
                title="Select one or more backup files",
                multiple=True,
            )
            if not file_path:
                exit()
            file_paths.extend(file_path)
        print(
            "Files selected:\n"
            + "\n".join(["- " + file_path for file_path in file_paths])
        )
        print()
        if os.path.exists(self.merged_db_path):
            os.remove(self.merged_db_path)
        db_paths = []
        for file_path in file_paths:
            db_path = self.extractDatabase(file_path)
            if not os.path.exists(self.merged_db_path):
                shutil.copy2(db_path, self.merged_db_path)
            db_paths.append(db_path)
        print(
            "Databases extracted:\n"
            + "\n".join(["- " + db_path for db_path in db_paths])
        )
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
        while len(file_paths) > 2:
            batch = file_paths[:2]
            print()
            print("============================")
            print()
            print(
                "Currently merging:\n"
                + "\n".join(["- " + file_path for file_path in batch])
            )
            self.process_databases(*batch)
            jwl_file = self.createJwlFile()
            file_paths = [self.extractDatabase(jwl_file)] + file_paths[2:]
        if file_paths:
            print()
            print("============================")
            print(
                "Currently merging:\n"
                + "\n".join(["- " + file_path for file_path in file_paths])
            )
            self.process_databases(*file_paths)
            self.createJwlFile(final=True)


if __name__ == "__main__":
    processor = DatabaseProcessor()
    selected_paths = processor.getJwlFiles()
    processor.process_multiple_databases(selected_paths)
    processor.cleanTempFiles()
