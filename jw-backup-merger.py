#!/usr/bin/python

from datetime import datetime
import difflib
import glob
import hashlib
import json
import os
import time
import pandas as pd
import shutil
import sqlite3
import tkinter as tk
from tkinter import filedialog
from dateutil import tz
from tqdm import tqdm
from zipfile import ZipFile


class DatabaseProcessor:
    def __init__(self):
        self.dataframes = {}
        self.primary_keys = {}
        self.fk_constraints = {}
        self.db = {}
        self.files_to_include_in_archive = []

        self.working_folder = os.path.join(".", "working")
        self.jwl_output_folder = os.path.join(".", "merged")

        self.output = {"info": [], "errors": []}

    def get_primary_keys(self, source_cursor):
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

    def get_foreign_keys(self, source_cursor):
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

        self.get_primary_keys(source_cursor)

        self.get_foreign_keys(source_cursor)

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

        # Perform the initial merge
        for dataframe_letter in conflicting_entries_by_dataset:
            for table in tqdm(
                conflicting_entries_by_dataset[dataframe_letter],
                desc="Merging tables from " + dataframe_letter,
            ):
                highest_pks = self.get_highest_pks_from_merged_table(table)
                for primary_key in self.primary_keys[table]:
                    dict_of_new_values = {}
                    if highest_pks[primary_key] is not None:
                        for index, value in enumerate(
                            conflicting_entries_by_dataset[dataframe_letter][table][
                                primary_key
                            ],
                            start=highest_pks[primary_key] + 1,
                        ):
                            if str(value).replace(".", "").isnumeric():
                                dict_of_new_values[value] = index

                    if len(dict_of_new_values) == 0:
                        continue

                    # Update primary keys
                    conflicting_entries_by_dataset[dataframe_letter][table][
                        primary_key
                    ] = conflicting_entries_by_dataset[dataframe_letter][table][
                        primary_key
                    ].replace(
                        dict_of_new_values
                    )

                    # Update foreign keys
                    if table in self.fk_constraints:
                        for rel_table, fk in self.fk_constraints[table][primary_key]:
                            if (
                                rel_table
                                in conflicting_entries_by_dataset[dataframe_letter]
                            ):
                                conflicting_entries_by_dataset[dataframe_letter][
                                    rel_table
                                ][fk] = conflicting_entries_by_dataset[
                                    dataframe_letter
                                ][
                                    rel_table
                                ][
                                    fk
                                ].replace(
                                    dict_of_new_values
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
                # ["ColorIndex", "LocationId", "StyleIndex", "Version"] # eventually, manually dedupe colors here
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
                [
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
            "TagMap": [["TagId", "Position", "NoteId", "PlaylistItemId", "LocationId"]],
        }
        for table, subsets in unique_constraints.items():
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
                    print(
                        "Table:", table, "Subset:", subset, "Primary key:", primary_key
                    )
                    print(collision_pair_replacement_dict)
                    self.dataframes["merged"][table][primary_key].replace(
                        collision_pair_replacement_dict, inplace=True
                    )
                    self.dataframes["merged"][table].drop_duplicates(
                        subset=subset, ignore_index=True, inplace=True
                    )

                    # Update foreign keys
                    if table in self.fk_constraints:
                        print("table:", table)
                        for rel_table, fk in self.fk_constraints[table][primary_key]:
                            if rel_table in self.dataframes["merged"]:
                                print("rel_table:", rel_table)
                                print("fk:", fk)
                                self.dataframes["merged"][rel_table][fk].replace(
                                    collision_pair_replacement_dict, inplace=True
                                )
                    # if duplicates.shape[0] > 0:
                    #     self.dataframes["merged"][table].sort_values(subset).to_excel(
                    #         table + "_final" + ".xlsx", index=False
                    #     )
                    #     duplicates.sort_values(subset).to_excel(
                    #         table + "_duplicates" + ".xlsx", index=False
                    #     )
        for table in self.dataframes["merged"]:
            self.dataframes["merged"][table].drop_duplicates(
                ignore_index=True, inplace=True
            )

        # Process duplicated entries, second pass: conflict is found, manual intervention is required
        unique_constraints_requiring_attention = {
            "Bookmark": [["PublicationLocationId", "Slot"]],
            "Note": [["Guid"]],
            "InputField": [["TextTag"]],
            "UserMark": [["UserMarkGuid"]],
            "TagMap": [
                ["TagId", "Position"],
                ["TagId", "NoteId"],
                ["TagId", "LocationId"],
                ["TagId", "PlaylistItemId"],
            ],
        }
        for table, subsets in unique_constraints_requiring_attention.items():
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
                        duplicates = self.dataframes["merged"][table][mask][duplicate_values_mask]

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
                    print(
                        "Table:", table, "Subset:", subset, "Primary key:", primary_key
                    )
                    print(collision_pair_replacement_dict)
                    if table == "Note":
                        for (
                            old_primary_key,
                            new_primary_key,
                        ) in collision_pair_replacement_dict.items():
                            old_row = self.dataframes["merged"][table].loc[
                                self.dataframes["merged"][table][primary_key]
                                == old_primary_key
                            ]
                            old_row_index = old_row.index[0]
                            old_row_title_value = old_row["Title"].values[0]
                            old_row_content_value = old_row["Content"].values[0]

                            new_row = self.dataframes["merged"][table].loc[
                                self.dataframes["merged"][table][primary_key]
                                == new_primary_key
                            ]
                            new_row_index = new_row.index[0]
                            new_row_title_value = new_row["Title"].values[0]
                            new_row_content_value = new_row["Content"].values[0]

                            if (
                                len(old_row_content_value) > 0
                                and not new_row_content_value.strip()
                                == old_row_content_value.strip()
                            ):
                                differ = difflib.Differ()
                                diff = differ.compare(
                                    old_row_content_value.splitlines(),
                                    new_row_content_value.splitlines(),
                                )
                                self.dataframes["merged"][table].at[
                                    new_row_index, "Content"
                                ] = "\n".join(diff)
                            if (
                                len(old_row_title_value) > 0
                                and not new_row_title_value.strip()
                                == old_row_title_value.strip()
                            ):
                                differ = difflib.Differ()
                                diff = differ.compare(
                                    old_row_title_value.splitlines(),
                                    new_row_title_value.splitlines(),
                                )
                                self.dataframes["merged"][table].at[
                                    new_row_index, "Title"
                                ] = "\n".join(diff)
                            self.dataframes["merged"][table].drop(
                                index=old_row_index, inplace=True
                            )
                    else:
                        print(
                            "Table:",
                            table,
                            "Subset:",
                            subset,
                            "Primary key:",
                            primary_key,
                        )
                        print(collision_pair_replacement_dict)
                        print(duplicates)
                        self.dataframes["merged"][table][primary_key].replace(
                            collision_pair_replacement_dict, inplace=True
                        )
                        self.dataframes["merged"][table].drop_duplicates(
                            subset=subset, ignore_index=True, inplace=True
                        )

                    # # Update foreign keys
                    if table in self.fk_constraints:
                        print("table:", table)
                        for rel_table, fk in self.fk_constraints[table][primary_key]:
                            if rel_table in self.dataframes["merged"]:
                                print("rel_table:", rel_table)
                                print("fk:", fk)
                                self.dataframes["merged"][rel_table][fk].replace(
                                    collision_pair_replacement_dict, inplace=True
                                )
                    # if duplicates.shape[0] > 0:
                    #     self.dataframes["merged"][table].to_excel(
                    #         table + "_final" + ".xlsx", index=False
                    #     )
                    #     duplicates.to_excel(
                    #         table + "_duplicates" + ".xlsx", index=False
                    #     )

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

        source_cursor.execute("SELECT FilePath FROM IndependentMedia;")
        self.files_to_include_in_archive.extend(
            [file[0] for file in source_cursor.fetchall()]
        )
        source_cursor.execute("SELECT ThumbnailFilePath FROM PlaylistItem;")
        self.files_to_include_in_archive.extend(
            [file[0] for file in source_cursor.fetchall()]
        )
        self.files_to_include_in_archive = list(set(self.files_to_include_in_archive))

        self.save_merged_tables(indices, triggers)

        for dataframe in self.db.values():
            dataframe.close()

    def get_highest_pks_from_merged_table(self, table_name):
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
                    highest_pk = highest_pk_lookup
            if highest_pks is None:
                highest_pks = {}
            if highest_pk is not None:
                highest_pks[key] = highest_pk
            else:
                highest_pks[key] = None
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

        conn_merged = sqlite3.connect(os.path.join(self.working_folder, "merged.db"))
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

        for table_name in self.dataframes["merged"].keys():
            dest_cursor.execute(f"DELETE FROM {table_name};")
            conn_merged.commit()

        for index_sql in indices:
            dest_cursor.execute(index_sql)

        for trigger_sql in triggers:
            dest_cursor.execute(trigger_sql)

        conn_merged.commit()
        print()
        print("Deleted all data from existing database to prepare for reinsertion...")
        dest_cursor.execute("VACUUM")
        conn_merged.commit()
        for table_name, table_data in self.dataframes["merged"].items():
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
            for index, row in tqdm(
                enumerate(rows_to_insert),
                total=len(rows_to_insert),
                desc=f"Inserting merged data into {table_name}",
            ):
                if table_name != "LastModified":
                    try:
                        dest_cursor.execute(insert_sql, row)
                        self.output["info"].append(
                            (table_name, insert_sql, rows_to_insert[index], "NO ERROR!")
                        )
                    except Exception as e:
                        self.output["errors"].append(
                            (table_name, insert_sql, rows_to_insert[index], e)
                        )
            conn_merged.commit()
        print()

        if len(self.output["info"]) > 0:
            print("Check the log file for debug info.")
            print()
            with open(os.path.join(".", "info.txt"), "w", encoding="utf-8") as f:
                for error in self.output["info"]:
                    f.write(str(error) + "\n")

        if len(self.output["errors"]) > 0:
            print("Errors encountered! Check the log file.")
            print()
            with open(os.path.join(".", "errors.txt"), "w", encoding="utf-8") as f:
                for error in self.output["errors"]:
                    f.write(str(error) + "\n")

        dest_cursor.execute("VACUUM")
        conn_merged.commit()

        conn_merged.close()

    def createJwlFile(self):
        print("Creating JWL file...")
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

        for folder in all_unzip_folder_names:
            full_path = os.path.join(self.working_folder, folder)
            for filename in tqdm(
                os.listdir(full_path), desc=f"Copying files from {folder}"
            ):
                file_path = os.path.join(full_path, filename)
                # Find files referenced in DB and include them in resulting archive...
                if (
                    os.path.isfile(file_path)
                    and filename in self.files_to_include_in_archive
                ):
                    shutil.copy2(file_path, merged_dir)

        with open(manifest_file_path, "r") as file:
            manifest_data = json.load(file)

        database_file_path = os.path.join(
            merged_dir, manifest_data["userDataBackup"]["databaseName"]
        )
        shutil.move(
            os.path.join(self.working_folder, "merged.db"),
            database_file_path,
        )

        current_datetime = datetime.now()
        formatted_date = current_datetime.astimezone(tz.gettz('US/Eastern')).strftime("%Y-%m-%dT%H:%M:%S%z")
        manifest_data["creationDate"] = formatted_date

        name_timestamp = current_datetime.strftime("%Y%m%d-%H%M%S")
        merged_file_name = f"UserdataBackup_{name_timestamp}_Merged.jwlibrary"

        manifest_data["name"] = merged_file_name

        userDataBackup = {
            "lastModifiedDate": formatted_date,
            "hash": self.calculate_sha256(database_file_path),
            "databaseName": manifest_data["userDataBackup"]["databaseName"],
            "schemaVersion": manifest_data["userDataBackup"]["schemaVersion"],
            "deviceName": "SuperMergerPro",
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

        os.rename(
            os.path.join(".", self.jwl_output_folder, merged_file_name + ".zip"),
            os.path.join(".", self.jwl_output_folder, merged_file_name),
        )

        print("Created JWL file! Full path:", os.path.join(".", merged_file_name))

    def cleanTempFiles(self):
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

        file_path_a = filedialog.askopenfilename(
            filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")],
            title="Select your first backup file",
        )
        if not file_path_a:
            exit()
        print("First file selected:", file_path_a)

        file_path_b = filedialog.askopenfilename(
            filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")],
            title="Select your second backup file",
        )
        if not file_path_b:
            exit()

        print("Second file selected:", file_path_b)

        unzip_path_a = self.unzipFile(file_path_a)
        unzip_path_b = self.unzipFile(file_path_b)

        db_path_a = self.getFirstDBFile(unzip_path_a)
        db_path_b = self.getFirstDBFile(unzip_path_b)

        shutil.copy2(db_path_a, os.path.join(self.working_folder, "merged.db"))

        print("Databases extracted:", db_path_a, db_path_b)

        return (db_path_a, db_path_b)

    def calculate_sha256(self, file_path):
        hash_sha256 = hashlib.sha256()
        with open(file_path, "rb") as file:
            for chunk in iter(lambda: file.read(4096), b""):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()


if __name__ == "__main__":
    processor = DatabaseProcessor()
    processor.process_databases(*processor.getJwlFiles())
    processor.createJwlFile()
    processor.cleanTempFiles()
