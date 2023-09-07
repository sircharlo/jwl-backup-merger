#!/usr/bin/python

from datetime import datetime
import glob
import hashlib
import json
import os
import re
import shutil
import sqlite3
import time
import tkinter as tk
import numpy as np
from tqdm import tqdm
from tkinter import filedialog
from zipfile import ZipFile

import pandas as pd


class DatabaseProcessor:
    def __init__(self):
        self.all_id_fields = []
        self.comparison_ignore_fields = ["LastModified", "Created"]
        # self.tables = {}

    def get_primary_keys(self, source_cursor):
        self.primary_keys = {}
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
        self.fk_constraints = {}
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
        self.db = {}
        self.db["a"] = sqlite3.connect(file_a)
        self.db["b"] = sqlite3.connect(file_b)

        for dataframe_letter in ["a", "b"]:
            for table in self.get_tables(self.db[dataframe_letter]):
                self.load_table_into_df(
                    self.db[dataframe_letter], table, dataframe_letter
                )

        # Reorder tables to facilitate processing later
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

            if "Hash" in concatenated_entries.columns:
                subset_columns = ["Hash"]
            elif "Guid" in concatenated_entries.columns:
                subset_columns = ["Guid"]
            elif "ThumbnailFilePath" in concatenated_entries.columns:
                subset_columns = concatenated_entries.columns.difference(
                    ["ThumbnailFilePath"]
                )
            else:
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

            # print("Total common_entries in table", table, ":", common_entries.shape[0])

            # total_conflicting_entries = sum(
            #     len(df)
            #     for inner_dict in conflicting_entries_by_dataset.values()
            #     for df in inner_dict.values()
            # )

            # print("Total conflicting_entries", total_conflicting_entries)

            # if total_conflicting_entries == 0:
            #     continue
            # else:
            # for dataframe_letter in conflicting_entries_by_dataset:
            # print("Conflicting entries in dataset", dataframe_letter)
            # print(conflicting_entries_by_dataset[dataframe_letter][table])

        # print("START MERGING")
        # print(conflicting_entries_by_dataset)
        # print()
        for dataframe_letter in conflicting_entries_by_dataset:
            for table in tqdm(
                conflicting_entries_by_dataset[dataframe_letter],
                desc="Merging tables from " + dataframe_letter,
            ):
                # print(
                #     conflicting_entries_by_dataset[dataframe_letter][table].shape[0],
                #     "changes in dataset '",
                #     dataframe_letter,
                #     "' in table",
                #     table,
                # )
                # print(conflicting_entries_by_dataset[dataframe_letter][table])
                # print(
                #     "Number of PKs in table ", table, ":", len(self.primary_keys[table])
                # )
                highest_pks = self.get_highest_pks_from_merged_table(table)
                # print("Highest PKs in table", table, ":", highest_pks)
                for primary_key in self.primary_keys[table]:
                    # print(primary_key)
                    dict_of_new_values = {}
                    # print(
                    #     "Highest PK for",
                    #     primary_key,
                    #     " in table",
                    #     table,
                    #     ":",
                    #     highest_pks[primary_key],
                    # )
                    if highest_pks[primary_key] is not None:
                        for index, value in enumerate(
                            conflicting_entries_by_dataset[dataframe_letter][table][
                                primary_key
                            ],
                            start=highest_pks[primary_key] + 1,
                        ):
                            if str(value).replace(".", "").isnumeric():
                                dict_of_new_values[value] = index

                    # print(dict_of_new_values)

                    if len(dict_of_new_values) == 0:
                        continue

                    # print()
                    # print("Temp table before")
                    # print(conflicting_entries_by_dataset[dataframe_letter][table])
                    # Update primary key
                    conflicting_entries_by_dataset[dataframe_letter][table][
                        primary_key
                    ] = conflicting_entries_by_dataset[dataframe_letter][table][
                        primary_key
                    ].map(
                        dict_of_new_values
                    )

                    # print("Temp table after")
                    # print(conflicting_entries_by_dataset[dataframe_letter][table])
                    # Update foreign keys
                    if table in self.fk_constraints:
                        for rel_table, fk in self.fk_constraints[table][primary_key]:
                            if (
                                rel_table
                                in conflicting_entries_by_dataset[dataframe_letter]
                            ):
                                # print(
                                #     "Related table",
                                #     rel_table,
                                #     "before (foreign key:",
                                #     fk,
                                #     ", linked to primary key:",
                                #     primary_key,
                                #     ")",
                                # )
                                # print(
                                #     conflicting_entries_by_dataset[dataframe_letter][
                                #         rel_table
                                #     ][
                                #         conflicting_entries_by_dataset[
                                #             dataframe_letter
                                #         ][rel_table][fk]
                                #         != ""
                                #     ]
                                # )
                                conflicting_entries_by_dataset[dataframe_letter][
                                    rel_table
                                ][fk] = (
                                    conflicting_entries_by_dataset[dataframe_letter][
                                        rel_table
                                    ][fk]
                                    .map(dict_of_new_values)
                                    .fillna(
                                        conflicting_entries_by_dataset[
                                            dataframe_letter
                                        ][rel_table][fk]
                                    )
                                )

                                # print(
                                #     "Related table",
                                #     rel_table,
                                #     "after:",
                                # )
                                # print(
                                #     conflicting_entries_by_dataset[dataframe_letter][
                                #         rel_table
                                #     ][
                                #         conflicting_entries_by_dataset[
                                #             dataframe_letter
                                #         ][rel_table][fk]
                                #         != ""
                                #     ]
                                # )

                # print("Merging into merged table", table)
                self.dataframes["merged"][table] = pd.concat(
                    [
                        self.dataframes["merged"][table],
                        conflicting_entries_by_dataset[dataframe_letter][table],
                    ],
                    ignore_index=True,
                )
                # print(self.dataframes["merged"][table])

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
            # dest_cursor.execute(index_sql)
            indices.append(index_sql)
        for trigger_info in triggers_fetcher:
            trigger_name, table_name, trigger_sql = trigger_info
            # dest_cursor.execute(trigger_sql)
            triggers.append(trigger_sql)
        indices = [x for x in list(set(indices)) if x]
        triggers = [x for x in list(set(triggers)) if x]

        self.files_to_include_in_archive = []

        source_cursor.execute("SELECT FilePath FROM IndependentMedia;")
        self.files_to_include_in_archive.extend([file[0] for file in source_cursor.fetchall()])
        source_cursor.execute("SELECT ThumbnailFilePath FROM PlaylistItem;")
        self.files_to_include_in_archive.extend([file[0] for file in source_cursor.fetchall()])
        self.files_to_include_in_archive = list(set(self.files_to_include_in_archive))
        
        self.save_merged_tables2(indices, triggers)

        for dataframe in self.db.values():
            dataframe.close()

    def get_highest_pks_from_merged_table(self, table_name):
        if table_name not in self.primary_keys:
            return None
        highest_pks = None
        for key in self.primary_keys[table_name]:
            highest_pk = None
            # for dataframe_letter in ["a"]:
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
        # if "dataframes_" + destination_letter not in self:
        if not hasattr(self, "dataframes"):
            self.dataframes = {}
            # " + destination_letter] = {}
        if not destination_letter in self.dataframes:
            self.dataframes[destination_letter] = {}
        self.dataframes[destination_letter][table_name] = pd.read_sql_query(
            f"SELECT * FROM {table_name}", db
        )
        self.dataframes[destination_letter][table_name].fillna("", inplace=True)

    def save_merged_tables2(self, indices, triggers):
        output_folder = os.path.join(".", "working")
        os.makedirs(output_folder, exist_ok=True)

        conn_merged = sqlite3.connect(os.path.join(output_folder, "merged.db"))
        dest_cursor = conn_merged.cursor()

        # Get a list of trigger names in the database
        dest_cursor.execute("SELECT name FROM sqlite_master WHERE type='trigger';")
        trigger_names = dest_cursor.fetchall()

        # Loop through each trigger and drop it
        for trigger_name in trigger_names:
            trigger_name = trigger_name[0]
            dest_cursor.execute(f"DROP TRIGGER IF EXISTS {trigger_name};")
        conn_merged.commit()

        # Get a list of index names in the database
        dest_cursor.execute("SELECT name FROM sqlite_master WHERE type='index';")
        index_names = dest_cursor.fetchall()

        # Loop through each index and drop it
        for index_name in index_names:
            index_name = index_name[0]
            if not index_name.startswith("sqlite_"):
                dest_cursor.execute(f"DROP INDEX IF EXISTS {index_name};")
        conn_merged.commit()

        # Loop through each table and delete all data
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
        errors = []
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
                    except Exception as e:
                        # print(insert_sql, row)
                        # # print type of everything in rows_to_insert
                        # for elem in row:
                        #     print(elem, ":", type(elem))
                        # print(rows_to_insert[index])
                        # print(e)
                        errors.append((table_name, insert_sql, rows_to_insert[index], e))
            conn_merged.commit()
        print()

        if len(errors) > 0:
            print("Errors encoutered:")
            for error in errors:
                print(error)
            print()

        dest_cursor.execute("VACUUM")
        conn_merged.commit()

        conn_merged.close()
    
    def createJwlFile(self):
        print("Creating JWL file...")
        working_dir = os.path.join(".", "working")
        merged_dir = os.path.join(working_dir, "merged")
        manifest_file_path = os.path.join(merged_dir, "manifest.json")
        all_unzip_folder_names = list(
            directory
            for directory in os.listdir(working_dir)
            if directory != "merged" and os.path.isdir(os.path.join(working_dir, directory))
        )
        first_jwl_unzip_folder_name = all_unzip_folder_names[0]
        first_jwl_unzip_folder_path = os.path.join(working_dir, first_jwl_unzip_folder_name)

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
            full_path = os.path.join(working_dir, folder)
            for filename in tqdm(os.listdir(full_path), desc=f"Copying files from {folder}"):
                file_path = os.path.join(full_path, filename)
                # Find files referenced in DB and include them in resulting archive...
                if os.path.isfile(file_path) and filename in self.files_to_include_in_archive:
                    # Copy files to the destination directory
                    shutil.copy2(file_path, merged_dir)

        # # Use glob to find files with no extensions in all subdirectories, these are probably thumbnails...
        # files_without_extension = glob.glob(
        #     os.path.join(working_dir, "**/*."), recursive=True
        # )
        # # Copy the files to the destination directory
        # for file_path in tqdm(files_without_extension, desc="Copying thumbnail files"):
        #     shutil.copy2(file_path, merged_dir)
            # TODO: only copy thumbnail files referenced in the db, drop the rest

        with open(manifest_file_path, "r") as file:
            manifest_data = json.load(file)

        database_file_path = os.path.join(
            merged_dir, manifest_data["userDataBackup"]["databaseName"]
        )
        shutil.move(
            os.path.join(working_dir, "merged.db"),
            database_file_path,
        )

        # Update the 'creationDate' key with the current date and time
        current_datetime = datetime.now()
        formatted_date = current_datetime.strftime("%Y-%m-%dT%H:%M:%S%z")
        manifest_data["creationDate"] = formatted_date

        name_timestamp = current_datetime.strftime("%Y%m%d-%H%M%S")
        merged_file_name = f"UserdataBackup_{name_timestamp}_Merged.jwlibrary"

        # Generate the 'name' key value based on the current time
        manifest_data["name"] = merged_file_name

        # Update the 'userDataBackup' sub-object
        userDataBackup = {
            "lastModifiedDate": formatted_date,
            "hash": calculate_md5(database_file_path),
            "databaseName": manifest_data["userDataBackup"]["databaseName"],
            "schemaVersion": manifest_data["userDataBackup"]["schemaVersion"],
            "deviceName": "SuperMergerPro",
        }
        manifest_data["userDataBackup"] = userDataBackup

        # Write the modified JSON back to the file
        with open(manifest_file_path, "w") as file:
            json.dump(manifest_data, file, indent=2)

        # zip merged dir into a .jwlibrary file
        shutil.make_archive(os.path.join(".", merged_file_name), "zip", merged_dir)

        os.rename(
            os.path.join(".", merged_file_name + ".zip"),
            os.path.join(".", merged_file_name),
        )

        print("Created JWL file! Full path:", os.path.join(".", merged_file_name))


def cleanTempFiles():
    workingDir = os.path.join(".", "working")
    if os.path.exists(workingDir):
        shutil.rmtree(workingDir)
    print("Cleaned up temporary files!")


def unzipFile(file_path):
    basename = os.path.basename(file_path)
    basename = os.path.splitext(basename)[0]
    unzipPath = os.path.join(".", "working", basename)
    with ZipFile(file_path, "r") as zip:
        zip.extractall(path=unzipPath)
    # return dir list of unzipped files
    return unzipPath


def getFirstDBFile(unzipPath):
    db_files = glob.glob(unzipPath + "/*.db")
    if db_files:
        return db_files[0]
    else:
        return None


def getJwlFiles():
    root = tk.Tk()
    root.withdraw()

    file_path_a = filedialog.askopenfilename(
        filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")]
    )
    if not file_path_a:
        exit()
    print("File selected:", file_path_a)

    file_path_b = filedialog.askopenfilename(
        filetypes=[(".JWLIBRARY files", "*.JWLIBRARY")]
    )
    if not file_path_b:
        exit()

    print("File selected:", file_path_b)

    unzip_path_a = unzipFile(file_path_a)
    unzip_path_b = unzipFile(file_path_b)

    db_path_a = getFirstDBFile(unzip_path_a)
    db_path_b = getFirstDBFile(unzip_path_b)

    shutil.copy2(db_path_a, os.path.join(".", "working", "merged.db"))

    print("Databases extracted:", db_path_a, db_path_b)

    return (db_path_a, db_path_b)


def calculate_md5(file_path):
    hash_md5 = hashlib.md5()
    with open(file_path, "rb") as file:
        for chunk in iter(lambda: file.read(4096), b""):
            hash_md5.update(chunk)
    return hash_md5.hexdigest()


if __name__ == "__main__":
    processor = DatabaseProcessor()
    processor.process_databases(*getJwlFiles())
    processor.createJwlFile()
    # cleanTempFiles()
