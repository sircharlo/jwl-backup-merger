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

import difflib
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
        self.fk_map = {}  # {from_table_lower: {from_col_lower: (to_table, to_col)}}
        self.table_name_map = {}  # {table_name_lower: table_name_original}
        self.pk_map = {}  # {table_name: {old_pk: new_pk}}
        self.note_bases = {}  # {guid: {'title': title, 'content': content, 'last_modified': ts}}
        self.files_to_include_in_archive = []
        self.start_time = 0

        self.working_folder = path.join(".", "working")
        self.jwl_output_folder = path.join(".", "merged")
        self.merged_db_path = path.join(self.working_folder, "merged.db")

        self.output = {"info": [], "errors": []}

    def get_table_info(self, db):
        """ Get table info from database

        Args:
            db (sqlite3.Connection): Database connection

        Returns:
            None
        """
        cursor = db.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
        tables = [table[0] for table in cursor.fetchall()]

        self.fk_map = {}
        for table_name in tables:
            self.table_name_map[table_name.lower()] = table_name
            # Get PKs
            cursor.execute(f"PRAGMA table_info('{table_name}');")
            columns = cursor.fetchall()
            pks = [col[1] for col in columns if col[5] > 0]
            self.primary_keys[table_name] = pks

            # Get FKs
            cursor.execute(f"PRAGMA foreign_key_list('{table_name}');")
            fks = cursor.fetchall()
            for fk in fks:
                # fk format: (id, seq, table, from, to, on_update, on_delete, match)
                to_table = fk[2]
                from_col = fk[3]
                to_col = fk[4]

                table_lower = table_name.lower()
                if table_lower not in self.fk_map:
                    self.fk_map[table_lower] = {}
                self.fk_map[table_lower][from_col.lower()] = (to_table, to_col)

    def process_databases(self, database_files):
        """ Process databases

        Args:
            database_files (list): List of database files to process

        Returns:
            None
        """
        self.start_time = time()
        self.note_bases = {}
        
        # Initialize merged_db from first file
        first_db = database_files[0]
        copy2(first_db, self.merged_db_path)
        merged_conn = sqlite3.connect(self.merged_db_path)
        merged_cursor = merged_conn.cursor()
        self.get_table_info(merged_conn)
        
        # Empty all tables in merged_db
        for table in self.primary_keys.keys():
            if table not in ["grdb_migrations", "LastModified"]:
                merged_cursor.execute(f"DELETE FROM {table};")
        merged_conn.commit()

        # Table processing order (dependencies first)
        table_order = [
            "Location",
            "IndependentMedia",
            "Tag",
            "PlaylistItemAccuracy",
            "PlaylistItem",
            "UserMark",
            "BlockRange",
            "Note",
            "Bookmark",
            "TagMap",
            "InputField",
            "PlaylistItemIndependentMediaMap",
            "PlaylistItemLocationMap",
            "PlaylistItemMarker",
            "PlaylistItemMarkerBibleVerseMap",
            "PlaylistItemMarkerParagraphMap"
        ]

        # Deduplication Identity Keys
        identity_keys = {
            "Location": ["BookNumber", "ChapterNumber", "DocumentId", "Track", "IssueTagNumber", "KeySymbol", "MepsLanguage", "Type", "Title"],
            "Tag": ["Type", "Name"],
            "IndependentMedia": ["Hash"],
            "PlaylistItemAccuracy": ["Description"],
            "PlaylistItem": ["Label", "ThumbnailFilePath"],
            "UserMark": ["UserMarkGuid"],
            "Note": ["Guid"],
            "Bookmark": ["PublicationLocationId", "Slot"],
            "BlockRange": ["BlockType", "Identifier", "UserMarkId"],
            "InputField": ["LocationId", "TextTag"],
            "TagMap": ["TagId", "PlaylistItemId", "LocationId", "NoteId"],
            "PlaylistItemIndependentMediaMap": ["PlaylistItemId", "IndependentMediaId"],
            "PlaylistItemLocationMap": ["PlaylistItemId", "LocationId"],
            "PlaylistItemMarkerBibleVerseMap": ["PlaylistItemMarkerId", "VerseId"],
            "PlaylistItemMarkerParagraphMap": ["PlaylistItemMarkerId", "MepsDocumentId", "ParagraphIndex", "MarkerIndexWithinParagraph"]
        }

        for file_path in tqdm(database_files, desc="Merging databases"):
            source_conn = sqlite3.connect(file_path)
            source_cursor = source_conn.cursor()
            skipped_pks = {} # {table: set(old_pk)}
            self.pk_map = {} # Clear for each file to avoid old PK collisions!

            for table_target in table_order:
                table = self.table_name_map.get(table_target.lower())
                if not table or table not in self.primary_keys:
                    continue

                # Get data from source
                try:
                    source_cursor.execute(f"SELECT * FROM [{table}]")
                except sqlite3.Error:
                    continue  # Table might not exist in this database

                cols_source = [
                    description[0] for description in source_cursor.description
                ]
                rows = source_cursor.fetchall()

                if table not in self.pk_map:
                    self.pk_map[table] = {}
                if table not in skipped_pks:
                    skipped_pks[table] = set()

                # Get target column names for consistency
                merged_cursor.execute(f"PRAGMA table_info([{table}])")
                cols_target = [col[1] for col in merged_cursor.fetchall()]

                # Pre-scan this table for conflicts
                table_conflicts = 0
                if table_target in ["UserMark", "Bookmark", "InputField", "Note"]:
                    for row in rows:
                        # Temporary dict to check identity
                        temp_row = dict(zip(cols_source, row))
                        temp_dict = {}
                        for ct in cols_target:
                            cs = next((k for k in temp_row if k.lower() == ct.lower()), None)
                            temp_dict[ct] = temp_row[cs] if cs else None
                        
                        # Remap FKs for identity check
                        table_lower = table.lower()
                        if table_lower in self.fk_map:
                            for c_name, val in temp_dict.items():
                                c_lower = c_name.lower()
                                if c_lower in self.fk_map[table_lower]:
                                    t_table, t_col = self.fk_map[table_lower][c_lower]
                                    t_canonical = self.table_name_map.get(t_table.lower(), t_table)
                                    if val in self.pk_map.get(t_canonical, {}):
                                        temp_dict[c_name] = self.pk_map[t_canonical][val]
                        
                        # Check identity
                        id_cols = identity_keys.get(table_target)
                        if id_cols:
                            query = f"SELECT {self.primary_keys[table][0]} FROM [{table}] WHERE " + " AND ".join([f"[{k}] IS ?" for k in id_cols])
                            merged_cursor.execute(query, [temp_dict.get(k) for k in id_cols])
                            res = merged_cursor.fetchone()
                            if res:
                                # Conflict check
                                merged_cursor.execute(f"SELECT * FROM [{table}] WHERE {self.primary_keys[table][0]} = ?", (res[0],))
                                curr = dict(zip(cols_target, merged_cursor.fetchone()))
                                is_diff = False
                                for c in temp_dict:
                                    if c in self.primary_keys[table]: continue
                                    if table_target == "Note" and c in ["Title", "Content"]:
                                        if (temp_dict[c] or "") != (curr.get(c) or ""): is_diff = True; break
                                    elif temp_dict[c] != curr.get(c):
                                        is_diff = True; break
                                
                                if is_diff:
                                    table_conflicts += 1
                
                table_conflict_index = 0

                for row in rows:
                    # Map source row to target schema
                    row_dict_source = dict(zip(cols_source, row))
                    row_dict = {}
                    source_cols_lower = {k.lower(): k for k in row_dict_source.keys()}

                    for col_target in cols_target:
                        col_source = source_cols_lower.get(col_target.lower())
                        row_dict[col_target] = (
                            row_dict_source[col_source] if col_source else None
                        )

                    old_pk = (
                        row_dict.get(self.primary_keys[table][0])
                        if self.primary_keys[table]
                        else None
                    )
                    
                    if old_pk is not None and old_pk in skipped_pks.get(table, set()):
                        continue

                    # Remap Foreign Keys
                    table_lower = table.lower()
                    if table_lower in self.fk_map:
                        for col_name, val in row_dict.items():
                            col_lower = col_name.lower()
                            if col_lower in self.fk_map[table_lower]:
                                to_table, to_col = self.fk_map[table_lower][col_lower]
                                to_table_canonical = self.table_name_map.get(
                                    to_table.lower(), to_table
                                )
                                if val in self.pk_map.get(to_table_canonical, {}):
                                    row_dict[col_name] = self.pk_map[to_table_canonical][
                                        val
                                    ]

                    # Check for duplicates in merged_db
                    identity_cols = identity_keys.get(table_target)
                    existing_new_pk = None
                    if identity_cols:
                        conditions = []
                        vals = []
                        for c in identity_cols:
                            if row_dict.get(c) is None:
                                conditions.append(f"[{c}] IS ?")
                            elif table_target == "Tag" and c == "Name":
                                conditions.append(f"[{c}] = ? COLLATE NOCASE")
                            else:
                                conditions.append(f"[{c}] = ?")
                            vals.append(row_dict.get(c))

                        where_clause = " AND ".join(conditions)
                        query = f"SELECT {self.primary_keys[table][0]} FROM [{table}] WHERE {where_clause}"
                        merged_cursor.execute(query, vals)
                        res = merged_cursor.fetchone()
                        if res:
                            existing_new_pk = res[0]

                    if existing_new_pk is not None:
                        # Handle conflicts for specific tables
                        if table_target == "UserMark":
                            # Bundle UserMark with its BlockRanges
                            merged_cursor.execute(f"SELECT ColorIndex, LocationId FROM [{table}] WHERE UserMarkId = ?", (existing_new_pk,))
                            curr_color, loc_id = merged_cursor.fetchone()
                            
                            # Get current BlockRanges
                            merged_cursor.execute("SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?", (existing_new_pk,))
                            curr_ranges = sorted(merged_cursor.fetchall())
                            
                            # Get incoming BlockRanges
                            source_cursor.execute("SELECT BlockRangeId, BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?", (old_pk,))
                            inc_br_rows = source_cursor.fetchall()
                            inc_ranges = sorted([r[1:] for r in inc_br_rows])
                            
                            inc_color = row_dict.get("ColorIndex")
                            color_names = {1: "yellow", 2: "green", 3: "blue", 4: "red", 5: "orange", 6: "purple"}
                            
                            if inc_color != curr_color or inc_ranges != curr_ranges:
                                table_conflict_index += 1
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(f"\nConflict {table_conflict_index}/{table_conflicts} in Highlight at {loc_info}:")
                                
                                if inc_color != curr_color:
                                    print(f"  Color: current='{curr_color} ({color_names.get(curr_color)})' vs incoming='{inc_color} ({color_names.get(inc_color)})'")
                                if inc_ranges != curr_ranges:
                                    print(f"  Ranges (BlockType, Id, Start, End):")
                                    print(f"    current : {curr_ranges}")
                                    print(f"    incoming: {inc_ranges}")
                                
                                choice = ""
                                while choice not in ["c", "i"]:
                                    choice = input("Keep (c)urrent or (i)ncoming? ").lower()
                                
                                if choice == "i":
                                    # Update UserMark color
                                    merged_cursor.execute(f"UPDATE [{table}] SET ColorIndex = ? WHERE UserMarkId = ?", (inc_color, existing_new_pk))
                                    # Replace BlockRanges
                                    merged_cursor.execute("DELETE FROM BlockRange WHERE UserMarkId = ?", (existing_new_pk,))
                                    for br in inc_br_rows:
                                        # Insert new BlockRange linked to existing_new_pk
                                        br_dict = dict(zip(["BlockRangeId", "BlockType", "Identifier", "StartToken", "EndToken"], br))
                                        br_dict["UserMarkId"] = existing_new_pk
                                        del br_dict["BlockRangeId"]
                                        cols = ", ".join([f"[{k}]" for k in br_dict.keys()])
                                        places = ", ".join(["?"] * len(br_dict))
                                        merged_cursor.execute(f"INSERT INTO BlockRange ({cols}) VALUES ({places})", list(br_dict.values()))
                                        # We don't need to update pk_map for BR here because we mark them as skipped
                            
                            # Mark all incoming BlockRanges as skipped
                            if "BlockRange" not in skipped_pks: skipped_pks["BlockRange"] = set()
                            for br in inc_br_rows:
                                skipped_pks["BlockRange"].add(br[0])

                        elif table_target in ["Bookmark", "InputField"]:
                            # Get existing data
                            merged_cursor.execute(f"SELECT * FROM [{table}] WHERE {self.primary_keys[table][0]} = ?", (existing_new_pk,))
                            current_row = dict(zip(cols_target, merged_cursor.fetchone()))
                            
                            # Compare relevant fields
                            diffs = {}
                            for col in row_dict:
                                if col in self.primary_keys[table]: continue
                                if row_dict[col] != current_row.get(col):
                                    diffs[col] = (current_row.get(col), row_dict[col])
                            
                            if diffs:
                                table_conflict_index += 1
                                # Fetch context for the user
                                loc_id = current_row.get("LocationId")
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(f"\nConflict {table_conflict_index}/{table_conflicts} in {table_target} at {loc_info}:")
                                for col, (old_val, new_val) in diffs.items():
                                    print(f"  {col}: current='{old_val}' vs incoming='{new_val}'")
                                
                                choice = ""
                                options = ["c", "i"]
                                if table_target == "InputField":
                                    options.append("m")
                                    merged_val = self.merge_text(None, current_row.get("Value"), row_dict.get("Value"))
                                    print(f"  Merged value: '{merged_val}'")
                                
                                prompt = f"Keep (c)urrent, (i)ncoming?"
                                if "m" in options: prompt = f"Keep (c)urrent, (i)ncoming, or (m)erged?"
                                
                                while choice not in options:
                                    choice = input(f"{prompt} ").lower()
                                
                                if choice == "i":
                                    update_cols = ", ".join([f"[{k}] = ?" for k in diffs.keys()])
                                    merged_cursor.execute(f"UPDATE [{table}] SET {update_cols} WHERE {self.primary_keys[table][0]} = ?", 
                                                          list(row_dict[k] for k in diffs.keys()) + [existing_new_pk])
                                elif choice == "m" and table_target == "InputField":
                                    merged_cursor.execute(f"UPDATE [{table}] SET Value = ? WHERE {self.primary_keys[table][0]} = ?", 
                                                          (merged_val, existing_new_pk))

                        elif table_target == "Note":
                            # Perform interactive 3-way merge for notes
                            merged_cursor.execute(f"SELECT Title, Content, LastModified, LocationId FROM [{table}] WHERE {self.primary_keys[table][0]} = ?", (existing_new_pk,))
                            current_merged = merged_cursor.fetchone()
                            curr_title, curr_content, m_ts, loc_id = current_merged
                            
                            guid = row_dict.get("Guid")
                            base = self.note_bases.get(guid, {"title": curr_title, "content": curr_content})
                            
                            inc_title = row_dict.get("Title") or ""
                            inc_content = row_dict.get("Content") or ""
                            curr_title = curr_title or ""
                            curr_content = curr_content or ""
                            
                            merged_title = self.merge_text(base.get("title"), curr_title, inc_title)
                            merged_content = self.merge_text(base.get("content"), curr_content, inc_content)
                            
                            if inc_title != curr_title or inc_content != curr_content:
                                table_conflict_index += 1
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(f"\nConflict {table_conflict_index}/{table_conflicts} in Note at {loc_info} (GUID: {guid}):")
                                
                                if inc_title != curr_title:
                                    print("\n--- Title Diff (current vs incoming) ---")
                                    self.print_diff(curr_title, inc_title)

                                    print("\n--- Auto-merged title ---")
                                    print(merged_title)
                                
                                if inc_content != curr_content:
                                    print("\n--- Content Diff (current vs incoming) ---")
                                    self.print_diff(curr_content, inc_content)

                                    print("\n--- Auto-merged content ---")
                                    print(merged_content)
                                
                                print("\nOptions:")
                                print(f"  [c]urrent")
                                print(f"  [i]ncoming")
                                print(f"  [m]erged")
                                
                                choice = ""
                                while choice not in ["c", "i", "m"]:
                                    choice = input("\nKeep (c)urrent, (i)ncoming, or (m)erged? ").lower()
                                
                                final_title, final_content = curr_title, curr_content
                                if choice == "i":
                                    final_title, final_content = inc_title, inc_content
                                elif choice == "m":
                                    final_title, final_content = merged_title, merged_content
                                
                                # Determine latest LastModified
                                s_ts = row_dict.get("LastModified")
                                latest_ts = s_ts if (not m_ts or (s_ts and s_ts > m_ts)) else m_ts
                                
                                merged_cursor.execute(f"UPDATE [{table}] SET Title = ?, Content = ?, LastModified = ? WHERE {self.primary_keys[table][0]} = ?", 
                                                      (final_title, final_content, latest_ts, existing_new_pk))

                        if old_pk is not None:
                            self.pk_map[table][old_pk] = existing_new_pk
                    else:
                        # Insert new row
                        insert_dict = row_dict.copy()
                        if table_target == "Note":
                            self.note_bases[row_dict.get("Guid")] = {"title": row_dict.get("Title"), "content": row_dict.get("Content")}
                        
                        if len(self.primary_keys[table]) == 1:
                            pk_name = self.primary_keys[table][0]
                            if isinstance(insert_dict.get(pk_name), int):
                                del insert_dict[pk_name]

                        columns = ", ".join([f"[{k}]" for k in insert_dict.keys()])
                        placeholders = ", ".join(["?"] * len(insert_dict))
                        insert_query = (
                            f"INSERT INTO [{table}] ({columns}) VALUES ({placeholders})"
                        )

                        try:
                            merged_cursor.execute(
                                insert_query, list(insert_dict.values())
                            )
                            new_pk = merged_cursor.lastrowid
                            if old_pk is not None:
                                self.pk_map[table][old_pk] = new_pk
                        except sqlite3.IntegrityError as e:
                            # Special handling for TagMap position conflicts
                            if table_target == "TagMap" and "TagMap.TagId, TagMap.Position" in str(e):
                                tag_id = insert_dict.get("TagId")
                                position = insert_dict.get("Position")
                                # Shift existing items forward manually to avoid "ORDER BY" syntax requirements in UPDATE
                                merged_cursor.execute(f"SELECT TagMapId, Position FROM [{table}] WHERE TagId = ? AND Position >= ? ORDER BY Position DESC", (tag_id, position))
                                for tid, pos in merged_cursor.fetchall():
                                    merged_cursor.execute(f"UPDATE [{table}] SET Position = ? WHERE TagMapId = ?", (pos + 1, tid))
                                # Retry insertion
                                merged_cursor.execute(insert_query, list(insert_dict.values()))
                                new_pk = merged_cursor.lastrowid
                                if old_pk is not None:
                                    self.pk_map[table][old_pk] = new_pk
                            else:
                                self.output["errors"].append((table, insert_query, e))
                        except sqlite3.Error as e:
                            self.output["errors"].append((table, insert_query, e))

            source_conn.close()
            merged_conn.commit()

        # Update LastModified
        merged_cursor.execute("UPDATE LastModified SET LastModified = strftime('%Y-%m-%dT%H:%M:%SZ', 'now');")
        merged_conn.commit()
        
        # Collect files for archive
        try:
            merged_cursor.execute("SELECT FilePath FROM IndependentMedia WHERE FilePath IS NOT NULL")
            self.files_to_include_in_archive.extend([r[0] for r in merged_cursor.fetchall()])
        except: pass
        try:
            merged_cursor.execute("SELECT ThumbnailFilePath FROM PlaylistItem WHERE ThumbnailFilePath IS NOT NULL")
            self.files_to_include_in_archive.extend([r[0] for r in merged_cursor.fetchall()])
        except: pass
        self.files_to_include_in_archive = list(set(self.files_to_include_in_archive))

        merged_conn.close()

        merged_conn.close()

    def createJwlFile(self):
        """ Create JWL file from the merged database in the working folder

        Returns:
            None
        """
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

    def print_diff(self, a, b):
        """ Print a colored diff between two strings. """
        a_lines = (a or "").splitlines()
        b_lines = (b or "").splitlines()
        
        # Color codes
        RED = "\033[91m"
        GREEN = "\033[92m"
        RESET = "\033[0m"
        
        diff = difflib.ndiff(a_lines, b_lines)
        for line in diff:
            if line.startswith("+ "):
                print(f"{GREEN}{line}{RESET}")
            elif line.startswith("- "):
                print(f"{RED}{line}{RESET}")
            elif line.startswith("? "):
                continue
            else:
                print(line)

    def get_location_info(self, cursor, location_id):
        """ Get formatted location info for display """
        if not location_id: return "Unknown Location"
        cursor.execute("SELECT BookNumber, ChapterNumber, DocumentId, Title, KeySymbol, IssueTagNumber, MepsLanguage FROM Location WHERE LocationId = ?", (location_id,))
        row = cursor.fetchone()
        if not row: return f"Location ID {location_id}"
        book, chapter, doc, title, keysym, issue, lang = row
        info = []
        if title: info.append(title)
        if keysym: info.append(f"{keysym}")
        if issue: info.append(f"{issue}")
        if lang: info.append(f"Lang {lang}")
        if book: info.append(f"Book {book}")
        if chapter: info.append(f"Ch. {chapter}")
        if not keysym and doc: info.append(f"Doc {doc}")
        return " - ".join(info) if info else f"Location {location_id}"

    def merge_text(self, base, a, b):
        """ Perform a 3-way merge on two strings using a common base. """
        if a == b: return a
        if not a: return b
        if not b: return a
        if not base:
            if a in b: return b
            if b in a: return a
            sep = "\n" if "\n" in a or "\n" in b else " "
            return a + sep + b

        if a == base: return b
        if b == base: return a

        # Identify changes in A and B relative to base
        def get_change(orig, other):
            i = 0
            while i < len(orig) and i < len(other) and orig[i] == other[i]:
                i += 1
            j = 0
            while j < (len(orig)-i) and j < (len(other)-i) and orig[-(j+1)] == other[-(j+1)]:
                j += 1
            return i, len(orig)-j, other[i:len(other)-j] if j > 0 else other[i:]

        start_a, end_a, content_a = get_change(base, a)
        start_b, end_b, content_b = get_change(base, b)

        # If changes are non-overlapping, apply both
        if end_a <= start_b:
            return base[:start_a] + content_a + base[end_a:start_b] + content_b + base[end_b:]
        if end_b <= start_a:
            return base[:start_b] + content_b + base[end_b:start_a] + content_a + base[end_a:]

        # Overlapping changes: use current conservative logic or concatenate
        # Find common prefix/suffix of all three
        i = 0
        while i < len(base) and i < len(a) and i < len(b) and base[i] == a[i] == b[i]:
            i += 1
        prefix = base[:i]

        j = 0
        while j < (len(base)-i) and j < (len(a)-i) and j < (len(b)-i) and base[-(j+1)] == a[-(j+1)] == b[-(j+1)]:
            j += 1
        suffix = base[len(base)-j:] if j > 0 else ""

        base_m = base[i:len(base)-j] if j > 0 else base[i:]
        a_m = a[i:len(a)-j] if j > 0 else a[i:]
        b_m = b[i:len(b)-j] if j > 0 else b[i:]

        if a_m == base_m:
            merged_m = b_m
        elif b_m == base_m:
            merged_m = a_m
        else:
            if a_m in b_m: merged_m = b_m
            elif b_m in a_m: merged_m = a_m
            else:
                sep = "\n" if "\n" in a_m or "\n" in b_m else " "
                merged_m = a_m + sep + b_m

        return prefix + merged_m + suffix

    def cleanTempFiles(self, force=False):
        """ Clean up temporary files 

        Args:
            force (bool, optional): Force cleanup. Defaults to False.

        Returns:
            None
        """
        if force or (not self.debug and len(self.output["errors"]) == 0):
            if path.isdir(self.working_folder):
                rmtree(self.working_folder)
            print()
            print("Cleaned up working directory!")

    def unzipFile(self, file_path):
        """ Unzip a file

        Args:
            file_path (str): Path to the file to unzip

        Returns:
            str: Path to the unzipped file
        """
        basename = path.splitext(path.basename(file_path))[0]
        unzipPath = path.join(self.working_folder, basename)
        unpack_archive(file_path, extract_dir=unzipPath, format="zip")
        return unzipPath

    def getFirstDBFile(self, unzipPath):
        """ Get the first database file in the unzipped folder

        Args:
            unzipPath (str): Path to the unzipped folder

        Returns:
            str: Path to the first database file
        """
        db_files = glob(unzipPath + "/*.db")
        if db_files:
            return db_files[0]
        else:
            return None

    def getJwlFiles(self):
        """ Get the list of JW Library backup files to merge

        Returns:
            list: List of JW Library backup database files
        """
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
        """ Calculate the SHA-256 hash of a file 

        Args:
            file_path (str): Path to the file to calculate the hash of

        Returns:
            str: SHA-256 hash of the file
        """
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
