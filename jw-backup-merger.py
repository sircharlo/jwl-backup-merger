#!/usr/bin/python
from argparse import ArgumentParser
from datetime import datetime
from dateutil import tz
from glob import glob
from os import path, makedirs, listdir, rename, remove
from shutil import copy2, make_archive, unpack_archive, rmtree
from time import time
from tqdm import tqdm

import difflib
import sqlite3
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
from html.parser import HTMLParser
import re
import sys
from urllib.parse import urlparse
import questionary

from langs import LANGUAGES


parser = ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
parser.add_argument("--folder", type=str, help="Folder containing JWL files to merge")
parser.add_argument("--file", type=str, help="JWL file to merge", action="append")
parser.add_argument("--test", action="store_true", help="Run automated tests")
args = parser.parse_args()

selectBlockRangeSql = "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?"
selectLocationSql = "SELECT DocumentId, MepsLanguage, KeySymbol, BookNumber, ChapterNumber FROM Location WHERE LocationId = ?"


class PExtractor(HTMLParser):
    def __init__(self, pid=None):
        super().__init__()
        self.pid = str(pid) if pid is not None else None
        self.found = pid is None
        self.in_parNum = False
        self.in_verseNum = False
        self.in_chapterNum = False
        self.text = ""

    def handle_starttag(self, tag, attrs):
        d = dict(attrs)
        if tag == "p" and self.pid is not None:
            if d.get("data-pid") == self.pid:
                self.found = True
        elif self.found:
            classes = d.get("class", "").split()
            if tag == "span" or tag == "sup":
                if "parNum" in classes:
                    self.in_parNum = True
                if "verseNum" in classes:
                    self.in_verseNum = True
                if "chapterNum" in classes:
                    self.in_chapterNum = True

    def handle_endtag(self, tag):
        if tag == "p" and self.pid is not None and self.found:
            self.found = False
        elif tag == "span" or tag == "sup":
            if self.in_parNum:
                self.in_parNum = False
            if self.in_verseNum:
                self.in_verseNum = False
            if self.in_chapterNum:
                self.in_chapterNum = False

    def handle_data(self, data):
        if (
            self.found
            and not self.in_parNum
            and not self.in_verseNum
            and not self.in_chapterNum
        ):
            data = data.replace("·", "")
            if data:
                self.text += data


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
        self.user_agent = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
        self.debug = args.debug
        self.primary_keys = {}
        self.pk_is_integer = {}  # {table_original: bool} — True iff single INTEGER PK (auto-increment)
        self.fk_map = {}  # {table_lower: {col_lower: (ref_table_original, ref_col)}}
        self.table_name_map = {}  # {table_lower: table_original}
        self.note_bases = {}  # {guid: {'title': ..., 'content': ...}}
        self.files_to_include_in_archive = []
        self.start_time = 0

        self.working_folder = path.join(".", "working")
        self.jwl_output_folder = path.join(".", "merged")
        self.merged_db_path = path.join(self.working_folder, "merged.db")

        self.output = {"info": [], "errors": []}
        self.doc_cache = {}
        self.bible_api_cache = {}
        self.conflict_cache = {
            "UserMark": {},
            "Note": {},
            "Bookmark": {},
            "InputField": {},
        }
        self.ignored_keysymbols = []
        self.autoresolve_config = {}
        self.usermark_sources = {}  # {merged_usermark_id: source_path}
        self.text_prefetch_workers = 3
        self.color_preference = [6, 5, 4, 3, 2, 1]

        # Tables processed in parent-before-child dependency order.
        # This is critical: every FK target must appear before the table that references it.
        self.table_order = [
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
            "PlaylistItemMarkerParagraphMap",
        ]

        # Columns whose combination uniquely identifies a real-world row,
        # independent of PK values.  FK columns here are remapped BEFORE lookup.
        self.identity_keys = {
            "Location": [
                "BookNumber",
                "ChapterNumber",
                "DocumentId",
                "Track",
                "IssueTagNumber",
                "KeySymbol",
                "MepsLanguage",
                "Type",
                "Title",
            ],
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
            "PlaylistItemMarkerParagraphMap": [
                "PlaylistItemMarkerId",
                "MepsDocumentId",
                "ParagraphIndex",
                "MarkerIndexWithinParagraph",
            ],
        }

    # ------------------------------------------------------------------
    # Schema introspection
    # ------------------------------------------------------------------

    def get_table_info(self, db):
        """Populate primary_keys, pk_is_integer, fk_map, and table_name_map from a live connection."""
        cursor = db.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
        tables = [t[0] for t in cursor.fetchall()]

        self.fk_map = {}
        self.primary_keys = {}
        self.pk_is_integer = {}
        self.table_name_map = {}

        for table_name in tables:
            self.table_name_map[table_name.lower()] = table_name

            # col: (cid, name, type, notnull, dflt_value, pk_position)
            cursor.execute(f"PRAGMA table_info('{table_name}');")
            columns = cursor.fetchall()

            pk_cols = [(col[1], col[2]) for col in columns if col[5] > 0]
            # Sort by pk position so multi-column PKs are ordered correctly
            pk_cols.sort(
                key=lambda c: next(col[5] for col in columns if col[1] == c[0])
            )

            self.primary_keys[table_name] = [c[0] for c in pk_cols]

            # Single INTEGER PK = SQLite rowid alias = auto-increment on INSERT
            self.pk_is_integer[table_name] = (
                len(pk_cols) == 1 and pk_cols[0][1].upper() == "INTEGER"
            )

            cursor.execute(f"PRAGMA foreign_key_list('{table_name}');")
            for fk in cursor.fetchall():
                to_table, from_col, to_col = fk[2], fk[3], fk[4]
                tl = table_name.lower()
                if tl not in self.fk_map:
                    self.fk_map[tl] = {}
                self.fk_map[tl][from_col.lower()] = (to_table, to_col)

    def _is_autoincrement_table(self, table):
        """True iff this table has a single INTEGER PK (SQLite auto-increment / rowid alias)."""
        return self.pk_is_integer.get(table, False)

    # ------------------------------------------------------------------
    # In-memory identity index
    # ------------------------------------------------------------------

    def _build_identity_index(self, merged_cursor):
        """
        Build a dict-of-dicts from the current merged DB content:

            For auto-increment tables:
                identity_index[table_name][identity_tuple] = pk_int
            For composite PK tables:
                identity_index[table_name][identity_tuple] = True   (existence flag)

        FK columns in identity tuples already hold merged PKs, so remapped source
        rows match correctly against this index.
        """
        index = {}
        for table_name in self.table_order:
            table = self.table_name_map.get(table_name.lower())
            if not table or table not in self.primary_keys:
                continue
            id_cols = self.identity_keys.get(table_name)
            if not id_cols:
                index[table_name] = {}
                continue

            autoincrement = self._is_autoincrement_table(table)

            if autoincrement:
                # Select PK + identity columns; value stored is the PK int
                pk_col = self.primary_keys[table][0]
                select_cols = ", ".join(f"[{c}]" for c in [pk_col] + id_cols)
                try:
                    merged_cursor.execute(f"SELECT {select_cols} FROM [{table}]")
                except sqlite3.Error:
                    index[table_name] = {}
                    continue
                index[table_name] = {}
                for row in merged_cursor.fetchall():
                    index[table_name][row[1:]] = row[0]  # identity_tuple → pk
            else:
                # Composite PK table — only need existence; value is True sentinel
                select_cols = ", ".join(f"[{c}]" for c in id_cols)
                try:
                    merged_cursor.execute(f"SELECT {select_cols} FROM [{table}]")
                except sqlite3.Error:
                    index[table_name] = {}
                    continue
                index[table_name] = {row: True for row in merged_cursor.fetchall()}

        return index

    def _index_lookup(self, table_name, identity_tuple, identity_index):
        """
        Look up an identity tuple in the index.
        Returns (found: bool, pk: int | None).
          - Auto-increment tables: found=True, pk=int
          - Composite PK tables:   found=True, pk=None  (no single PK to remap)
          - Not found:             found=False, pk=None
        Tag.Name comparison is case-insensitive.
        """
        table_index = identity_index.get(table_name, {})

        # Fast path
        val = table_index.get(identity_tuple)
        if val is not None:
            return (True, None if val is True else val)

        # Case-insensitive fallback for Tag.Name
        if table_name == "Tag":
            id_cols = self.identity_keys.get("Tag", [])
            name_pos = id_cols.index("Name") if "Name" in id_cols else None
            if name_pos is not None:
                for stored_key, stored_val in table_index.items():
                    match = all(
                        (sv or "").lower() == (iv or "").lower()
                        if i == name_pos
                        else sv == iv
                        for i, (sv, iv) in enumerate(zip(stored_key, identity_tuple))
                    )
                    if match:
                        return (True, None if stored_val is True else stored_val)

        return (False, None)

    # ------------------------------------------------------------------
    # FK remapping
    # ------------------------------------------------------------------

    def _remap_fks(self, table, row_dict, pk_remap):
        """
        Rewrite every FK column in row_dict using pk_remap.
        Because tables are processed in dependency order, the referenced
        table's pk_remap is always fully populated at this point.
        """
        table_lower = table.lower()
        if table_lower not in self.fk_map:
            return
        for col_name in list(row_dict.keys()):
            col_lower = col_name.lower()
            if col_lower in self.fk_map[table_lower]:
                ref_table_orig, _ = self.fk_map[table_lower][col_lower]
                ref_table = self.table_name_map.get(
                    ref_table_orig.lower(), ref_table_orig
                )
                old_val = row_dict[col_name]
                if old_val is not None and old_val in pk_remap.get(ref_table, {}):
                    row_dict[col_name] = pk_remap[ref_table][old_val]

    # ------------------------------------------------------------------
    # Core merge entry points
    # ------------------------------------------------------------------

    def _initialize_merge(self, database_files):
        """Copy first source DB as the merge target and wipe all data tables."""
        self.start_time = time()
        self.note_bases = {}

        copy2(database_files[0], self.merged_db_path)
        merged_conn = sqlite3.connect(self.merged_db_path)
        self.get_table_info(merged_conn)

        cursor = merged_conn.cursor()
        for table in self.primary_keys.keys():
            if table not in ["grdb_migrations", "LastModified"]:
                cursor.execute(f"DELETE FROM [{table}];")
        merged_conn.commit()
        return merged_conn

    def _finalize_merge(self, merged_conn):
        """Stamp LastModified and collect media file paths for the archive."""
        cursor = merged_conn.cursor()
        cursor.execute(
            "UPDATE LastModified SET LastModified = strftime('%Y-%m-%dT%H:%M:%SZ', 'now');"
        )
        merged_conn.commit()

        for table, col in [
            ("IndependentMedia", "FilePath"),
            ("PlaylistItem", "ThumbnailFilePath"),
        ]:
            try:
                cursor.execute(
                    f"SELECT [{col}] FROM [{table}] WHERE [{col}] IS NOT NULL"
                )
                self.files_to_include_in_archive.extend(
                    [r[0] for r in cursor.fetchall()]
                )
            except sqlite3.Error:
                pass

        self.files_to_include_in_archive = list(set(self.files_to_include_in_archive))
        merged_conn.close()

    def process_databases(self, database_files):
        """
        Main entry point.  For each source DB:
          1. Build/refresh the in-memory identity index from the current merged state.
          2. Process every table in dependency order with a fresh pk_remap.
          3. Commit once per source DB.
        """
        merged_conn = self._initialize_merge(database_files)
        merged_cursor = merged_conn.cursor()

        # Collect unique KeySymbols from all source databases
        all_keysymbols = set()
        for file_path in database_files:
            conn = sqlite3.connect(file_path)
            cursor = conn.cursor()
            try:
                cursor.execute(
                    "SELECT DISTINCT KeySymbol FROM Location WHERE KeySymbol IS NOT NULL"
                )
                all_keysymbols.update([r[0] for r in cursor.fetchall()])
            except sqlite3.Error:
                pass
            conn.close()

        sorted_keys = sorted(list(all_keysymbols))
        if sorted_keys:
            self._configure_color_preference()

            if self._ask_confirm(
                "Would you like to ignore certain publications for highlight merge?"
            ):
                self.ignored_keysymbols = (
                    self._ask_checkbox(
                        "Select publications to ignore for highlight merging:",
                        choices=sorted_keys,
                    )
                    or []
                )

            remaining_keys = [
                k for k in sorted_keys if k not in self.ignored_keysymbols
            ]
            if remaining_keys and self._ask_confirm(
                "Should some publications autoresolve highlight issues by choosing preferred source?"
            ):
                auto_keys = (
                    self._ask_checkbox(
                        "Select publications to autoresolve highlight issues:",
                        choices=remaining_keys,
                    )
                    or []
                )

                for key in auto_keys:
                    print(f"\nConfiguring preference for {key}:")
                    # Show file basenames for easier selection
                    choices = [
                        f"{i + 1}: {path.basename(f)}"
                        for i, f in enumerate(database_files)
                    ]
                    preference = []
                    temp_choices = list(choices)
                    for i in range(len(database_files)):
                        p = self._ask_select(
                            f"Select priority #{i + 1} source for {key}:",
                            choices=temp_choices,
                        )
                        preference.append(database_files[choices.index(p)])
                        temp_choices.remove(p)
                        if len(temp_choices) == 1:
                            preference.append(
                                database_files[choices.index(temp_choices[0])]
                            )
                            break
                    self.autoresolve_config[key] = preference

        for file_path in tqdm(database_files, desc="Merging databases"):
            # Fresh per-DB remap: old_pk → new_pk, keyed by original table name
            pk_remap = {}

            # Rebuild identity index from current merged state before each DB pass.
            # This ensures newly inserted rows from previous DBs are visible.
            identity_index = self._build_identity_index(merged_cursor)

            source_conn = sqlite3.connect(file_path)
            source_cursor = source_conn.cursor()

            # UserMark needs special overlap handling; collect decisions here so
            # BlockRange processing (which comes after) can skip losing ranges.
            usermark_skip_source_pks = set()  # source BlockRange PKs to skip

            for table_name in self.table_order:
                table = self.table_name_map.get(table_name.lower())
                if not table or table not in self.primary_keys:
                    continue

                pk_remap.setdefault(table, {})

                try:
                    source_cursor.execute(f"SELECT * FROM [{table}]")
                except sqlite3.Error:
                    continue

                cols = [d[0] for d in source_cursor.description]
                rows = source_cursor.fetchall()

                if table_name == "UserMark":
                    self._merge_usermark_table(
                        table,
                        rows,
                        cols,
                        source_cursor,
                        merged_cursor,
                        pk_remap,
                        identity_index,
                        usermark_skip_source_pks,
                        file_path,
                    )
                elif table_name == "BlockRange":
                    self._merge_blockrange_table(
                        table,
                        rows,
                        cols,
                        merged_cursor,
                        pk_remap,
                        identity_index,
                        usermark_skip_source_pks,
                    )
                else:
                    for row in rows:
                        self._merge_row(
                            table,
                            table_name,
                            dict(zip(cols, row)),
                            merged_cursor,
                            pk_remap,
                            identity_index,
                        )

            source_conn.close()
            merged_conn.commit()

        self._finalize_merge(merged_conn)

    def _configure_color_preference(self):
        """Prompt once for preferred highlight color order used in identical-text autoresolve."""
        color_names = {
            1: "yellow",
            2: "green",
            3: "blue",
            4: "red",
            5: "orange",
            6: "purple",
        }

        if not self._ask_confirm(
            "Set highlight color priority for identical-text auto-resolution?",
            default=False,
        ):
            return

        available = list(self.color_preference)
        preference = []
        for idx in range(len(available)):
            choices = [
                {
                    "name": f"{color_names.get(c, f'color_{c}')} (#{c})",
                    "value": c,
                }
                for c in available
            ]
            picked = self._ask_select(
                f"Choose preferred color #{idx + 1}:",
                choices=choices,
                default=available[0],
            )
            if picked not in available:
                picked = available[0]
            preference.append(picked)
            available.remove(picked)

        if preference:
            self.color_preference = preference

    # ------------------------------------------------------------------
    # Generic row merge
    # ------------------------------------------------------------------

    def _merge_row(
        self, table, table_name, row_dict, merged_cursor, pk_remap, identity_index
    ):
        """
        Merge a single row:
          1. Remap all FK columns using pk_remap (parents already fully processed).
          2. Build identity tuple from the (now-remapped) row.
          3. O(1) lookup in identity_index.
          4a. Found + auto-increment table -> record pk mapping, resolve conflicts.
          4b. Found + composite PK table   -> skip insert (duplicate).
          5a. Not found + auto-increment   -> insert (omit PK col), use lastrowid, update index.
          5b. Not found + composite PK     -> insert all columns (PK cols are remapped FK values).
        """
        autoincrement = self._is_autoincrement_table(table)
        pk_cols = self.primary_keys.get(table, [])
        # Only auto-increment tables have a single source PK worth tracking
        old_pk = row_dict.get(pk_cols[0]) if autoincrement and pk_cols else None

        # 1. Remap all FK columns (mutates row_dict in place)
        self._remap_fks(table, row_dict, pk_remap)

        # 2. Identity tuple - built AFTER FK remap so FK-based identity cols are correct
        id_cols = self.identity_keys.get(table_name, [])
        identity_tuple = tuple(row_dict.get(c) for c in id_cols)

        # 3. Lookup -> (found: bool, existing_pk: int | None)
        found, existing_pk = self._index_lookup(
            table_name, identity_tuple, identity_index
        )

        new_pk = None
        if found:
            # --- Duplicate row ---
            if autoincrement and old_pk is not None and existing_pk is not None:
                pk_remap[table][old_pk] = existing_pk

            # Conflict resolution only applies to auto-increment tables with a real pk
            if (
                table_name in ("Note", "Bookmark", "InputField")
                and existing_pk is not None
            ):
                self._resolve_conflict(
                    table, table_name, merged_cursor, existing_pk, row_dict
                )
        else:
            # --- New row ---
            if table_name == "Note":
                self.note_bases[row_dict.get("Guid")] = {
                    "title": row_dict.get("Title"),
                    "content": row_dict.get("Content"),
                }

            if autoincrement:
                # Omit the PK column - SQLite assigns a fresh sequential value
                insert_dict = {k: v for k, v in row_dict.items() if k != pk_cols[0]}
                new_pk = self._insert_row(table, table_name, insert_dict, merged_cursor)
                if new_pk is not None:
                    if old_pk is not None:
                        pk_remap[table][old_pk] = new_pk
                    if id_cols:
                        identity_index.setdefault(table_name, {})[identity_tuple] = (
                            new_pk
                        )
            else:
                # Composite PK table - insert all columns including the (remapped) PK cols
                new_pk = self._insert_row(table, table_name, row_dict, merged_cursor)
                if new_pk is not None and id_cols:
                    # True sentinel: these tables are never FK targets, no int pk needed
                    identity_index.setdefault(table_name, {})[identity_tuple] = True

        return existing_pk if found else new_pk

    def _insert_row(self, table, table_name, insert_dict, merged_cursor):
        """Insert a row (PK already excluded from insert_dict). Returns new PK."""
        # TagMap has a unique constraint on (TagId, Position); shift positions if needed.
        if table_name == "TagMap":
            return self._insert_tagmap(table, insert_dict, merged_cursor)

        cols = ", ".join(f"[{k}]" for k in insert_dict)
        placeholders = ", ".join("?" * len(insert_dict))
        query = f"INSERT INTO [{table}] ({cols}) VALUES ({placeholders})"
        try:
            merged_cursor.execute(query, list(insert_dict.values()))
            return merged_cursor.lastrowid
        except sqlite3.Error as e:
            self.output["errors"].append((table, query, e))
            return None

    def _insert_tagmap(self, table, insert_dict, merged_cursor):
        """Insert TagMap row, shifting existing positions to avoid constraint violation."""
        cols = ", ".join(f"[{k}]" for k in insert_dict)
        placeholders = ", ".join("?" * len(insert_dict))
        query = f"INSERT INTO [{table}] ({cols}) VALUES ({placeholders})"
        try:
            merged_cursor.execute(query, list(insert_dict.values()))
            return merged_cursor.lastrowid
        except sqlite3.IntegrityError as e:
            if "TagMap.TagId, TagMap.Position" in str(e):
                tag_id = insert_dict.get("TagId")
                position = insert_dict.get("Position")
                merged_cursor.execute(
                    f"SELECT TagMapId, Position FROM [{table}] WHERE TagId = ? AND Position >= ? ORDER BY Position DESC",
                    (tag_id, position),
                )
                for tid, pos in merged_cursor.fetchall():
                    merged_cursor.execute(
                        f"UPDATE [{table}] SET Position = ? WHERE TagMapId = ?",
                        (pos + 1, tid),
                    )
                merged_cursor.execute(query, list(insert_dict.values()))
                return merged_cursor.lastrowid
            else:
                self.output["errors"].append((table, query, e))
                return None

    # ------------------------------------------------------------------
    # UserMark: overlap / connected-component merge
    # ------------------------------------------------------------------

    def _merge_usermark_table(
        self,
        table,
        rows,
        cols,
        source_cursor,
        merged_cursor,
        pk_remap,
        identity_index,
        usermark_skip_source_pks,
        file_path,
    ):
        """
        Process UserMark rows with overlap detection.

        Strategy:
          - Group incoming rows by LocationId (after FK remap).
          - For each location, gather existing merged highlights + incoming highlights.
          - Find connected components (identical signature or overlapping token ranges).
          - For each component, pick one winner; remap all losers to the winner's PK.
          - Populate usermark_skip_source_pks with source BlockRange PKs that belong
            to losing incoming highlights (so _merge_blockrange_table skips them).
        """
        pk_col = self.primary_keys[table][0]

        # Remap FKs for all incoming rows first, group by remapped LocationId
        remapped_rows = []
        for row in rows:
            rd = dict(zip(cols, row))
            self._remap_fks(table, rd, pk_remap)
            remapped_rows.append(rd)

        loc_to_rows = {}
        for rd in remapped_rows:
            loc_id = rd.get("LocationId")
            loc_to_rows.setdefault(loc_id, []).append(rd)

        for loc_id, incoming_rows in loc_to_rows.items():
            # --- Check if this location's publication should be ignored ---
            merged_cursor.execute(
                "SELECT KeySymbol FROM Location WHERE LocationId = ?", (loc_id,)
            )
            res = merged_cursor.fetchone()
            if res and res[0] in self.ignored_keysymbols:
                continue

            # --- Gather existing merged highlights for this location ---
            merged_cursor.execute(
                "SELECT UserMarkId, ColorIndex FROM UserMark WHERE LocationId = ?",
                (loc_id,),
            )
            existing_highlights = []
            for um_id, color in merged_cursor.fetchall():
                merged_cursor.execute(selectBlockRangeSql, (um_id,))
                existing_highlights.append(
                    {
                        "usermark_id": um_id,
                        "color": color,
                        "ranges": sorted(merged_cursor.fetchall()),
                        "source": "current",
                        "source_path": self.usermark_sources.get(um_id),
                    }
                )

            # --- Gather incoming highlights ---
            incoming_highlights = []
            for rd in incoming_rows:
                old_pk = rd.get(pk_col)
                source_cursor.execute(selectBlockRangeSql, (old_pk,))
                incoming_highlights.append(
                    {
                        "usermark_id": old_pk,
                        "color": rd.get("ColorIndex"),
                        "ranges": sorted(source_cursor.fetchall()),
                        "source": "incoming",
                        "source_path": file_path,
                        "row_dict": rd,
                    }
                )

            all_highlights = existing_highlights + incoming_highlights

            # --- Connected components ---
            components = self._find_highlight_components(all_highlights)

            for comp in components:
                # Group by (color, ranges) signature
                sig_groups = {}
                for hl in comp:
                    sig = (hl["color"], tuple(hl["ranges"]))
                    sig_groups.setdefault(sig, []).append(hl)

                if len(sig_groups) > 1:
                    chosen = self._resolve_usermark_conflict(
                        loc_id, sig_groups, merged_cursor
                    )
                else:
                    proto_list = list(sig_groups.values())[0]
                    chosen = {
                        "color": proto_list[0]["color"],
                        "ranges": proto_list[0]["ranges"],
                        "highlights": proto_list,
                    }

                self._apply_usermark_choice(
                    table,
                    pk_col,
                    comp,
                    chosen,
                    merged_cursor,
                    source_cursor,
                    pk_remap,
                    identity_index,
                    usermark_skip_source_pks,
                    file_path,
                )

    def _apply_usermark_choice(
        self,
        table,
        pk_col,
        comp,
        chosen,
        merged_cursor,
        source_cursor,
        pk_remap,
        identity_index,
        usermark_skip_source_pks,
        file_path,
    ):
        """
        Write the winning highlight into the merged DB and record all PK remappings.

        - If the winner already exists in merged (source=="current"), keep it and
          remap all incoming losers to it.
        - If the winner is incoming-only, insert it and remap everyone to the new PK.
        - Delete any existing merged highlights that lost.
        - Record source BlockRange PKs for losing incoming highlights so they are skipped.
        """
        # Prefer an already-merged highlight as the lead to minimise DB writes.
        lead_hl = (
            next((h for h in chosen["highlights"] if h["source"] == "current"), None)
            or chosen["highlights"][0]
        )

        lead_merged_pk = None

        if lead_hl["source"] == "current":
            lead_merged_pk = lead_hl["usermark_id"]
            self.usermark_sources[lead_merged_pk] = lead_hl.get("source_path")
            # Sync color if needed
            merged_cursor.execute(
                "UPDATE UserMark SET ColorIndex = ? WHERE UserMarkId = ?",
                (chosen["color"], lead_merged_pk),
            )
            # Rebuild BlockRanges to match chosen ranges
            merged_cursor.execute(
                "DELETE FROM BlockRange WHERE UserMarkId = ?", (lead_merged_pk,)
            )
            for r in chosen["ranges"]:
                merged_cursor.execute(
                    "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                    list(r) + [lead_merged_pk],
                )
        else:
            # Insert the incoming winner with a fresh auto-increment PK.
            # First, remove any existing row with the same UserMarkGuid to avoid
            # a UNIQUE constraint violation (it would be deleted as a loser anyway).
            # Re-point any dependents (Notes, etc.) to the new winner PK afterward.
            incoming_guid = lead_hl["row_dict"].get("UserMarkGuid")
            guid_evicted_pk = None
            if incoming_guid is not None:
                merged_cursor.execute(
                    "SELECT UserMarkId FROM UserMark WHERE UserMarkGuid = ?",
                    (incoming_guid,),
                )
                existing_by_guid = merged_cursor.fetchone()
                if existing_by_guid is not None:
                    guid_evicted_pk = existing_by_guid[0]
                    merged_cursor.execute(
                        "DELETE FROM BlockRange WHERE UserMarkId = ?",
                        (guid_evicted_pk,),
                    )
                    merged_cursor.execute(
                        "DELETE FROM UserMark WHERE UserMarkId = ?", (guid_evicted_pk,)
                    )

            rd = {k: v for k, v in lead_hl["row_dict"].items() if k != pk_col}
            cols_str = ", ".join(f"[{k}]" for k in rd)
            placeholders = ", ".join("?" * len(rd))
            merged_cursor.execute(
                f"INSERT INTO [{table}] ({cols_str}) VALUES ({placeholders})",
                list(rd.values()),
            )
            lead_merged_pk = merged_cursor.lastrowid

            # Insert BlockRanges for the incoming winner (they will be skipped by
            # _merge_blockrange_table because their source PKs are in usermark_skip_source_pks)
            for r in chosen["ranges"]:
                merged_cursor.execute(
                    "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                    list(r) + [lead_merged_pk],
                )

            # Re-point Notes that were attached to the evicted row to the new winner
            if guid_evicted_pk is not None:
                merged_cursor.execute(
                    "UPDATE Note SET UserMarkId = ? WHERE UserMarkId = ?",
                    (lead_merged_pk, guid_evicted_pk),
                )

        # Delete any OTHER existing merged highlights in this component (losers)
        for hl in comp:
            if hl["source"] == "current" and hl["usermark_id"] != lead_merged_pk:
                merged_cursor.execute(
                    "UPDATE Note SET UserMarkId = ? WHERE UserMarkId = ?",
                    (lead_merged_pk, hl["usermark_id"]),
                )
                # Add more UPDATE statements here if future schema adds FK refs to UserMark
                merged_cursor.execute(
                    "DELETE FROM BlockRange WHERE UserMarkId = ?", (hl["usermark_id"],)
                )
                merged_cursor.execute(
                    "DELETE FROM UserMark WHERE UserMarkId = ?", (hl["usermark_id"],)
                )

        # Map ALL incoming highlights in this component to lead_merged_pk
        for hl in comp:
            if hl["source"] == "incoming":
                old_pk = hl["usermark_id"]
                pk_remap[table][old_pk] = lead_merged_pk

                # Mark this incoming highlight's BlockRanges for skipping
                source_cursor.execute(
                    "SELECT BlockRangeId FROM BlockRange WHERE UserMarkId = ?",
                    (old_pk,),
                )
                for (br_id,) in source_cursor.fetchall():
                    usermark_skip_source_pks.add(br_id)

    def _merge_blockrange_table(
        self,
        table,
        rows,
        cols,
        merged_cursor,
        pk_remap,
        identity_index,
        usermark_skip_source_pks,
    ):
        """
        Process BlockRange rows.  Rows whose source PK is in usermark_skip_source_pks
        are skipped because _apply_usermark_choice already wrote them directly.
        All others go through the normal _merge_row path.
        """
        pk_col = self.primary_keys[table][0]
        for row in rows:
            row_dict = dict(zip(cols, row))
            if row_dict.get(pk_col) in usermark_skip_source_pks:
                continue
            self._merge_row(
                table, "BlockRange", row_dict, merged_cursor, pk_remap, identity_index
            )

    # ------------------------------------------------------------------
    # UserMark conflict helpers (unchanged logic, cleaner signatures)
    # ------------------------------------------------------------------

    def _find_highlight_components(self, all_highlights):
        """Find connected components by identical signature or token-range overlap."""
        n = len(all_highlights)
        adj = {i: set() for i in range(n)}
        for i in range(n):
            for j in range(i + 1, n):
                h1, h2 = all_highlights[i], all_highlights[j]
                same_sig = h1["color"] == h2["color"] and h1["ranges"] == h2["ranges"]
                overlap = False
                if not same_sig:
                    for r1 in h1["ranges"]:
                        for r2 in h2["ranges"]:
                            if r1[0] == r2[0] and r1[1] == r2[1]:
                                if r1[2] < r2[3] and r2[2] < r1[3]:
                                    overlap = True
                                    break
                        if overlap:
                            break
                if same_sig or overlap:
                    adj[i].add(j)
                    adj[j].add(i)

        visited = set()
        components = []
        for i in range(n):
            if i not in visited:
                comp = []
                stack = [i]
                visited.add(i)
                while stack:
                    curr = stack.pop()
                    comp.append(all_highlights[curr])
                    for nb in adj[curr]:
                        if nb not in visited:
                            visited.add(nb)
                            stack.append(nb)
                components.append(comp)
        return components

    def _is_interactive_terminal(self):
        return sys.stdin.isatty() and sys.stdout.isatty()

    def _ask_confirm(self, message, default=False):
        if not self._is_interactive_terminal():
            return default
        answer = questionary.confirm(message).ask()
        return default if answer is None else answer

    def _ask_checkbox(self, message, choices):
        if not self._is_interactive_terminal():
            return []
        answer = questionary.checkbox(message, choices=choices).ask()
        return answer or []

    def _ask_select(self, message, choices, default=None):
        if not self._is_interactive_terminal():
            if isinstance(default, dict):
                return default.get("value")
            return default
        answer = questionary.select(message, choices=choices).ask()
        if answer is None:
            if isinstance(default, dict):
                return default.get("value")
            return default
        return answer

    def _fetch_highlight_variant_text(self, loc_res, ranges):
        if not loc_res:
            return None
        full_text = []
        for r in ranges:
            txt = self.get_highlighted_text(
                loc_res[0],
                r[1],
                r[2],
                r[3],
                loc_res[1],
                loc_res[2],
                loc_res[3],
                loc_res[4],
            )
            if txt:
                full_text.append(txt)
        return " [...] ".join(full_text) if full_text else None

    def _prefetch_variant_texts(self, loc_res, sig_groups):
        if not loc_res:
            return {}

        sig_items = list(sig_groups.items())
        texts = {}
        with ThreadPoolExecutor(max_workers=self.text_prefetch_workers) as executor:
            future_map = {
                executor.submit(
                    self._fetch_highlight_variant_text, loc_res, sig[1]
                ): sig
                for sig, _ in sig_items
            }
            for future in as_completed(future_map):
                sig = future_map[future]
                try:
                    texts[sig] = future.result()
                except Exception:
                    texts[sig] = None
        return texts

    def _range_contains(self, outer, inner):
        """True if outer BlockRange fully contains inner BlockRange (same block/identifier)."""
        return (
            outer[0] == inner[0]
            and outer[1] == inner[1]
            and outer[2] <= inner[2]
            and outer[3] >= inner[3]
        )

    def _ranges_contain_other_ranges(self, outer_ranges, inner_ranges):
        """True if every inner range is fully covered by at least one outer range."""
        if not outer_ranges or not inner_ranges:
            return False
        for inner in inner_ranges:
            if not any(self._range_contains(outer, inner) for outer in outer_ranges):
                return False
        return True

    def _find_containment_parent_option(self, options):
        """
        Return (parent_idx, contained_indices) when one option contains all other options' ranges.
        """
        if len(options) < 2:
            return (None, [])

        for p_idx, parent in enumerate(options):
            contained = []
            for c_idx, child in enumerate(options):
                if p_idx == c_idx:
                    continue
                if self._ranges_contain_other_ranges(parent["ranges"], child["ranges"]):
                    contained.append(c_idx)
            if len(contained) == len(options) - 1:
                return (p_idx, contained)

        return (None, [])

    def _pick_option_by_preference(self, option_subset):
        """Deterministically pick one option by color preference, then current-source bias."""
        ranked = sorted(
            option_subset,
            key=lambda o: (
                self.color_preference.index(o["color"])
                if o["color"] in self.color_preference
                else len(self.color_preference),
                0 if any(h.get("source") == "current" for h in o["highlights"]) else 1,
            ),
        )
        return ranked[0]

    def _resolve_containment_fold_choice(
        self, loc_res, options, conflict_key, color_names
    ):
        """
        If one option fully contains all others, ask which contained option it should fold into.
        Returns chosen option or None when no containment pattern is found.
        """
        parent_idx, contained_indices = self._find_containment_parent_option(options)
        if parent_idx is None:
            return None

        parent = options[parent_idx]
        contained_opts = [options[i] for i in contained_indices]

        print(
            "  Detected container highlight pattern (one variant fully contains the others)."
        )
        print(
            "  Choose which contained variant the container highlight should be folded into."
        )

        containment_key = (
            "containment-fold",
            conflict_key,
            tuple(sorted((o["color"], tuple(o["ranges"])) for o in contained_opts)),
            (parent["color"], tuple(parent["ranges"])),
        )
        cached = self.conflict_cache["UserMark"].get(containment_key)
        if cached:
            chosen = next(
                (
                    o
                    for o in contained_opts
                    if (o["color"], tuple(o["ranges"])) == cached
                ),
                None,
            )
            if chosen is not None:
                print("  (Using previously resolved containment fold choice)")
                return chosen

        choices = []
        for idx, opt in enumerate(contained_opts, 1):
            cname = color_names.get(opt["color"], f"color_{opt['color']}")
            choices.append(
                {
                    "name": f"Fold into Option {idx}: {cname} (instances: {len(opt['highlights'])})",
                    "value": idx,
                }
            )

        default_choice = self._pick_option_by_preference(contained_opts)
        default_idx = contained_opts.index(default_choice) + 1
        chosen_idx = self._ask_select(
            "Container highlight detected — choose contained target:",
            choices=choices,
            default=default_idx,
        )
        if (
            not isinstance(chosen_idx, int)
            or chosen_idx < 1
            or chosen_idx > len(contained_opts)
        ):
            chosen_idx = default_idx

        chosen = contained_opts[chosen_idx - 1]
        self.conflict_cache["UserMark"][containment_key] = (
            chosen["color"],
            tuple(chosen["ranges"]),
        )
        return chosen

    def _resolve_usermark_conflict(self, loc_id, sig_groups, merged_cursor):
        """Prompt the user to pick a highlight variant, with caching."""
        loc_info = self.get_location_info(merged_cursor, loc_id)
        print(f"\nConflict in Highlight at {loc_info}:")
        print(
            f"  Found {sum(len(v) for v in sig_groups.values())} highlight(s) with {len(sig_groups)} unique variant(s)"
        )

        color_names = {
            1: "yellow",
            2: "green",
            3: "blue",
            4: "red",
            5: "orange",
            6: "purple",
        }
        color_codes = {
            1: "\033[93m",
            2: "\033[92m",
            3: "\033[94m",
            4: "\033[91m",
            5: "\033[38;5;208m",
            6: "\033[95m",
        }
        RESET = "\033[0m"

        merged_cursor.execute(selectLocationSql, (loc_id,))
        loc_res = merged_cursor.fetchone()
        if loc_res:
            print("  Fetching text context from JW.org...")

        prefetched_text = self._prefetch_variant_texts(loc_res, sig_groups)

        options = []
        normalized_option_text = {}
        for idx, (sig, group) in enumerate(sig_groups.items(), 1):
            color, ranges = sig
            sources = sorted({hl["source"] for hl in group})
            color_name = color_names.get(color, f"color_{color}")
            color_code = color_codes.get(color, "")
            print(
                f"\n  Option {idx}: {color_code}{color_name}{RESET} ({len(group)} instance(s): {', '.join(sources)})"
            )
            text = prefetched_text.get(sig)
            if text:
                normalized_option_text[sig] = " ".join(text.split()).casefold()
            print(
                f"    Text: {color_code}{text if text else '(Text unavailable)'}{RESET}"
            )
            options.append(
                {"color": color, "ranges": list(ranges), "highlights": group}
            )

        conflict_key = (loc_res, tuple(sorted(sig_groups.keys())))

        # Containment-specific decision: one parent/container + contained variants.
        containment_choice = self._resolve_containment_fold_choice(
            loc_res, options, conflict_key, color_names
        )
        if containment_choice is not None:
            self.conflict_cache["UserMark"][conflict_key] = (
                containment_choice["color"],
                tuple(containment_choice["ranges"]),
            )
            return containment_choice

        # --- Autoresolve logic ---
        keysymbol = loc_res[2] if loc_res else None

        # Autoresolve if every option renders to the exact same text.
        unique_texts = {
            t
            for t in normalized_option_text.values()
            if t and t != "(text unavailable)"
        }
        if len(unique_texts) == 1 and len(normalized_option_text) == len(options):
            chosen = self._pick_option_by_preference(options)
            chosen_color_name = color_names.get(
                chosen["color"], f"color_{chosen['color']}"
            )
            print(
                "  (Autoresolved: all variants have identical highlight text; "
                f"selected preferred color '{chosen_color_name}')"
            )
            self.conflict_cache["UserMark"][conflict_key] = (
                chosen["color"],
                tuple(chosen["ranges"]),
            )
            return chosen

        if keysymbol in self.autoresolve_config:
            preference = self.autoresolve_config[keysymbol]
            # preference is a list of database_files in order of priority.
            # We need to find which variant (option) has an instance from the highest priority source.
            # hl["source"] is the filename if incoming, or "current" if it was already in merged.
            # Since "current" is from databases processed earlier, we should ideally know which DB it came from.
            # However, for simplicity, we can treat "current" as having come from one of the previous DBs.
            # Let's refine the source tagging in _merge_usermark_table to be the absolute path.

            for pref_path in preference:
                for opt in options:
                    # Check if any highlight in this option comes from pref_path
                    if any(
                        hl.get("source_path") == pref_path for hl in opt["highlights"]
                    ):
                        print(
                            f"  (Autoresolved to variant from {path.basename(pref_path)})"
                        )
                        self.conflict_cache["UserMark"][conflict_key] = (
                            opt["color"],
                            tuple(opt["ranges"]),
                        )
                        return opt

        choice_sig = self.conflict_cache["UserMark"].get(conflict_key)
        if choice_sig:
            print("  (Using previously resolved choice)")
            return next(
                o for o in options if (o["color"], tuple(o["ranges"])) == choice_sig
            )

        # Build choices for questionary
        choices = []
        for idx, opt in enumerate(options, 1):
            color_name = color_names.get(opt["color"], f"color_{opt['color']}")
            # We can't use ANSI codes easily in questionary labels if we want it to look good,
            # but we can just use the name.
            choices.append(
                {
                    "name": f"Option {idx}: {color_name} (Instances: {len(opt['highlights'])})",
                    "value": idx,
                }
            )

        choice_idx = self._ask_select(
            "Choose highlight variant:", choices=choices, default=1
        )

        chosen = options[choice_idx - 1]
        self.conflict_cache["UserMark"][conflict_key] = (
            chosen["color"],
            tuple(chosen["ranges"]),
        )
        return chosen

    # ------------------------------------------------------------------
    # Generic conflict resolution (Note, Bookmark, InputField)
    # ------------------------------------------------------------------

    def _resolve_conflict(
        self, table, table_name, merged_cursor, existing_pk, row_dict
    ):
        """Dispatch conflict resolution for mutable tables."""
        pk_col = self.primary_keys[table][0]
        merged_cursor.execute(
            f"SELECT * FROM [{table}] WHERE [{pk_col}] = ?", (existing_pk,)
        )
        merged_cursor_desc = merged_cursor.description
        current_row_raw = merged_cursor.fetchone()
        if current_row_raw is None:
            return
        cols = [d[0] for d in merged_cursor_desc]
        current_row = dict(zip(cols, current_row_raw))

        diffs = {
            c: (current_row.get(c), row_dict[c])
            for c in row_dict
            if c not in self.primary_keys[table]
            and row_dict.get(c) != current_row.get(c)
        }
        if not diffs:
            return

        if table_name == "Note":
            self._handle_note_merge(
                table, merged_cursor, existing_pk, row_dict, current_row
            )
        elif table_name in ("Bookmark", "InputField"):
            self._handle_simple_conflict(
                table,
                table_name,
                merged_cursor,
                existing_pk,
                row_dict,
                current_row,
                diffs,
            )

    def _handle_simple_conflict(
        self,
        table,
        table_name,
        merged_cursor,
        existing_pk,
        row_dict,
        current_row,
        diffs,
    ):
        """Resolve Bookmark or InputField conflicts via user prompt."""
        loc_info = self.get_location_info(merged_cursor, current_row.get("LocationId"))
        print(f"\nConflict in {table_name} at {loc_info}:")
        for col, (old_v, new_v) in diffs.items():
            print(f"  {col}: current='{old_v}' vs incoming='{new_v}'")

        options = ["c", "i"]
        merged_val = None
        if table_name == "InputField":
            options.append("m")
            merged_val = self.merge_text(
                None, current_row.get("Value"), row_dict.get("Value")
            )
            print(f"  Merged value: '{merged_val}'")

        merged_cursor.execute(selectLocationSql, (current_row.get("LocationId"),))
        loc_res = merged_cursor.fetchone()
        conflict_key = (
            table_name,
            loc_res,
            current_row.get("Slot" if table_name == "Bookmark" else "TextTag"),
            tuple(sorted(diffs.items())),
        )

        choice = self.conflict_cache[table_name].get(conflict_key, "")
        if choice:
            print(f"  (Using previously resolved choice: {choice})")
        else:
            choices = [
                {"name": "Keep (c)urrent", "value": "c"},
                {"name": "Keep (i)ncoming", "value": "i"},
            ]
            if "m" in options:
                choices.append({"name": "Keep (m)erged", "value": "m"})

            choice = self._ask_select(
                f"Conflict in {table_name}:", choices=choices, default="c"
            )
            self.conflict_cache[table_name][conflict_key] = choice

        if choice == "i":
            set_clause = ", ".join(f"[{k}] = ?" for k in diffs)
            merged_cursor.execute(
                f"UPDATE [{table}] SET {set_clause} WHERE [{self.primary_keys[table][0]}] = ?",
                [row_dict[k] for k in diffs] + [existing_pk],
            )
        elif choice == "m" and table_name == "InputField":
            merged_cursor.execute(
                f"UPDATE [{table}] SET Value = ? WHERE [{self.primary_keys[table][0]}] = ?",
                (merged_val, existing_pk),
            )

    def _handle_note_merge(
        self, table, merged_cursor, existing_pk, row_dict, current_row
    ):
        """3-way merge for Note title and content."""
        guid = row_dict.get("Guid")
        base = self.note_bases.get(
            guid,
            {
                "title": current_row.get("Title"),
                "content": current_row.get("Content"),
            },
        )

        merged_title = self.merge_text(
            base.get("title"),
            current_row.get("Title") or "",
            row_dict.get("Title") or "",
        )
        merged_content = self.merge_text(
            base.get("content"),
            current_row.get("Content") or "",
            row_dict.get("Content") or "",
        )

        if row_dict.get("Title") == current_row.get("Title") and row_dict.get(
            "Content"
        ) == current_row.get("Content"):
            return

        loc_info = self.get_location_info(merged_cursor, current_row.get("LocationId"))
        print(f"\nConflict in Note at {loc_info} (GUID: {guid}):")

        merged_cursor.execute(selectLocationSql, (current_row.get("LocationId"),))
        loc_res = merged_cursor.fetchone()
        conflict_key = (
            guid,
            loc_res,
            (current_row.get("Title"), current_row.get("Content")),
            (row_dict.get("Title"), row_dict.get("Content")),
        )

        choice = self.conflict_cache["Note"].get(conflict_key, "")
        if choice:
            print(f"  (Using previously resolved choice: {choice})")
        else:
            if row_dict.get("Title") != current_row.get("Title"):
                print("\n--- Title Diff ---")
                self.print_diff(
                    current_row.get("Title") or "", row_dict.get("Title") or ""
                )
                print(f"Merged: {merged_title}")
            if row_dict.get("Content") != current_row.get("Content"):
                print("\n--- Content Diff ---")
                self.print_diff(
                    current_row.get("Content") or "", row_dict.get("Content") or ""
                )
                print(f"Merged: {merged_content}")
            choice = self._ask_select(
                "Conflict in Note:",
                choices=[
                    {"name": "Keep (c)urrent", "value": "c"},
                    {"name": "Keep (i)ncoming", "value": "i"},
                    {"name": "Keep (m)erged", "value": "m"},
                ],
                default="c",
            )
            self.conflict_cache["Note"][conflict_key] = choice

        final_t, final_c = current_row.get("Title"), current_row.get("Content")
        if choice == "i":
            final_t, final_c = row_dict.get("Title"), row_dict.get("Content")
        elif choice == "m":
            final_t, final_c = merged_title, merged_content

        latest_ts = max(
            row_dict.get("LastModified") or "",
            current_row.get("LastModified") or "",
        )
        merged_cursor.execute(
            f"UPDATE [{table}] SET Title = ?, Content = ?, LastModified = ? WHERE [{self.primary_keys[table][0]}] = ?",
            (final_t, final_c, latest_ts, existing_pk),
        )

    # ------------------------------------------------------------------
    # JWL archive creation
    # ------------------------------------------------------------------

    def create_jwl_file(self):
        merged_dir = path.join(self.working_folder, "merged")
        manifest_file_path = path.join(merged_dir, "manifest.json")
        all_unzip_folder_names = [
            d
            for d in listdir(self.working_folder)
            if d != "merged" and path.isdir(path.join(self.working_folder, d))
        ]
        first_jwl_unzip_folder_path = path.join(
            self.working_folder, all_unzip_folder_names[0]
        )

        makedirs(merged_dir, exist_ok=True)

        for file_name in tqdm(
            listdir(first_jwl_unzip_folder_path), desc="Adding base files to archive"
        ):
            if file_name.endswith(".png") or file_name.endswith(".json"):
                copy2(path.join(first_jwl_unzip_folder_path, file_name), merged_dir)

        for i in range(len(self.files_to_include_in_archive)):
            if not path.exists(self.files_to_include_in_archive[i]):
                found = glob(
                    path.join(
                        self.working_folder, "**", self.files_to_include_in_archive[i]
                    ),
                    recursive=True,
                )
                if found:
                    self.files_to_include_in_archive[i] = path.join(
                        path.dirname(found[0]),
                        self.files_to_include_in_archive[i],
                    )

        for f in tqdm(
            self.files_to_include_in_archive,
            desc="Adding additional media files to archive",
            disable=len(self.files_to_include_in_archive) == 0,
        ):
            if f != path.join(merged_dir, path.basename(f)):
                copy2(f, merged_dir)

        import json

        with open(manifest_file_path, "r") as file:
            manifest_data = json.load(file)

        database_file_path = path.join(
            merged_dir, manifest_data["userDataBackup"]["databaseName"]
        )
        copy2(self.merged_db_path, database_file_path)

        current_datetime = datetime.now()
        formatted_date = current_datetime.astimezone(tz.gettz("US/Eastern")).strftime(
            "%Y-%m-%dT%H:%M:%S%z"
        )
        manifest_data["creationDate"] = formatted_date

        name_timestamp = current_datetime.strftime("%Y-%m-%d-%H%M%S")
        merged_file_name = f"UserdataBackup_{name_timestamp}_{self.app_name}.jwlibrary"
        manifest_data["name"] = self.app_name

        user_data_backup = {
            "lastModifiedDate": formatted_date,
            "hash": self.calculate_sha256(database_file_path),
            "databaseName": manifest_data["userDataBackup"]["databaseName"],
            "schemaVersion": manifest_data["userDataBackup"]["schemaVersion"],
            "deviceName": self.app_name,
        }
        manifest_data["userDataBackup"] = user_data_backup

        with open(manifest_file_path, "w") as file:
            json.dump(manifest_data, file, indent=2)

        makedirs(self.jwl_output_folder, exist_ok=True)
        make_archive(
            path.join(self.jwl_output_folder, merged_file_name), "zip", merged_dir
        )

        output_jwl_file_path = path.abspath(
            path.join(self.jwl_output_folder, merged_file_name)
        )
        rename(output_jwl_file_path + ".zip", output_jwl_file_path)

        self.clean_temp_files()

        print()
        end_time = time()
        print(f"Work completed in {round(end_time - self.start_time, 1)} seconds.")
        print()
        print("Successfully created JW Library backup containing all merged user data!")
        print()
        print("Find it here:\n- ", output_jwl_file_path)
        print()
        return output_jwl_file_path

    # ------------------------------------------------------------------
    # Utilities
    # ------------------------------------------------------------------

    def print_diff(self, a, b):
        RED, GREEN, RESET = "\033[91m", "\033[92m", "\033[0m"
        diff = difflib.ndiff((a or "").splitlines(), (b or "").splitlines())
        for line in diff:
            if line.startswith("+ "):
                print(f"{GREEN}{line}{RESET}")
            elif line.startswith("- "):
                print(f"{RED}{line}{RESET}")
            elif line.startswith("? "):
                continue
            else:
                print(line)

    def get_highlighted_text(
        self,
        docid,
        identifier,
        start_token,
        end_token,
        meps_lang_code="0",
        keysym=None,
        book=None,
        chapter=None,
    ):
        try:
            lang_key = int(meps_lang_code) if meps_lang_code is not None else 0
        except (ValueError, TypeError):
            lang_key = 0

        lang_info = LANGUAGES.get(lang_key)
        if lang_info is None:
            print(f"Invalid language code: {meps_lang_code}")
            return None

        lang_code = lang_info.get("Symbol")
        ietf_code = lang_info.get("PrimaryIetfCode") or "en"
        if lang_code is None:
            return None

        if (
            keysym
            and "nwt" in keysym.lower()
            and book is not None
            and chapter is not None
        ):
            api_path = self.bible_api_cache.get(lang_code)
            if api_path == "None":
                api_path = None

            if not api_path:
                try:
                    home_url = f"https://www.jw.org/{ietf_code}"
                    r = requests.get(
                        home_url, headers={"User-Agent": self.user_agent}, timeout=5
                    )
                    r.raise_for_status()
                    match = None
                    if keysym:
                        match = re.search(
                            f'data-bible_data_api_{re.escape(keysym.lower())}="([^"]+)"',
                            r.text,
                        )
                    if not match:
                        match = re.search(
                            r'data-bible_data_api(_nwtsty|_nwt)?="([^"]+)"', r.text
                        )
                    if not match:
                        match = re.search(r'data-bible_data_api="([^"]+)"', r.text)
                    if match:
                        api_path = match.groups()[-1]
                        self.bible_api_cache[lang_code] = api_path
                    else:
                        self.bible_api_cache[lang_code] = "None"
                except Exception as e:
                    if self.debug:
                        print(f"Error discovering Bible API for {ietf_code}: {e}")

            if api_path and api_path != "None":
                book_id = book * 10
                range_start = f"{book_id}{chapter:02d}000"
                range_id = f"{range_start}-{book_id}{chapter:02d}999"
                url = f"https://www.jw.org{api_path}{range_id}"
                try:
                    data = self.doc_cache.get(url)
                    if not data:
                        r = requests.get(
                            url, headers={"User-Agent": self.user_agent}, timeout=10
                        )
                        r.raise_for_status()
                        data = r.json()
                        self.doc_cache[url] = data
                    if data:
                        ranges_data = data.get("ranges", {})
                        range_content = ranges_data.get(range_id) or (
                            list(ranges_data.values())[0] if ranges_data else None
                        )
                        if range_content:
                            verses = range_content.get("verses", [])
                            target_verse = next(
                                (
                                    v
                                    for v in verses
                                    if v.get("verseNumber") == int(identifier)
                                ),
                                None,
                            )
                            if target_verse:
                                content = target_verse.get("content", "")
                                parser = PExtractor()
                                parser.feed(content)
                                text = " ".join(parser.text.split())
                                tokens = re.findall(
                                    r"\w+(?:[''.:-]\w+)*|[^\s\w\u200b]", text
                                )
                                return " ".join(tokens[start_token : end_token + 1])
                except Exception as e:
                    if self.debug:
                        print(f"Error fetching Bible text from {url}: {e}")

        cache_key = (docid, lang_code)
        if cache_key in self.doc_cache:
            html_content = self.doc_cache[cache_key]
        else:
            url = f"https://www.jw.org/open?docid={docid}&wtlocale={lang_code}&appLanguage=E&prefer=content"
            try:
                r = requests.get(
                    url, headers={"User-Agent": self.user_agent}, timeout=5
                )
                if urlparse(r.url).path.count("/") <= 2:
                    raise ValueError(f"Invalid redirect to {r.url}")
                html_content = r.text
                self.doc_cache[cache_key] = html_content
            except Exception as e:
                print(f"Error fetching content: {e}")
                return None

        parser = PExtractor(identifier)
        parser.feed(html_content)
        full_text = parser.text
        if not full_text:
            return f"[Text not found for pid={identifier}]"

        tokens = re.findall(r"\w+(?:[''.:-]\w+)*|[^\s\w\u200b]", full_text)
        start_token = max(start_token, 0)
        end_token = min(end_token, len(tokens))
        return " ".join(tokens[start_token : end_token + 1])

    def get_location_info(self, cursor, location_id):
        if not location_id:
            return "Unknown Location"
        cursor.execute(
            "SELECT BookNumber, ChapterNumber, DocumentId, Title, KeySymbol, IssueTagNumber, MepsLanguage FROM Location WHERE LocationId = ?",
            (location_id,),
        )
        row = cursor.fetchone()
        if not row:
            return f"Location ID {location_id}"
        book, chapter, doc, title, keysym, issue, lang = row
        info = []
        if title:
            info.append(title)
        if keysym:
            info.append(keysym)
        if issue:
            info.append(str(issue))
        if lang:
            info.append(f"Lang {lang}")
        if book:
            info.append(f"Book {book}")
        if chapter:
            info.append(f"Ch. {chapter}")
        if not keysym and doc:
            info.append(f"Doc {doc}")
        return " ".join(info) if info else f"Location {location_id}"

    def merge_text(self, base, a, b):
        if a == b:
            return a
        if not a:
            return b
        if not b:
            return a
        if not base:
            if a in b:
                return b
            if b in a:
                return a
            sep = "\n" if "\n" in a or "\n" in b else " "
            return a + sep + b
        if a == base:
            return b
        if b == base:
            return a

        def get_change(orig, other):
            i = 0
            while i < len(orig) and i < len(other) and orig[i] == other[i]:
                i += 1
            j = 0
            while (
                j < (len(orig) - i)
                and j < (len(other) - i)
                and orig[-(j + 1)] == other[-(j + 1)]
            ):
                j += 1
            return i, len(orig) - j, other[i : len(other) - j] if j > 0 else other[i:]

        start_a, end_a, content_a = get_change(base, a)
        start_b, end_b, content_b = get_change(base, b)

        if end_a <= start_b:
            return (
                base[:start_a]
                + content_a
                + base[end_a:start_b]
                + content_b
                + base[end_b:]
            )
        if end_b <= start_a:
            return (
                base[:start_b]
                + content_b
                + base[end_b:start_a]
                + content_a
                + base[end_a:]
            )

        i = 0
        while i < len(base) and i < len(a) and i < len(b) and base[i] == a[i] == b[i]:
            i += 1
        prefix = base[:i]
        j = 0
        while (
            j < (len(base) - i)
            and j < (len(a) - i)
            and j < (len(b) - i)
            and base[-(j + 1)] == a[-(j + 1)] == b[-(j + 1)]
        ):
            j += 1
        suffix = base[len(base) - j :] if j > 0 else ""
        base_m = base[i : len(base) - j] if j > 0 else base[i:]
        a_m = a[i : len(a) - j] if j > 0 else a[i:]
        b_m = b[i : len(b) - j] if j > 0 else b[i:]

        if a_m == base_m:
            merged_m = b_m
        elif b_m == base_m:
            merged_m = a_m
        elif a_m in b_m:
            merged_m = b_m
        elif b_m in a_m:
            merged_m = a_m
        else:
            sep = "\n" if "\n" in a_m or "\n" in b_m else " "
            merged_m = a_m + sep + b_m

        return prefix + merged_m + suffix

    def clean_temp_files(self, force=False):
        if force or (not self.debug and len(self.output["errors"]) == 0):
            if path.isdir(self.working_folder):
                rmtree(self.working_folder)
            print()
            print("Cleaned up working directory!")

    def unzip_file(self, file_path):
        basename = path.splitext(path.basename(file_path))[0]
        unzip_path = path.join(self.working_folder, basename)
        unpack_archive(file_path, extract_dir=unzip_path, format="zip")
        return unzip_path

    def get_first_db_file(self, unzip_path):
        db_files = glob(unzip_path + "/*.db")
        return db_files[0] if db_files else None

    def get_jwl_files(self):
        file_paths = []
        if args.file is not None or args.folder is not None:
            if args.file:
                file_paths.extend(args.file)
            if args.folder:
                for file in listdir(args.folder):
                    if file.lower().endswith(".jwlibrary"):
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
            if file_paths:
                print("Provided arguments:")
                print("\n".join(["- " + p for p in [args.file, args.folder] if p]))
            exit()

        self.clean_temp_files(force=True)
        print(
            "JW Library backup files to be merged:\n"
            + "\n".join("- " + f for f in file_paths)
        )
        print()

        if path.exists(self.merged_db_path):
            remove(self.merged_db_path)

        db_paths = []
        for file_path in tqdm(file_paths, desc="Extracting databases"):
            db_path = self.get_first_db_file(self.unzip_file(file_path))
            copy2(db_path, self.merged_db_path)
            db_paths.append(db_path)
        return db_paths

    def calculate_sha256(self, file_path):
        import hashlib

        h = hashlib.sha256()
        with open(file_path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                h.update(chunk)
        return h.hexdigest()

    # ------------------------------------------------------------------
    # Tests
    # ------------------------------------------------------------------

    def _create_test_db(self, db_path, data_ops=None):
        # Always start fresh
        if path.exists(db_path):
            remove(db_path)
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        schema = [
            "CREATE TABLE IF NOT EXISTS Location (LocationId INTEGER PRIMARY KEY, BookNumber INTEGER, ChapterNumber INTEGER, DocumentId INTEGER, Track INTEGER, IssueTagNumber INTEGER, KeySymbol TEXT, MepsLanguage INTEGER, Type INTEGER, Title TEXT)",
            "CREATE TABLE IF NOT EXISTS Tag (TagId INTEGER PRIMARY KEY, Type INTEGER, Name TEXT)",
            "CREATE TABLE IF NOT EXISTS UserMark (UserMarkId INTEGER PRIMARY KEY, ColorIndex INTEGER, LocationId INTEGER, UserMarkGuid TEXT)",
            "CREATE TABLE IF NOT EXISTS BlockRange (BlockRangeId INTEGER PRIMARY KEY, BlockType INTEGER, Identifier INTEGER, StartToken INTEGER, EndToken INTEGER, UserMarkId INTEGER)",
            "CREATE TABLE IF NOT EXISTS Note (NoteId INTEGER PRIMARY KEY, Guid TEXT, Title TEXT, Content TEXT, LastModified TEXT, LocationId INTEGER, UserMarkId INTEGER)",
            "CREATE TABLE IF NOT EXISTS Bookmark (BookmarkId INTEGER PRIMARY KEY, PublicationLocationId INTEGER, Slot INTEGER, Title TEXT, Snippet TEXT, LocationId INTEGER)",
            "CREATE TABLE IF NOT EXISTS InputField (LocationId INTEGER REFERENCES Location(LocationId), TextTag TEXT, Value TEXT, PRIMARY KEY (LocationId, TextTag))",
            "CREATE TABLE IF NOT EXISTS TagMap (TagMapId INTEGER PRIMARY KEY, TagId INTEGER, PlaylistItemId INTEGER, LocationId INTEGER, NoteId INTEGER, Position INTEGER)",
            "CREATE TABLE IF NOT EXISTS PlaylistItem (PlaylistItemId INTEGER PRIMARY KEY, Label TEXT, ThumbnailFilePath TEXT, StoragePath TEXT)",
            "CREATE TABLE IF NOT EXISTS IndependentMedia (IndependentMediaId INTEGER PRIMARY KEY, Hash TEXT, FilePath TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemAccuracy (PlaylistItemAccuracyId INTEGER PRIMARY KEY, Description TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemIndependentMediaMap (PlaylistItemId INTEGER REFERENCES PlaylistItem(PlaylistItemId), IndependentMediaId INTEGER REFERENCES IndependentMedia(IndependentMediaId), PRIMARY KEY (PlaylistItemId, IndependentMediaId))",
            "CREATE TABLE IF NOT EXISTS PlaylistItemLocationMap (PlaylistItemId INTEGER REFERENCES PlaylistItem(PlaylistItemId), LocationId INTEGER REFERENCES Location(LocationId), PRIMARY KEY (PlaylistItemId, LocationId))",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarker (PlaylistItemMarkerId INTEGER PRIMARY KEY, PlaylistItemId INTEGER, Label TEXT, StartTime TEXT, Duration TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarkerBibleVerseMap (PlaylistItemMarkerId INTEGER REFERENCES PlaylistItemMarker(PlaylistItemMarkerId), VerseId INTEGER, PRIMARY KEY (PlaylistItemMarkerId, VerseId))",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarkerParagraphMap (PlaylistItemMarkerId INTEGER REFERENCES PlaylistItemMarker(PlaylistItemMarkerId), MepsDocumentId INTEGER, ParagraphIndex INTEGER, MarkerIndexWithinParagraph INTEGER, PRIMARY KEY (PlaylistItemMarkerId, MepsDocumentId, ParagraphIndex, MarkerIndexWithinParagraph))",
            "CREATE TABLE IF NOT EXISTS LastModified (LastModified TEXT)",
            "INSERT INTO LastModified (LastModified) VALUES ('2026-01-29T00:00:00Z')",
        ]
        for stmt in schema:
            cursor.execute(stmt)
        if data_ops:
            for table, rows in data_ops.items():
                if not rows:
                    continue
                cols = ", ".join(rows[0].keys())
                placeholders = ", ".join(["?"] * len(rows[0]))
                for row in rows:
                    cursor.execute(
                        f"INSERT INTO {table} ({cols}) VALUES ({placeholders})",
                        list(row.values()),
                    )
        conn.commit()
        conn.close()

    def run_tests(self):
        print("\n=== Running Automated Tests ===\n")
        import tempfile, shutil

        test_dir = tempfile.mkdtemp(prefix="jwl_test_")

        try:
            db1_path = path.join(test_dir, "db1.db")
            db2_path = path.join(test_dir, "db2.db")
            db3_path = path.join(test_dir, "db3.db")

            # -------------------------------------------------------
            # Test 1: Basic deduplication
            # -------------------------------------------------------
            print("Test 1: Simple Deduplication...")
            self._create_test_db(
                db1_path,
                {
                    "Tag": [{"Type": 1, "Name": "Favorites"}],
                    "Location": [
                        {"LocationId": 1, "KeySymbol": "nwt", "Title": "Psalm 1"}
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Tag": [{"Type": 1, "Name": "Favorites"}],
                    "Location": [
                        {"LocationId": 1, "KeySymbol": "nwt", "Title": "Psalm 2"}
                    ],
                },
            )

            makedirs(self.working_folder, exist_ok=True)
            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            tag_count = conn.execute("SELECT COUNT(*) FROM Tag").fetchone()[0]
            conn.close()
            assert tag_count == 1, f"Expected 1 tag, got {tag_count}"
            print("  ✓ Tag deduplicated")

            # -------------------------------------------------------
            # Test 2: Cross-DB deduplication with different PKs
            # -------------------------------------------------------
            print("\nTest 2: Cross-DB dedup with different PKs/FKs...")
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 1,
                            "KeySymbol": "nwt",
                            "BookNumber": 40,
                            "ChapterNumber": 5,
                            "MepsLanguage": 0,
                        }
                    ],
                    "Note": [
                        {
                            "Guid": "note-xdb",
                            "Title": "Same Note",
                            "Content": "Same Content",
                            "LocationId": 1,
                        }
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    # Same location but with a completely different PK
                    "Location": [
                        {
                            "LocationId": 99,
                            "KeySymbol": "nwt",
                            "BookNumber": 40,
                            "ChapterNumber": 5,
                            "MepsLanguage": 0,
                        }
                    ],
                    # Note references the different PK
                    "Note": [
                        {
                            "Guid": "note-xdb",
                            "Title": "Same Note",
                            "Content": "Same Content",
                            "LocationId": 99,
                        }
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            loc_count = conn.execute("SELECT COUNT(*) FROM Location").fetchone()[0]
            note_count = conn.execute("SELECT COUNT(*) FROM Note").fetchone()[0]
            conn.close()
            assert loc_count == 1, f"Expected 1 Location, got {loc_count}"
            assert note_count == 1, f"Expected 1 Note, got {note_count}"
            print("  ✓ Location and Note deduplicated across different source PKs")

            # -------------------------------------------------------
            # Test 3: Note 3-way merge
            # -------------------------------------------------------
            print("\nTest 3: Note 3-way Merge...")
            original_ask_select = self._ask_select
            self._ask_select = lambda message, choices, default=None: (
                "m" if message == "Conflict in Note:" else (default or 1)
            )
            self._create_test_db(
                db1_path,
                {
                    "Location": [{"LocationId": 10, "Title": "Note Loc"}],
                    "Note": [
                        {
                            "Guid": "note-123",
                            "Title": "Base Title",
                            "Content": "Base Content",
                            "LocationId": 10,
                        }
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [{"LocationId": 10, "Title": "Note Loc"}],
                    "Note": [
                        {
                            "Guid": "note-123",
                            "Title": "User A Title",
                            "Content": "Base Content",
                            "LocationId": 10,
                        }
                    ],
                },
            )
            self._create_test_db(
                db3_path,
                {
                    "Location": [{"LocationId": 10, "Title": "Note Loc"}],
                    "Note": [
                        {
                            "Guid": "note-123",
                            "Title": "Base Title",
                            "Content": "User B Content",
                            "LocationId": 10,
                        }
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path, db3_path])

            conn = sqlite3.connect(self.merged_db_path)
            res = conn.execute(
                "SELECT Title, Content FROM Note WHERE Guid = 'note-123'"
            ).fetchone()
            conn.close()
            assert res[0] == "User A Title", f"Expected 'User A Title', got '{res[0]}'"
            assert res[1] == "User B Content", (
                f"Expected 'User B Content', got '{res[1]}'"
            )
            self._ask_select = original_ask_select
            print("  ✓ Note 3-way merge successful")

            # -------------------------------------------------------
            # Test 4: UserMark identical signature merge
            # -------------------------------------------------------
            print("\nTest 4: UserMark Overlap (identical signature)...")
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {"LocationId": 20, "DocumentId": 123, "MepsLanguage": 0}
                    ],
                    "UserMark": [
                        {
                            "UserMarkId": 100,
                            "ColorIndex": 1,
                            "LocationId": 20,
                            "UserMarkGuid": "um-1",
                        }
                    ],
                    "BlockRange": [
                        {
                            "BlockType": 1,
                            "Identifier": 1,
                            "StartToken": 0,
                            "EndToken": 10,
                            "UserMarkId": 100,
                        }
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [
                        {"LocationId": 20, "DocumentId": 123, "MepsLanguage": 0}
                    ],
                    "UserMark": [
                        {
                            "UserMarkId": 200,
                            "ColorIndex": 1,
                            "LocationId": 20,
                            "UserMarkGuid": "um-2",
                        }
                    ],
                    "BlockRange": [
                        {
                            "BlockType": 1,
                            "Identifier": 1,
                            "StartToken": 0,
                            "EndToken": 10,
                            "UserMarkId": 200,
                        }
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            um_count = conn.execute("SELECT COUNT(*) FROM UserMark").fetchone()[0]
            br_count = conn.execute("SELECT COUNT(*) FROM BlockRange").fetchone()[0]
            conn.close()
            assert um_count == 1, f"Expected 1 UserMark, got {um_count}"
            assert br_count == 1, f"Expected 1 BlockRange, got {br_count}"
            print("  ✓ UserMark identical signature merged (no duplicate BlockRange)")

            # -------------------------------------------------------
            # Test 5: Sequential PKs in merged output
            # -------------------------------------------------------
            print("\nTest 5: Sequential PKs...")
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 5,
                            "KeySymbol": "w",
                            "BookNumber": None,
                            "Title": "Watchtower A",
                        },
                        {
                            "LocationId": 10,
                            "KeySymbol": "g",
                            "BookNumber": None,
                            "Title": "Awake A",
                        },
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [
                        {
                            "LocationId": 3,
                            "KeySymbol": "w",
                            "BookNumber": None,
                            "Title": "Watchtower A",
                        },  # dup
                        {
                            "LocationId": 8,
                            "KeySymbol": "nwt",
                            "BookNumber": 1,
                            "Title": "Genesis",
                        },  # new
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            pks = [
                r[0]
                for r in conn.execute(
                    "SELECT LocationId FROM Location ORDER BY LocationId"
                ).fetchall()
            ]
            conn.close()
            # Should be 3 rows (2 from db1 + 1 new from db2), sequential from 1
            assert pks == list(range(1, len(pks) + 1)), f"PKs not sequential: {pks}"
            assert len(pks) == 3, f"Expected 3 locations, got {len(pks)}"
            print(f"  ✓ Sequential PKs: {pks}")

            # -------------------------------------------------------
            # Test 6: Composite PK table deduplication with different parent FKs
            # -------------------------------------------------------
            print("\nTest 6: Composite PK table dedup (PlaylistItemLocationMap)...")
            # DB1: PlaylistItem pk=1 linked to Location pk=10
            # DB2: Same PlaylistItem (same label) and same Location (same identity),
            #      but stored under completely different source PKs (pk=99 and pk=77).
            # After merge: only one PlaylistItem, one Location, one map row.
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 10,
                            "KeySymbol": "nwt",
                            "BookNumber": 40,
                            "ChapterNumber": 1,
                            "MepsLanguage": 0,
                            "Title": "Matthew 1",
                        }
                    ],
                    "PlaylistItem": [
                        {
                            "PlaylistItemId": 1,
                            "Label": "My Playlist",
                            "ThumbnailFilePath": None,
                            "StoragePath": None,
                        }
                    ],
                    "PlaylistItemLocationMap": [
                        {"PlaylistItemId": 1, "LocationId": 10}
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [
                        {
                            "LocationId": 77,
                            "KeySymbol": "nwt",
                            "BookNumber": 40,
                            "ChapterNumber": 1,
                            "MepsLanguage": 0,
                            "Title": "Matthew 1",
                        }
                    ],
                    "PlaylistItem": [
                        {
                            "PlaylistItemId": 99,
                            "Label": "My Playlist",
                            "ThumbnailFilePath": None,
                            "StoragePath": None,
                        }
                    ],
                    "PlaylistItemLocationMap": [
                        {"PlaylistItemId": 99, "LocationId": 77}
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            loc_count = conn.execute("SELECT COUNT(*) FROM Location").fetchone()[0]
            pi_count = conn.execute("SELECT COUNT(*) FROM PlaylistItem").fetchone()[0]
            map_count = conn.execute(
                "SELECT COUNT(*) FROM PlaylistItemLocationMap"
            ).fetchone()[0]
            map_row = conn.execute(
                "SELECT PlaylistItemId, LocationId FROM PlaylistItemLocationMap"
            ).fetchone()
            pi_pk = conn.execute("SELECT PlaylistItemId FROM PlaylistItem").fetchone()[
                0
            ]
            loc_pk = conn.execute("SELECT LocationId FROM Location").fetchone()[0]
            conn.close()
            assert loc_count == 1, f"Expected 1 Location, got {loc_count}"
            assert pi_count == 1, f"Expected 1 PlaylistItem, got {pi_count}"
            assert map_count == 1, f"Expected 1 map row, got {map_count}"
            assert map_row == (pi_pk, loc_pk), (
                f"Map row PKs {map_row} don't match merged PKs ({pi_pk}, {loc_pk})"
            )
            print(
                f"  ✓ Composite PK map row correctly deduped and FK-remapped to ({pi_pk}, {loc_pk})"
            )

            # -------------------------------------------------------
            # Test 7: InputField composite PK dedup (LocationId INTEGER + TextTag TEXT)
            # -------------------------------------------------------
            print("\nTest 7: InputField composite PK dedup...")
            # Same location, same TextTag in both DBs but under different LocationId PKs
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 1,
                            "KeySymbol": "mwb",
                            "DocumentId": 501,
                            "MepsLanguage": 0,
                        }
                    ],
                    "InputField": [
                        {"LocationId": 1, "TextTag": "field_1", "Value": "answer A"}
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [
                        {
                            "LocationId": 55,
                            "KeySymbol": "mwb",
                            "DocumentId": 501,
                            "MepsLanguage": 0,
                        }
                    ],
                    "InputField": [
                        {"LocationId": 55, "TextTag": "field_1", "Value": "answer A"}
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            if_count = conn.execute("SELECT COUNT(*) FROM InputField").fetchone()[0]
            if_row = conn.execute(
                "SELECT LocationId, TextTag, Value FROM InputField"
            ).fetchone()
            merged_loc_pk = conn.execute("SELECT LocationId FROM Location").fetchone()[
                0
            ]
            conn.close()
            assert if_count == 1, f"Expected 1 InputField, got {if_count}"
            assert if_row[0] == merged_loc_pk, (
                f"InputField.LocationId {if_row[0]} should match merged Location pk {merged_loc_pk}"
            )
            assert if_row[1] == "field_1", f"Wrong TextTag: {if_row[1]}"
            print(
                f"  ✓ InputField composite PK deduped, LocationId remapped to {merged_loc_pk}"
            )

            # -------------------------------------------------------
            # Test 8: Ignored KeySymbol skips highlight merge
            # -------------------------------------------------------
            print("\nTest 8: Ignored KeySymbol skips highlights...")
            self.ignored_keysymbols = {"w"}

            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 1,
                            "KeySymbol": "w",
                            "DocumentId": 200,
                            "MepsLanguage": 0,
                        }
                    ],
                    "UserMark": [
                        {
                            "UserMarkId": 1,
                            "ColorIndex": 1,
                            "LocationId": 1,
                            "UserMarkGuid": "um-ignore-1",
                        }
                    ],
                    "BlockRange": [
                        {
                            "BlockType": 1,
                            "Identifier": 1,
                            "StartToken": 0,
                            "EndToken": 5,
                            "UserMarkId": 1,
                        }
                    ],
                },
            )
            self._create_test_db(
                db2_path,
                {
                    "Location": [
                        {
                            "LocationId": 1,
                            "KeySymbol": "w",
                            "DocumentId": 200,
                            "MepsLanguage": 0,
                        }
                    ],
                    "UserMark": [
                        {
                            "UserMarkId": 1,
                            "ColorIndex": 2,
                            "LocationId": 1,
                            "UserMarkGuid": "um-ignore-2",
                        }
                    ],
                    "BlockRange": [
                        {
                            "BlockType": 1,
                            "Identifier": 1,
                            "StartToken": 0,
                            "EndToken": 5,
                            "UserMarkId": 1,
                        }
                    ],
                },
            )

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            um_count = conn.execute("SELECT COUNT(*) FROM UserMark").fetchone()[0]
            conn.close()
            assert um_count == 0, f"Expected 0 UserMarks (ignored), got {um_count}"
            print("  ✓ Highlights for ignored KeySymbol 'w' were skipped")

            self.ignored_keysymbols = set()

            # -------------------------------------------------------
            # Test 9: UserMark same rendered text should autoresolve
            # -------------------------------------------------------
            print("\nTest 9: UserMark identical rendered text autoresolves...")
            self._create_test_db(
                db1_path,
                {
                    "Location": [
                        {
                            "LocationId": 1,
                            "KeySymbol": "w",
                            "DocumentId": 20170800,
                            "MepsLanguage": 0,
                        }
                    ]
                },
            )

            conn = sqlite3.connect(db1_path)
            cur = conn.cursor()
            self.color_preference = [4, 2, 1, 3, 5, 6]

            sig_groups = {
                (4, ((1, 1, 0, 5),)): [
                    {
                        "source": "incoming",
                        "source_path": "incoming-red.db",
                    }
                ],
                (2, ((1, 1, 1, 6),)): [
                    {
                        "source": "incoming",
                        "source_path": "incoming-green.db",
                    }
                ],
            }

            original_get_text = self.get_highlighted_text

            def fake_get_text(*_args, **_kwargs):
                return "He showed great patience in putting up with the weaknesses of his followers"

            self.get_highlighted_text = fake_get_text
            try:
                chosen = self._resolve_usermark_conflict(1, sig_groups, cur)
            finally:
                self.get_highlighted_text = original_get_text
            conn.close()

            assert chosen["color"] == 4, (
                f"Expected red highlight from preference order, got {chosen}"
            )
            print(
                "  ✓ Identical rendered highlight text now autoresolves using configured color priority"
            )

            # -------------------------------------------------------
            # Test 10: Container highlight can be folded into chosen child variant
            # -------------------------------------------------------
            print("\nTest 10: Containment fold chooses target contained variant...")
            conn = sqlite3.connect(db1_path)
            cur = conn.cursor()
            sig_groups = {
                (2, ((1, 1, 0, 12),)): [
                    {
                        "source": "incoming",
                        "source_path": "parent-green.db",
                    }
                ],
                (2, ((1, 1, 0, 3),)): [
                    {
                        "source": "current",
                        "source_path": "child-green.db",
                    }
                ],
                (4, ((1, 1, 4, 7),)): [
                    {
                        "source": "incoming",
                        "source_path": "child-red.db",
                    }
                ],
            }

            original_ask_select = self._ask_select

            def ask_select_containment(message, choices, default=None):
                if message == "Container highlight detected — choose contained target:":
                    for c in choices:
                        if "red" in c["name"]:
                            return c["value"]
                return default

            self._ask_select = ask_select_containment
            original_get_text = self.get_highlighted_text
            self.get_highlighted_text = lambda *_args, **_kwargs: (
                "synthetic containment text"
            )
            try:
                chosen = self._resolve_usermark_conflict(1, sig_groups, cur)
            finally:
                self.get_highlighted_text = original_get_text
                self._ask_select = original_ask_select

            assert chosen["color"] == 4, (
                f"Expected red child highlight to be chosen, got {chosen}"
            )
            assert chosen["ranges"] == [(1, 1, 4, 7)], (
                f"Expected fold target child range [(1,1,4,7)], got {chosen['ranges']}"
            )
            print(
                "  ✓ Container highlight fold now allows choosing the contained target variant"
            )
            conn.close()

            print("\n=== All Tests Passed! ===\n")

        finally:

            def secure_delete(p, is_dir=False):
                import time

                for _ in range(5):
                    try:
                        (shutil.rmtree if is_dir else remove)(p) if path.exists(
                            p
                        ) else None
                        return
                    except PermissionError:
                        time.sleep(0.1)
                    except Exception:
                        break

            secure_delete(test_dir, True)
            secure_delete(self.merged_db_path)
            secure_delete(self.working_folder, True)


if __name__ == "__main__":
    processor = JwlBackupProcessor()
    if args.test:
        processor.run_tests()
    else:
        selected_paths = processor.get_jwl_files()
        if selected_paths:
            processor.process_databases(selected_paths)
            processor.create_jwl_file()
        else:
            print("No JWL files selected for merge.")
