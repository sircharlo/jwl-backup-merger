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
from html.parser import HTMLParser
import re
from urllib.parse import urlparse

from langs import LANGUAGES


parser = ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
parser.add_argument("--folder", type=str, help="Folder containing JWL files to merge")
parser.add_argument("--file", type=str, help="JWL file to merge", action="append")
args = parser.parse_args()


class PExtractor(HTMLParser):
    def __init__(self, pid=None):
        super().__init__()
        self.pid = str(pid) if pid is not None else None
        self.found = pid is None  # Always found if no pid requested
        self.in_parNum = False
        self.in_verseNum = False
        self.in_chapterNum = False
        self.text = ""

    def handle_starttag(self, tag, attrs):
        d = dict(attrs)
        if tag == "p" and self.pid is not None:
            # data-pid matches Identifier
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
        self.doc_cache = {}
        self.bible_api_cache = {}  # {lang_code: bible_data_api_path}
        self.conflict_cache = {
            "UserMark": {},  # {conflict_key: chosen_signature}
            "Note": {},  # {conflict_key: choice}
            "Bookmark": {},  # {conflict_key: choice}
            "InputField": {},  # {conflict_key: choice}
        }

    def get_table_info(self, db):
        """Get table info from database

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
        """Process databases

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
            "PlaylistItemMarkerParagraphMap",
        ]

        # Deduplication Identity Keys
        identity_keys = {
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

        for file_path in tqdm(database_files, desc="Merging databases"):
            source_conn = sqlite3.connect(file_path)
            source_cursor = source_conn.cursor()
            skipped_pks = {}  # {table: set(old_pk)}
            self.pk_map = {}  # Clear for each file to avoid old PK collisions!

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
                table_automerged = 0

                # Pre-scan (non-UserMark tables)
                if table_target in ["Bookmark", "InputField", "Note"]:
                    for row in rows:
                        # Temporary dict to check identity
                        temp_row = dict(zip(cols_source, row))
                        temp_dict = {}
                        for ct in cols_target:
                            cs = next(
                                (k for k in temp_row if k.lower() == ct.lower()), None
                            )
                            temp_dict[ct] = temp_row[cs] if cs else None

                        # Remap FKs for identity check
                        table_lower = table.lower()
                        if table_lower in self.fk_map:
                            for c_name, val in temp_dict.items():
                                c_lower = c_name.lower()
                                if c_lower in self.fk_map[table_lower]:
                                    t_table, t_col = self.fk_map[table_lower][c_lower]
                                    t_canonical = self.table_name_map.get(
                                        t_table.lower(), t_table
                                    )
                                    if val in self.pk_map.get(t_canonical, {}):
                                        temp_dict[c_name] = self.pk_map[t_canonical][
                                            val
                                        ]

                        # Check identity
                        id_cols = identity_keys.get(table_target)
                        if id_cols:
                            query = (
                                f"SELECT {self.primary_keys[table][0]} FROM [{table}] WHERE "
                                + " AND ".join([f"[{k}] IS ?" for k in id_cols])
                            )
                            merged_cursor.execute(
                                query, [temp_dict.get(k) for k in id_cols]
                            )
                            res = merged_cursor.fetchone()
                            if res:
                                # Conflict check
                                merged_cursor.execute(
                                    f"SELECT * FROM [{table}] WHERE {self.primary_keys[table][0]} = ?",
                                    (res[0],),
                                )
                                curr = dict(zip(cols_target, merged_cursor.fetchone()))
                                is_diff = False
                                for c in temp_dict:
                                    if c in self.primary_keys[table]:
                                        continue
                                    if table_target == "Note" and c in [
                                        "Title",
                                        "Content",
                                    ]:
                                        if (temp_dict[c] or "") != (curr.get(c) or ""):
                                            is_diff = True
                                            break
                                    elif temp_dict[c] != curr.get(c):
                                        is_diff = True
                                        break

                                if is_diff:
                                    table_conflicts += 1

                table_conflict_index = 0
                automerge_stats_shown = False

                # Special handling for UserMark: process location by location
                if table_target == "UserMark":
                    # Group incoming UserMarks by LocationId
                    loc_to_usermarks = {}
                    for row in rows:
                        row_dict_source = dict(zip(cols_source, row))
                        loc_id = row_dict_source.get("LocationId")
                        if loc_id not in loc_to_usermarks:
                            loc_to_usermarks[loc_id] = []
                        loc_to_usermarks[loc_id].append(row_dict_source)

                    for loc_id, incoming_rows in loc_to_usermarks.items():
                        # We need to simulate the grouping to get counts
                        # 1. Get existing
                        merged_cursor.execute(
                            "SELECT UserMarkId, ColorIndex FROM UserMark WHERE LocationId = ?",
                            (loc_id,),
                        )
                        existing_usermarks = merged_cursor.fetchall()
                        all_highlights = []
                        for um_id, color in existing_usermarks:
                            merged_cursor.execute(
                                "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                                (um_id,),
                            )
                            ranges = sorted(merged_cursor.fetchall())
                            all_highlights.append(
                                {"color": color, "ranges": ranges, "source": "current"}
                            )
                        # 2. Add incoming
                        for row_dict_source in incoming_rows:
                            old_pk = row_dict_source.get(self.primary_keys[table][0])
                            source_cursor.execute(
                                "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                                (old_pk,),
                            )
                            inc_ranges = sorted(source_cursor.fetchall())
                            inc_color = row_dict_source.get("ColorIndex")
                            all_highlights.append(
                                {
                                    "color": inc_color,
                                    "ranges": inc_ranges,
                                    "source": "incoming",
                                }
                            )

                        # 3. Find components
                        num_hl = len(all_highlights)
                        adj = {i: set() for i in range(num_hl)}
                        for i in range(num_hl):
                            for j in range(i + 1, num_hl):
                                h1, h2 = all_highlights[i], all_highlights[j]
                                same_sig = (
                                    h1["color"] == h2["color"]
                                    and h1["ranges"] == h2["ranges"]
                                )
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
                        for i in range(num_hl):
                            if i not in visited:
                                comp = []
                                stack = [i]
                                visited.add(i)
                                sigs = set()
                                has_current = False
                                while stack:
                                    curr = stack.pop()
                                    hl = all_highlights[curr]
                                    sigs.add((hl["color"], tuple(hl["ranges"])))
                                    if hl["source"] == "current":
                                        has_current = True
                                    for neighbor in adj[curr]:
                                        if neighbor not in visited:
                                            visited.add(neighbor)
                                            stack.append(neighbor)
                                if len(sigs) > 1:
                                    table_conflicts += 1
                                elif len(all_highlights) > 1 and has_current:
                                    # This logic is a bit simplified but good enough for counting automerge
                                    # (multiple highlights in component but all same signature)
                                    # Wait, if sigs is 1 but we have multiple highlights, it's automerge
                                    # IF there's at least one current to merge into.
                                    table_automerged += 1

                    # Sort locations (optional, but keep it ordered like before if possible)
                    source_cursor.execute("SELECT LocationId, KeySymbol FROM Location")
                    loc_symbol_map = {
                        r[0]: (r[1] or "") for r in source_cursor.fetchall()
                    }
                    sorted_loc_ids = sorted(
                        loc_to_usermarks.keys(),
                        key=lambda lid: loc_symbol_map.get(lid, ""),
                    )

                    for loc_id in sorted_loc_ids:
                        incoming_rows = loc_to_usermarks[loc_id]

                        # Get all existing highlights at this location in merged DB
                        merged_cursor.execute(
                            "SELECT UserMarkId, ColorIndex FROM UserMark WHERE LocationId = ?",
                            (loc_id,),
                        )
                        existing_usermarks = merged_cursor.fetchall()
                        all_highlights = []

                        # Add existing highlights
                        for um_id, color in existing_usermarks:
                            merged_cursor.execute(
                                "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                                (um_id,),
                            )
                            ranges = sorted(merged_cursor.fetchall())
                            all_highlights.append(
                                {
                                    "usermark_id": um_id,
                                    "color": color,
                                    "ranges": ranges,
                                    "source": "current",
                                }
                            )

                        # Add all incoming highlights for this location
                        for row_dict_source in incoming_rows:
                            # Map source row to target schema
                            row_dict = {}
                            source_cols_lower = {
                                k.lower(): k for k in row_dict_source.keys()
                            }
                            for col_target in cols_target:
                                col_source = source_cols_lower.get(col_target.lower())
                                row_dict[col_target] = (
                                    row_dict_source[col_source] if col_source else None
                                )

                            old_pk = row_dict_source.get(self.primary_keys[table][0])

                            # Fetch incoming ranges
                            source_cursor.execute(
                                "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                                (old_pk,),
                            )
                            inc_ranges = sorted(source_cursor.fetchall())
                            inc_color = row_dict.get("ColorIndex")

                            all_highlights.append(
                                {
                                    "usermark_id": old_pk,
                                    "color": inc_color,
                                    "ranges": inc_ranges,
                                    "source": "incoming",
                                    "row_dict": row_dict,
                                }
                            )

                        # Group by actual overlap or identical signature within this location
                        # Two highlights have an edge if they overlap OR have same signature
                        num_hl = len(all_highlights)
                        adj = {i: set() for i in range(num_hl)}
                        for i in range(num_hl):
                            for j in range(i + 1, num_hl):
                                h1, h2 = all_highlights[i], all_highlights[j]
                                # Check identical signature
                                same_sig = (
                                    h1["color"] == h2["color"]
                                    and h1["ranges"] == h2["ranges"]
                                )
                                # Check overlap
                                overlap = False
                                if not same_sig:
                                    for r1 in h1["ranges"]:
                                        for r2 in h2["ranges"]:
                                            # BlockType, Identifier match
                                            if r1[0] == r2[0] and r1[1] == r2[1]:
                                                # Token overlap
                                                if r1[2] < r2[3] and r2[2] < r1[3]:
                                                    overlap = True
                                                    break
                                        if overlap:
                                            break
                                if same_sig or overlap:
                                    adj[i].add(j)
                                    adj[j].add(i)

                        # Find connected components
                        visited = set()
                        hl_components = []
                        for i in range(num_hl):
                            if i not in visited:
                                comp = []
                                stack = [i]
                                visited.add(i)
                                while stack:
                                    curr = stack.pop()
                                    comp.append(all_highlights[curr])
                                    for neighbor in adj[curr]:
                                        if neighbor not in visited:
                                            visited.add(neighbor)
                                            stack.append(neighbor)
                                hl_components.append(comp)

                        for comp_highlights in hl_components:
                            # Group by unique signature (color + ranges) within this component
                            signature_groups = {}  # {(color, tuple(ranges)): [highlight_dicts]}
                            for hl in comp_highlights:
                                sig = (hl["color"], tuple(hl["ranges"]))
                                if sig not in signature_groups:
                                    signature_groups[sig] = []
                                signature_groups[sig].append(hl)

                            # Check if we need user input
                            needs_user_input = len(signature_groups) > 1

                            if needs_user_input:
                                # Show automerge statistics once
                                if not automerge_stats_shown and table_automerged > 0:
                                    print(
                                        f"\n  Automerged {table_automerged} identical highlight(s)"
                                    )
                                    print(
                                        f"  {table_conflicts} conflict(s) require your input\n"
                                    )
                                    automerge_stats_shown = True

                                table_conflict_index += 1
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(
                                    f"\nConflict {table_conflict_index}/{table_conflicts} in Highlight at {loc_info}:"
                                )
                                print(
                                    f"  Found {len(comp_highlights)} highlight(s) with {len(signature_groups)} unique variant(s)"
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

                                # Fetch text context info
                                doc_id, lang, keysym, book, chapter = (
                                    None,
                                    None,
                                    None,
                                    None,
                                    None,
                                )
                                try:
                                    merged_cursor.execute(
                                        "SELECT DocumentId, MepsLanguage, KeySymbol, BookNumber, ChapterNumber FROM Location WHERE LocationId = ?",
                                        (loc_id,),
                                    )
                                    loc_res = merged_cursor.fetchone()
                                    if loc_res:
                                        doc_id, lang, keysym, book, chapter = loc_res
                                        print("  Fetching text context from JW.org...")
                                except Exception as e:
                                    print(f"Error fetching text context: {e}")
                                    pass

                                # Display options
                                options = []
                                for idx, (sig, group) in enumerate(
                                    signature_groups.items(), 1
                                ):
                                    color, ranges = sig
                                    sources = []
                                    for hl in group:
                                        if hl["source"] not in sources:
                                            sources.append(hl["source"])

                                    color_name = color_names.get(
                                        color, f"color_{color}"
                                    )
                                    color_code = color_codes.get(color, "")

                                    print(
                                        f"\n  Option {idx}: {color_code}{color_name}{RESET} ({len(group)} instance(s): {', '.join(sources)})"
                                    )

                                    # Fetch text
                                    text = None
                                    if doc_id or (keysym and book and chapter):
                                        try:
                                            full_text = []
                                            for r in ranges:
                                                txt = self.get_highlighted_text(
                                                    doc_id,
                                                    r[1],
                                                    r[2],
                                                    r[3],
                                                    lang,
                                                    keysym,
                                                    book,
                                                    chapter,
                                                )
                                                if txt is None:
                                                    text = None
                                                    break
                                                full_text.append(txt)
                                            if full_text and None not in full_text:
                                                text = " [...] ".join(full_text)
                                        except Exception as e:
                                            print(f"Error fetching text: {e}")
                                            text = None

                                    if text:
                                        print(f"    Text: {color_code}'{text}'{RESET}")
                                    else:
                                        print("    (Text unavailable)")
                                        print(f"    Ranges: {list(ranges)}")

                                    options.append(
                                        {
                                            "color": color,
                                            "ranges": ranges,
                                            "highlights": group,
                                        }
                                    )

                                conflict_key = (
                                    (doc_id, lang, keysym, book, chapter),
                                    tuple(sorted(signature_groups.keys())),
                                )
                                chosen_option = None
                                if conflict_key in self.conflict_cache["UserMark"]:
                                    chosen_sig = self.conflict_cache["UserMark"][
                                        conflict_key
                                    ]
                                    chosen_option = next(
                                        (
                                            o
                                            for o in options
                                            if (o["color"], tuple(o["ranges"]))
                                            == chosen_sig
                                        ),
                                        None,
                                    )
                                    if chosen_option:
                                        print(
                                            f"  (Using previously resolved choice: Option {options.index(chosen_option) + 1})"
                                        )

                                if not chosen_option:
                                    choice_idx = None
                                    while choice_idx is None:
                                        try:
                                            choice_str = input(
                                                f"\n  Choose option (1-{len(options)}): "
                                            ).strip()
                                            choice_idx = int(choice_str)
                                            if choice_idx < 1 or choice_idx > len(
                                                options
                                            ):
                                                choice_idx = None
                                        except ValueError:
                                            pass

                                    chosen_option = options[choice_idx - 1]
                                    self.conflict_cache["UserMark"][conflict_key] = (
                                        chosen_option["color"],
                                        tuple(chosen_option["ranges"]),
                                    )
                            else:
                                # Auto-merge or single variant
                                if len(comp_highlights) > 1 and any(
                                    h["source"] == "current" for h in comp_highlights
                                ):
                                    table_automerged += 1
                                chosen_hl_proto = list(signature_groups.values())[0][0]
                                chosen_option = {
                                    "color": chosen_hl_proto["color"],
                                    "ranges": chosen_hl_proto["ranges"],
                                    "highlights": list(signature_groups.values())[0],
                                }

                            # Apply the chosen option
                            # 1. Choose a lead UserMarkId from the chosen group
                            lead_usermark_id = None
                            # Prefer existing highlight if it's in the chosen group
                            for hl in chosen_option["highlights"]:
                                if hl["source"] == "current":
                                    lead_usermark_id = hl["usermark_id"]
                                    break
                            if not lead_usermark_id:
                                # If no existing highlight matches, we'll need to create/keep one incoming
                                lead_usermark_id = chosen_option["highlights"][0][
                                    "usermark_id"
                                ]

                            # 2. Remap ALL highlights in this component to the lead_usermark_id in our map
                            for hl in comp_highlights:
                                if hl["source"] == "incoming":
                                    self.pk_map[table][hl["usermark_id"]] = (
                                        lead_usermark_id
                                    )

                            # 3. Handle Merged DB cleanup and update
                            # Remove all existing UserMarks in this COMPONENT that were NOT chosen
                            comp_existing_ids = [
                                hl["usermark_id"]
                                for hl in comp_highlights
                                if hl["source"] == "current"
                            ]
                            for um_id in comp_existing_ids:
                                if um_id != lead_usermark_id:
                                    # Remap references in Note table
                                    merged_cursor.execute(
                                        "UPDATE Note SET UserMarkId = ? WHERE UserMarkId = ?",
                                        (lead_usermark_id, um_id),
                                    )
                                    # Delete BlockRanges
                                    merged_cursor.execute(
                                        "DELETE FROM BlockRange WHERE UserMarkId = ?",
                                        (um_id,),
                                    )
                                    # Delete UserMark
                                    merged_cursor.execute(
                                        "DELETE FROM UserMark WHERE UserMarkId = ?",
                                        (um_id,),
                                    )

                            # 4. If lead is incoming, we need to insert it (if not already there)
                            if lead_usermark_id not in comp_existing_ids:
                                # Insert the chosen incoming highlight
                                chosen_hl = next(
                                    hl
                                    for hl in chosen_option["highlights"]
                                    if hl["usermark_id"] == lead_usermark_id
                                )
                                row_dict = chosen_hl["row_dict"]

                                # Clean PK
                                insert_dict = row_dict.copy()
                                pk_name = self.primary_keys[table][0]
                                if isinstance(insert_dict.get(pk_name), int):
                                    del insert_dict[pk_name]

                                columns_str = ", ".join(
                                    [f"[{k}]" for k in insert_dict.keys()]
                                )
                                placeholders = ", ".join(["?"] * len(insert_dict))
                                merged_cursor.execute(
                                    f"INSERT INTO [{table}] ({columns_str}) VALUES ({placeholders})",
                                    list(insert_dict.values()),
                                )
                                new_pk = merged_cursor.lastrowid
                                # Re-map all that were pointing to the temporary old_pk in this component
                                for hl in comp_highlights:
                                    if (
                                        hl["source"] == "incoming"
                                        and self.pk_map[table][hl["usermark_id"]]
                                        == lead_usermark_id
                                    ):
                                        self.pk_map[table][hl["usermark_id"]] = new_pk

                                lead_usermark_id = new_pk

                                # Insert ranges for the new lead
                                source_cursor.execute(
                                    "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                                    (chosen_hl["usermark_id"],),
                                )
                                for br in source_cursor.fetchall():
                                    merged_cursor.execute(
                                        "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                                        list(br) + [lead_usermark_id],
                                    )
                            else:
                                # Lead is already in DB, just ensure its color matches (in case we chose an incoming variant color)
                                merged_cursor.execute(
                                    "UPDATE UserMark SET ColorIndex = ? WHERE UserMarkId = ?",
                                    (chosen_option["color"], lead_usermark_id),
                                )
                                # And ensure ranges match (delete and re-insert for simplicity)
                                merged_cursor.execute(
                                    "DELETE FROM BlockRange WHERE UserMarkId = ?",
                                    (lead_usermark_id,),
                                )
                                # Get ranges from the chosen variant
                                ranges = chosen_option["ranges"]
                                for r in ranges:
                                    merged_cursor.execute(
                                        "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                                        list(r) + [lead_usermark_id],
                                    )

                            # Skip individual inserts for BlockRange for these incoming UserMarks in this component
                            if "BlockRange" not in skipped_pks:
                                skipped_pks["BlockRange"] = set()
                            for hl in comp_highlights:
                                if hl["source"] == "incoming":
                                    source_cursor.execute(
                                        "SELECT BlockRangeId FROM BlockRange WHERE UserMarkId = ?",
                                        (hl["usermark_id"],),
                                    )
                                    for (br_id,) in source_cursor.fetchall():
                                        skipped_pks["BlockRange"].add(br_id)

                        continue  # Done with UserMark table for this file loc_id

                    continue  # Done with UserMark table for this file

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
                                    row_dict[col_name] = self.pk_map[
                                        to_table_canonical
                                    ][val]

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
                        if table_target in ["Bookmark", "InputField"]:
                            # Get existing data
                            merged_cursor.execute(
                                f"SELECT * FROM [{table}] WHERE {self.primary_keys[table][0]} = ?",
                                (existing_new_pk,),
                            )
                            current_row = dict(
                                zip(cols_target, merged_cursor.fetchone())
                            )

                            # Compare relevant fields
                            diffs = {}
                            for col in row_dict:
                                if col in self.primary_keys[table]:
                                    continue
                                if row_dict[col] != current_row.get(col):
                                    diffs[col] = (current_row.get(col), row_dict[col])

                            if diffs:
                                table_conflict_index += 1
                                # Fetch context for the user
                                loc_id = current_row.get("LocationId")
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(
                                    f"\nConflict {table_conflict_index}/{table_conflicts} in {table_target} at {loc_info}:"
                                )
                                for col, (old_val, new_val) in diffs.items():
                                    print(
                                        f"  {col}: current='{old_val}' vs incoming='{new_val}'"
                                    )

                                choice = ""
                                options = ["c", "i"]
                                if table_target == "InputField":
                                    options.append("m")
                                    merged_val = self.merge_text(
                                        None,
                                        current_row.get("Value"),
                                        row_dict.get("Value"),
                                    )
                                    print(f"  Merged value: '{merged_val}'")

                                prompt = "Keep (c)urrent, (i)ncoming?"
                                if "m" in options:
                                    prompt = "Keep (c)urrent, (i)ncoming, or (m)erged?"

                                # Caching logic
                                # Get canonical location info
                                merged_cursor.execute(
                                    "SELECT DocumentId, MepsLanguage, KeySymbol, BookNumber, ChapterNumber FROM Location WHERE LocationId = ?",
                                    (loc_id,),
                                )
                                loc_res = merged_cursor.fetchone()
                                # Identity field
                                id_field = (
                                    "Slot" if table_target == "Bookmark" else "TextTag"
                                )
                                id_val = current_row.get(id_field)

                                conflict_key = (
                                    table_target,
                                    loc_res,
                                    id_val,
                                    tuple(sorted(diffs.items())),
                                )

                                choice = self.conflict_cache[table_target].get(
                                    conflict_key, ""
                                )
                                if choice:
                                    print(
                                        f"  (Using previously resolved choice: {choice})"
                                    )
                                else:
                                    while choice not in options:
                                        choice = input(f"{prompt} ").lower()
                                    self.conflict_cache[table_target][conflict_key] = (
                                        choice
                                    )

                                if choice == "i":
                                    update_cols = ", ".join(
                                        [f"[{k}] = ?" for k in diffs.keys()]
                                    )
                                    merged_cursor.execute(
                                        f"UPDATE [{table}] SET {update_cols} WHERE {self.primary_keys[table][0]} = ?",
                                        list(row_dict[k] for k in diffs.keys())
                                        + [existing_new_pk],
                                    )
                                elif choice == "m" and table_target == "InputField":
                                    merged_cursor.execute(
                                        f"UPDATE [{table}] SET Value = ? WHERE {self.primary_keys[table][0]} = ?",
                                        (merged_val, existing_new_pk),
                                    )

                        elif table_target == "Note":
                            # Perform interactive 3-way merge for notes
                            merged_cursor.execute(
                                f"SELECT Title, Content, LastModified, LocationId FROM [{table}] WHERE {self.primary_keys[table][0]} = ?",
                                (existing_new_pk,),
                            )
                            current_merged = merged_cursor.fetchone()
                            curr_title, curr_content, m_ts, loc_id = current_merged

                            guid = row_dict.get("Guid")
                            base = self.note_bases.get(
                                guid, {"title": curr_title, "content": curr_content}
                            )

                            inc_title = row_dict.get("Title") or ""
                            inc_content = row_dict.get("Content") or ""
                            curr_title = curr_title or ""
                            curr_content = curr_content or ""

                            merged_title = self.merge_text(
                                base.get("title"), curr_title, inc_title
                            )
                            merged_content = self.merge_text(
                                base.get("content"), curr_content, inc_content
                            )

                            if inc_title != curr_title or inc_content != curr_content:
                                table_conflict_index += 1
                                loc_info = self.get_location_info(merged_cursor, loc_id)
                                print(
                                    f"\nConflict {table_conflict_index}/{table_conflicts} in Note at {loc_info} (GUID: {guid}):"
                                )

                                if inc_title != curr_title:
                                    print("\n--- Title Diff (current vs incoming) ---")
                                    self.print_diff(curr_title, inc_title)

                                    print("\n--- Auto-merged title ---")
                                    print(merged_title)

                                if inc_content != curr_content:
                                    print(
                                        "\n--- Content Diff (current vs incoming) ---"
                                    )
                                    self.print_diff(curr_content, inc_content)

                                    print("\n--- Auto-merged content ---")
                                    print(merged_content)

                                print("\nOptions:")
                                print("  [c]urrent")
                                print("  [i]ncoming")
                                print("  [m]erged")

                                # Caching logic
                                # Get canonical location info
                                merged_cursor.execute(
                                    "SELECT DocumentId, MepsLanguage, KeySymbol, BookNumber, ChapterNumber FROM Location WHERE LocationId = ?",
                                    (loc_id,),
                                )
                                loc_res = merged_cursor.fetchone()
                                conflict_key = (
                                    guid,
                                    loc_res,
                                    (curr_title, curr_content),
                                    (inc_title, inc_content),
                                )

                                choice = self.conflict_cache["Note"].get(
                                    conflict_key, ""
                                )
                                if choice:
                                    print(
                                        f"  (Using previously resolved choice: {choice})"
                                    )
                                else:
                                    while choice not in ["c", "i", "m"]:
                                        choice = input(
                                            "\nKeep (c)urrent, (i)ncoming, or (m)erged? "
                                        ).lower()
                                    self.conflict_cache["Note"][conflict_key] = choice

                                final_title, final_content = curr_title, curr_content
                                if choice == "i":
                                    final_title, final_content = inc_title, inc_content
                                elif choice == "m":
                                    final_title, final_content = (
                                        merged_title,
                                        merged_content,
                                    )

                                # Determine latest LastModified
                                s_ts = row_dict.get("LastModified")
                                latest_ts = (
                                    s_ts
                                    if (not m_ts or (s_ts and s_ts > m_ts))
                                    else m_ts
                                )

                                merged_cursor.execute(
                                    f"UPDATE [{table}] SET Title = ?, Content = ?, LastModified = ? WHERE {self.primary_keys[table][0]} = ?",
                                    (
                                        final_title,
                                        final_content,
                                        latest_ts,
                                        existing_new_pk,
                                    ),
                                )

                        if old_pk is not None:
                            self.pk_map[table][old_pk] = existing_new_pk
                    else:
                        # Insert new row
                        insert_dict = row_dict.copy()
                        if table_target == "Note":
                            self.note_bases[row_dict.get("Guid")] = {
                                "title": row_dict.get("Title"),
                                "content": row_dict.get("Content"),
                            }

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
                            if (
                                table_target == "TagMap"
                                and "TagMap.TagId, TagMap.Position" in str(e)
                            ):
                                tag_id = insert_dict.get("TagId")
                                position = insert_dict.get("Position")
                                # Shift existing items forward manually to avoid "ORDER BY" syntax requirements in UPDATE
                                merged_cursor.execute(
                                    f"SELECT TagMapId, Position FROM [{table}] WHERE TagId = ? AND Position >= ? ORDER BY Position DESC",
                                    (tag_id, position),
                                )
                                for tid, pos in merged_cursor.fetchall():
                                    merged_cursor.execute(
                                        f"UPDATE [{table}] SET Position = ? WHERE TagMapId = ?",
                                        (pos + 1, tid),
                                    )
                                # Retry insertion
                                merged_cursor.execute(
                                    insert_query, list(insert_dict.values())
                                )
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
        merged_cursor.execute(
            "UPDATE LastModified SET LastModified = strftime('%Y-%m-%dT%H:%M:%SZ', 'now');"
        )
        merged_conn.commit()

        # Collect files for archive
        try:
            merged_cursor.execute(
                "SELECT FilePath FROM IndependentMedia WHERE FilePath IS NOT NULL"
            )
            self.files_to_include_in_archive.extend(
                [r[0] for r in merged_cursor.fetchall()]
            )
        except Exception as e:
            print(f"Error fetching file paths: {e}")
            pass
        try:
            merged_cursor.execute(
                "SELECT ThumbnailFilePath FROM PlaylistItem WHERE ThumbnailFilePath IS NOT NULL"
            )
            self.files_to_include_in_archive.extend(
                [r[0] for r in merged_cursor.fetchall()]
            )
        except Exception as e:
            print(f"Error fetching thumbnail file paths: {e}")
            pass
        self.files_to_include_in_archive = list(set(self.files_to_include_in_archive))

        merged_conn.close()

        merged_conn.close()

    def createJwlFile(self):
        """Create JWL file from the merged database in the working folder

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
        """Print a colored diff between two strings."""
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
        """Fetch content from JW.org and extract highlighted text based on tokens."""
        # Convert to int for dictionary lookup
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
            print(f"No symbol found for language code: {meps_lang_code}")
            return None

        # Bible logic branch
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
                # Try to discover API path from language home page
                try:
                    home_url = f"https://www.jw.org/{ietf_code}"
                    headers = {
                        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                    }
                    r = requests.get(home_url, headers=headers, timeout=5)
                    r.raise_for_status()

                    # Search for data-bible_data_api in pageConfig
                    # Prioritize specific versions if keysym is available
                    match = None
                    if keysym:
                        # e.g. data-bible_data_api_nwtsty or data-bible_data_api_nwt
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
                # Construct Bible API URL
                # The ID format is [BookNumber*10][ChapterNumber(2)][000]
                # Example: Matthew (40) * 10 = 400. Chapter 10 -> 40010000
                book_id = book * 10
                range_start = f"{book_id}{chapter:02d}000"
                range_id = f"{range_start}-{book_id}{chapter:02d}999"
                url = f"https://www.jw.org{api_path}{range_id}"

                try:
                    data = None
                    if url in self.doc_cache:
                        data = self.doc_cache[url]
                    else:
                        headers = {
                            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                        }
                        r = requests.get(url, headers=headers, timeout=10)
                        r.raise_for_status()
                        data = r.json()

                        self.doc_cache[url] = data

                    if data:
                        # Extract verse text using confirmed pattern: [Book*10][Chapter(2)][Verse(3)]
                        # Example: Matthew 10:1 (Identifier=1) -> 40010001
                        ranges_data = data.get("ranges", {})

                        # Find the correct range object. It key matches range_id.
                        range_content = ranges_data.get(range_id)

                        if not range_content:
                            # Fallback: maybe the first range in the dict?
                            if ranges_data:
                                range_content = list(ranges_data.values())[0]

                        if range_content:
                            verses = range_content.get("verses", [])
                            # Find the specific verse in the list
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

                                # Use PExtractor to strip tags and discard chapter/verse numbers
                                parser = (
                                    PExtractor()
                                )  # No pid means it processes everything
                                parser.feed(content)
                                text = " ".join(parser.text.split())

                                # Tokenize consistently with PExtractor branch
                                tokens = re.findall(
                                    r"\w+(?:['’.:-]\w+)*|[^\s\w" + "\u200b" + r"]", text
                                )
                                subset = tokens[start_token : end_token + 1]
                                return " ".join(subset)
                except Exception as e:
                    if self.debug:
                        print(f"Error fetching Bible text from {url}: {e}")

        if (docid, lang_code) in self.doc_cache:
            html_content = self.doc_cache[(docid, lang_code)]
        else:
            url = f"https://www.jw.org/open?docid={docid}&wtlocale={lang_code}&appLanguage=E&prefer=content"
            try:
                headers = {
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                }

                r = requests.get(url, headers=headers, timeout=5)

                if urlparse(r.url).path.count("/") <= 2:
                    raise Exception(f"Invalid redirect to {r.url}")

                html_content = r.text
                self.doc_cache[(docid, lang_code)] = html_content
            except Exception as e:
                print(f"Error fetching content: {e}")
                return None

        parser = PExtractor(identifier)
        parser.feed(html_content)
        full_text = parser.text

        if not full_text:
            return f"[Text not found for pid={identifier}]"

        # Tokenization Logic corresponding to:
        # "any word, series of chars that starts and ends with alphanumeric...
        # en dash, em dash, special char, etc. are tokens of their own if at end of word"
        # Regex: \w+(?:['’.:-]\w+)* matches words with internal punctuation.
        # [^\s\w] matches single symbols.

        # We look for words OR symbols, ignoring whitespace
        tokens = re.findall(r"\w+(?:['’.:-]\w+)*|[^\s\w" + "\u200b" + r"]", full_text)

        # Extract subset
        if start_token < 0:
            start_token = 0
        if end_token > len(tokens):
            end_token = len(tokens)

        subset = tokens[start_token : end_token + 1]
        return " ".join(subset)

    def check_overlap(self, cursor, location_id, new_ranges, exclude_usermark_id=None):
        """Check if new ranges overlap with existing highlights at the same location."""
        if not location_id or not new_ranges:
            return []

        # Get all UserMarks for this location
        query = "SELECT UserMarkId FROM UserMark WHERE LocationId = ?"
        params = [location_id]
        if exclude_usermark_id:
            query += " AND UserMarkId != ?"
            params.append(exclude_usermark_id)

        cursor.execute(query, params)
        candidate_usermarks = [r[0] for r in cursor.fetchall()]

        conflicting_pks = []

        for um_id in candidate_usermarks:
            # Get ranges for this UserMark
            cursor.execute(
                "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?",
                (um_id,),
            )
            existing_ranges = cursor.fetchall()  # List of tuples

            # Check overlap
            is_overlap = False
            for nr in new_ranges:  # nr is (BlockType, Identifier, StartToken, EndToken)
                for er in existing_ranges:
                    # Check BlockType and Identifier (Pid) match
                    if nr[0] == er[0] and nr[1] == er[1]:
                        # Check Token Overlap: StartA < EndB and StartB < EndA
                        if nr[2] < er[3] and er[2] < nr[3]:
                            is_overlap = True
                            break
                if is_overlap:
                    break

            if is_overlap:
                conflicting_pks.append(um_id)

        return conflicting_pks

    def get_location_info(self, cursor, location_id):
        """Get formatted location info for display"""
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
            info.append(f"{keysym}")
        if issue:
            info.append(f"{issue}")
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
        """Perform a 3-way merge on two strings using a common base."""
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

        # Identify changes in A and B relative to base
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

        # If changes are non-overlapping, apply both
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

        # Overlapping changes: use current conservative logic or concatenate
        # Find common prefix/suffix of all three
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
        else:
            if a_m in b_m:
                merged_m = b_m
            elif b_m in a_m:
                merged_m = a_m
            else:
                sep = "\n" if "\n" in a_m or "\n" in b_m else " "
                merged_m = a_m + sep + b_m

        return prefix + merged_m + suffix

    def cleanTempFiles(self, force=False):
        """Clean up temporary files

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
        """Unzip a file

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
        """Get the first database file in the unzipped folder

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
        """Get the list of JW Library backup files to merge

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
        """Calculate the SHA-256 hash of a file

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
