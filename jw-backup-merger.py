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
import sys
import importlib
import importlib.util
import json

from langs import LANGUAGES


parser = ArgumentParser()
parser.add_argument("--debug", action="store_true", help="Enable debug mode")
parser.add_argument("--folder", type=str, help="Folder containing JWL files to merge")
parser.add_argument("--file", type=str, help="JWL file to merge", action="append")
parser.add_argument("--test", action="store_true", help="Run automated tests")
parser.add_argument(
    "--conflict-policy",
    type=str,
    default="prompt",
    choices=["prompt", "current", "incoming", "merged"],
    help="How to resolve conflicts: prompt, current, incoming, merged",
)
parser.add_argument(
    "--verbose-stats",
    action="store_true",
    help="Print per-table merge statistics for each source DB and the merged result",
)
args = parser.parse_args()

selectBlockRangeSql = "SELECT BlockType, Identifier, StartToken, EndToken FROM BlockRange WHERE UserMarkId = ?"
selectLocationSql = "SELECT DocumentId, MepsLanguage, KeySymbol, BookNumber, ChapterNumber FROM Location WHERE LocationId = ?"
selectLocationPreferenceSql = "SELECT KeySymbol FROM Location WHERE LocationId = ?"


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
        self.user_agent = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
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
        self.conflict_policy = args.conflict_policy
        self.verbose_stats = args.verbose_stats
        self.doc_cache = {}
        self.bible_api_cache = {}  # {lang_code: bible_data_api_path}
        self.conflict_cache = {
            "UserMark": {},  # {conflict_key: chosen_signature}
            "Note": {},  # {conflict_key: choice}
            "Bookmark": {},  # {conflict_key: choice}
            "InputField": {},  # {conflict_key: choice}
        }
        self.highlight_preview_cache = {}  # {(loc_tuple, ranges_tuple): preview_text}
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
        self.table_stats = {}
        self.current_file_label = None
        self.location_preferences = {}
        self.source_file_priorities = {}
        self.color_priority = [4, 3, 2, 1, 5, 6]
        self.note_conflict_variants = {}
        self.config_path = path.expanduser("~/.jw-backup-merger.json")
        self._load_user_config()

    def _load_user_config(self):
        try:
            if not path.exists(self.config_path):
                return
            with open(self.config_path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data.get("location_preferences"), dict):
                self.location_preferences = data["location_preferences"]
            if isinstance(data.get("source_file_priorities"), dict):
                self.source_file_priorities = data["source_file_priorities"]
            colors = data.get("color_priority")
            if isinstance(colors, list) and all(isinstance(c, int) for c in colors):
                self.color_priority = colors
        except Exception:
            pass

    def _save_user_config(self):
        payload = {
            "location_preferences": self.location_preferences,
            "source_file_priorities": self.source_file_priorities,
            "color_priority": self.color_priority,
        }
        try:
            with open(self.config_path, "w", encoding="utf-8") as fh:
                json.dump(payload, fh, indent=2, sort_keys=True)
        except Exception:
            pass


    def _ensure_table_stat(self, table_target):
        if table_target not in self.table_stats:
            self.table_stats[table_target] = {
                "source_counts": {},
                "new_by_file": {},
                "duplicates_by_file": {},
                "identical": 0,
                "dropped": {},
                "merged_count": 0,
            }
        return self.table_stats[table_target]

    def _inc_stat(self, table_target, key, subkey=None, amount=1):
        stat = self._ensure_table_stat(table_target)
        if subkey is None:
            stat[key] = stat.get(key, 0) + amount
        else:
            bucket = stat[key]
            bucket[subkey] = bucket.get(subkey, 0) + amount

    def _record_dropped(self, table_target, reason, amount=1):
        self._inc_stat(table_target, "dropped", reason, amount)

    def _print_stats(self):
        if not self.verbose_stats:
            return

        print("\n=== Merge Statistics ===")

        for table in self.table_order:
            stat = self.table_stats.get(table)
            if not stat:
                continue

            print(f"\n[{table}]")

            for file_label in sorted(stat["source_counts"].keys()):
                print(f"  {file_label}: {stat['source_counts'][file_label]} records")
            print(f"  merged: {stat.get('merged_count', 0)} records")
            print(f"  identical duplicates: {stat.get('identical', 0)}")

            if stat["duplicates_by_file"]:
                print("  merged/deduplicated by source file:")
                for file_label in sorted(stat["duplicates_by_file"].keys()):
                    print(
                        f"    {file_label}: {stat['duplicates_by_file'][file_label]} records"
                    )

            if stat["new_by_file"]:
                print("  new records by source file:")
                for file_label in sorted(stat["new_by_file"].keys()):
                    print(f"    {file_label}: {stat['new_by_file'][file_label]} records")

            if stat["dropped"]:
                print("  dropped items:")
                for reason in sorted(stat["dropped"].keys()):
                    print(f"    {reason}: {stat['dropped'][reason]}")

    def _location_signature_from_values(self, keysymbol):
        return keysymbol

    def _location_display_from_values(self, keysymbol):
        return str(keysymbol) if keysymbol else "(No KeySymbol)"

    def _is_tty_interactive(self):
        return sys.stdin.isatty() and sys.stdout.isatty()

    def _get_questionary(self):
        if not self._is_tty_interactive():
            return None
        if importlib.util.find_spec("questionary") is None:
            return None
        return importlib.import_module("questionary")

    def _rank_selected_indices(self, title, selected_indices, items):
        questionary = self._get_questionary()
        if questionary is None or len(selected_indices) <= 1:
            return list(selected_indices)

        remaining = list(selected_indices)
        ranked = []
        while remaining:
            choices = [
                questionary.Choice(title=items[idx], value=idx) for idx in remaining
            ]
            chosen = questionary.select(
                f"{title} (choose next highest priority)", choices=choices
            ).ask()
            if chosen is None:
                break
            ranked.append(chosen)
            remaining = [idx for idx in remaining if idx != chosen]

        if remaining:
            ranked.extend(remaining)
        return ranked

    def _multi_select_menu(self, title, items):
        if not items:
            return []
        questionary = self._get_questionary()
        if questionary is None:
            return None

        choices = [questionary.Choice(title=item, value=idx) for idx, item in enumerate(items)]
        result = questionary.checkbox(title, choices=choices).ask()
        if not result:
            return []
        selected = list(result)
        return self._rank_selected_indices(title, selected, items)

    def _single_select_menu(self, title, items):
        if not items:
            return None
        questionary = self._get_questionary()
        if questionary is None:
            return None

        choices = [questionary.Choice(title=item, value=idx) for idx, item in enumerate(items)]
        result = questionary.select(title, choices=choices).ask()
        return result

    def _get_location_signature(self, cursor, location_id):
        cursor.execute(selectLocationPreferenceSql, (location_id,))
        row = cursor.fetchone()
        if not row:
            return None
        return self._location_signature_from_values(row[0])

    def _prompt_yes_no(self, message, default=False):
        questionary = self._get_questionary()
        if questionary is not None:
            result = questionary.confirm(message, default=default).ask()
            return bool(result)

        answer = input(f"\n{message} [{'Y/n' if default else 'y/N'}]: ").strip().lower()
        if not answer:
            return default
        return answer in ("y", "yes")

    def _configure_source_priorities(self, database_files):
        file_labels = [
            path.basename(path.dirname(db_path)) or path.basename(db_path)
            for db_path in database_files
        ]
        unique_labels = []
        for file_label in file_labels:
            if file_label not in unique_labels:
                unique_labels.append(file_label)

        for table_target in ["Bookmark", "InputField", "Note", "UserMark"]:
            existing = self.source_file_priorities.get(table_target, [])
            ordered = [x for x in existing if x in unique_labels]
            ordered.extend([x for x in unique_labels if x not in ordered])

            print(f"\nSource priority for {table_target} conflict fallbacks:")
            for idx, item in enumerate(ordered, 1):
                print(f"  {idx}. {item}")

            selected = self._multi_select_menu(
                f"Select sources in priority order for {table_target} (top selected = highest priority)",
                ordered,
            )

            if selected is None:
                raw = input(
                    "Enter one or more source numbers in priority order (comma-separated), or press Enter to keep current order: "
                ).strip()
                if raw:
                    reordered = []
                    for token in raw.split(","):
                        token = token.strip()
                        if token.isdigit():
                            idx = int(token) - 1
                            if 0 <= idx < len(ordered):
                                chosen = ordered[idx]
                                if chosen not in reordered:
                                    reordered.append(chosen)
                    if reordered:
                        ordered = reordered + [x for x in ordered if x not in reordered]
            elif selected:
                reordered = [ordered[idx] for idx in selected]
                ordered = reordered + [x for x in ordered if x not in reordered]

            self.source_file_priorities[table_target] = ordered

    def _configure_color_priority(self):
        color_names = {
            1: "yellow",
            2: "green",
            3: "blue",
            4: "red",
            5: "orange",
            6: "purple",
        }
        ordered = [c for c in self.color_priority if c in color_names]
        ordered.extend([c for c in color_names if c not in ordered])

        print("\nCurrent highlight color priority:")
        print("  " + " > ".join(color_names[c] for c in ordered))

        selected = self._multi_select_menu(
            "Select color priority (use space to select in desired order)",
            [f"{c}: {color_names[c]}" for c in ordered],
        )
        if selected is None:
            raw = input(
                "Enter color IDs in priority order (e.g. 4,3,1,2,5,6), or press Enter to keep: "
            ).strip()
            if raw:
                reordered = []
                for token in raw.split(","):
                    token = token.strip()
                    if token.isdigit():
                        color_idx = int(token)
                        if color_idx in color_names and color_idx not in reordered:
                            reordered.append(color_idx)
                if reordered:
                    ordered = reordered + [x for x in ordered if x not in reordered]
        elif selected:
            reordered = [ordered[idx] for idx in selected]
            ordered = reordered + [x for x in ordered if x not in reordered]

        self.color_priority = ordered

    def _maybe_configure_location_preferences(self, database_files):
        if self.conflict_policy != "prompt":
            return

        if self._prompt_yes_no(
            "Configure per-table source priority for automatic conflict fallback?",
            default=True,
        ):
            self._configure_source_priorities(database_files)

        if self._prompt_yes_no(
            "Configure highlight color priority for identical highlight conflicts?",
            default=True,
        ):
            self._configure_color_priority()

        if not self._prompt_yes_no(
            "Do you want to prioritize highlights/notes/bookmarks/input fields from a specific input file for specific KeySymbol values?",
            default=False,
        ):
            self._save_user_config()
            return

        location_catalog = {}
        for db_path in database_files:
            file_label = path.basename(path.dirname(db_path)) or path.basename(db_path)
            conn = sqlite3.connect(db_path)
            cur = conn.cursor()
            try:
                cur.execute("SELECT KeySymbol FROM Location")
                for row in cur.fetchall():
                    sig = self._location_signature_from_values(row[0])
                    item = location_catalog.setdefault(
                        sig,
                        {
                            "display": self._location_display_from_values(row[0]),
                            "files": set(),
                        },
                    )
                    item["files"].add(file_label)
            finally:
                conn.close()

        if not location_catalog:
            print("No locations found for preference selection.")
            self._save_user_config()
            return

        indexed_locations = sorted(
            location_catalog.items(), key=lambda x: (x[1]["display"].lower(), str(x[0]))
        )

        print("\nAvailable KeySymbol groups across input files:")
        for idx, (_, info) in enumerate(indexed_locations, 1):
            files_str = ", ".join(sorted(info["files"]))
            print(f"  {idx}. {info['display']}  [files: {files_str}]")

        selected_indexes = self._multi_select_menu(
            "Select KeySymbol groups to prioritize",
            [info["display"] for _, info in indexed_locations],
        )
        if selected_indexes is None:
            raw_selection = input(
                "\nEnter one or more KeySymbol-group numbers to prioritize (comma-separated), or press Enter to skip: "
            ).strip()
            if not raw_selection:
                self._save_user_config()
                return

            selected_indexes = []
            for token in raw_selection.split(","):
                token = token.strip()
                if not token:
                    continue
                try:
                    parsed = int(token)
                    if 1 <= parsed <= len(indexed_locations):
                        selected_indexes.append(parsed - 1)
                except ValueError:
                    continue
            selected_indexes = sorted(set(selected_indexes))

        if not selected_indexes:
            print("No valid locations selected. Skipping location preferences.")
            self._save_user_config()
            return

        for sel_idx in selected_indexes:
            sig, info = indexed_locations[sel_idx]
            files = sorted(info["files"])
            print(f"\nKeySymbol group: {info['display']}")
            choice_index = self._single_select_menu(
                f"Choose source file for KeySymbol '{info['display']}'", files
            )
            if choice_index is None:
                for i, f in enumerate(files, 1):
                    print(f"  {i}. {f}")
                choice = None
                while choice is None:
                    raw_choice = input("Choose source file number for this location: ").strip()
                    try:
                        parsed_choice = int(raw_choice)
                        if 1 <= parsed_choice <= len(files):
                            choice = files[parsed_choice - 1]
                    except ValueError:
                        pass
            else:
                choice = files[choice_index]

            self.location_preferences[sig] = choice

        if self.location_preferences:
            print("\nConfigured location preferences:")
            for sig, source_file in self.location_preferences.items():
                print(f"  - {location_catalog[sig]['display']}: {source_file}")

        self._save_user_config()

    def _source_rank(self, table_target, source_label):
        priorities = self.source_file_priorities.get(table_target, [])
        try:
            return priorities.index(source_label)
        except ValueError:
            return len(priorities) + 999

    def _preferred_choice_for_location(self, cursor, location_id):
        loc_sig = self._get_location_signature(cursor, location_id)
        if not loc_sig:
            return None
        preferred_file = self.location_preferences.get(loc_sig)
        if not preferred_file:
            return None
        return "incoming" if self.current_file_label == preferred_file else "current"

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

    def _initialize_merge(self, database_files):
        """Initialize the merged database from the first source file"""
        self.start_time = time()
        self.note_bases = {}
        self.table_stats = {}

        first_db = database_files[0]
        copy2(first_db, self.merged_db_path)
        merged_conn = sqlite3.connect(self.merged_db_path)
        self.get_table_info(merged_conn)

        # Empty all tables in merged_db
        cursor = merged_conn.cursor()
        for table in self.primary_keys.keys():
            if table not in ["grdb_migrations", "LastModified"]:
                cursor.execute(f"DELETE FROM [{table}];")
        merged_conn.commit()
        return merged_conn

    def _remap_references_to_pk(self, cursor, target_table, target_pk_col, old_pk, new_pk):
        target_lower = target_table.lower()
        for from_table_lower, fk_cols in self.fk_map.items():
            from_table = self.table_name_map.get(from_table_lower)
            if not from_table:
                continue
            for from_col_lower, (to_table, _to_col) in fk_cols.items():
                if to_table.lower() != target_lower:
                    continue
                from_col = None
                cursor.execute(f"PRAGMA table_info([{from_table}])")
                for col in cursor.fetchall():
                    if col[1].lower() == from_col_lower:
                        from_col = col[1]
                        break
                if not from_col:
                    continue
                cursor.execute(
                    f"UPDATE OR IGNORE [{from_table}] SET [{from_col}] = ? WHERE [{from_col}] = ?",
                    (new_pk, old_pk),
                )
                cursor.execute(
                    f"DELETE FROM [{from_table}] WHERE [{from_col}] = ?",
                    (old_pk,),
                )

    def _choose_highlight_winner(self, options, allow_prompt=True):
        color_names = {1: "yellow", 2: "green", 3: "blue", 4: "red", 5: "orange", 6: "purple"}
        ranked = sorted(
            options,
            key=lambda o: (
                self.color_priority.index(o["color"]) if o["color"] in self.color_priority else len(self.color_priority) + 99,
                o["usermark_id"],
            ),
        )

        if self.conflict_policy != "prompt" or not allow_prompt:
            return ranked[0]

        questionary = self._get_questionary()
        if questionary is not None:
            choices = []
            for opt in ranked:
                ranges = "; ".join([f"{r[2]}-{r[3]}" for r in opt["ranges"]])
                preview = self._get_highlight_preview_text(opt.get("loc_res"), opt["ranges"])
                preview_short = (preview[:120] + "...") if len(preview) > 120 else preview
                title = f"{color_names.get(opt['color'], opt['color'])} | UserMarkId={opt['usermark_id']} | tokens={ranges} | {preview_short}"
                choices.append(questionary.Choice(title=title, value=opt["usermark_id"]))
            chosen_id = questionary.select(
                "Select highlight to keep for overlapping ranges", choices=choices
            ).ask()
            selected = next((o for o in ranked if o["usermark_id"] == chosen_id), None)
            if selected:
                return selected

        print("Overlapping highlights detected. Choose winner:")
        for idx, opt in enumerate(ranked, 1):
            ranges = "; ".join([f"{r[2]}-{r[3]}" for r in opt["ranges"]])
            preview = self._get_highlight_preview_text(opt.get("loc_res"), opt["ranges"])
            print(f"  {idx}. color={opt['color']} usermark={opt['usermark_id']} tokens={ranges}")
            print(f"     text: {preview}")
        try:
            chosen_idx = int(input("Pick option number: ").strip())
            if 1 <= chosen_idx <= len(ranked):
                return ranked[chosen_idx - 1]
        except Exception:
            pass
        return ranked[0]

    def _highlight_token_signature(self, ranges):
        return tuple(sorted((r[2], r[3]) for r in ranges))

    def _get_highlight_preview_text(self, loc_res, ranges):
        if not loc_res:
            return "(Text unavailable: missing location)"

        cache_key = (tuple(loc_res), tuple(ranges))
        if cache_key in self.highlight_preview_cache:
            return self.highlight_preview_cache[cache_key]

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
            full_text.append(txt or self._format_highlight_marker(r))
        preview = " [...] ".join(full_text) if full_text else "(Text unavailable)"
        self.highlight_preview_cache[cache_key] = preview
        return preview

    def _dedupe_highlights_post_merge(self, merged_conn):
        cursor = merged_conn.cursor()
        cursor.execute("SELECT DISTINCT LocationId FROM UserMark WHERE LocationId IS NOT NULL")
        location_ids = [r[0] for r in cursor.fetchall()]

        for loc_id in location_ids:
            cursor.execute(selectLocationSql, (loc_id,))
            loc_res = cursor.fetchone()
            cursor.execute("SELECT UserMarkId, ColorIndex FROM UserMark WHERE LocationId = ?", (loc_id,))
            usermarks = []
            for um_id, color in cursor.fetchall():
                cursor.execute(selectBlockRangeSql, (um_id,))
                ranges = sorted(cursor.fetchall())
                usermarks.append(
                    {
                        "usermark_id": um_id,
                        "color": color,
                        "ranges": ranges,
                        "source": "current",
                        "loc_res": loc_res,
                    }
                )

            components = self._find_highlight_components(usermarks)
            for comp in components:
                if len(comp) <= 1:
                    continue

                by_token_range = {}
                for hl in comp:
                    by_token_range.setdefault(self._highlight_token_signature(hl["ranges"]), []).append(hl)

                if len(by_token_range) == 1:
                    winner = self._choose_highlight_winner(comp, allow_prompt=False)
                    reason = "Duplicate highlight token range resolved by color priority"
                else:
                    winner = self._choose_highlight_winner(comp, allow_prompt=True)
                    reason = "Overlapping highlight resolved by user/priority selection"

                winner_id = winner["usermark_id"]
                for hl in comp:
                    if hl["usermark_id"] == winner_id:
                        continue
                    old_id = hl["usermark_id"]
                    self._remap_references_to_pk(
                        cursor,
                        "UserMark",
                        "UserMarkId",
                        old_id,
                        winner_id,
                    )
                    cursor.execute("DELETE FROM BlockRange WHERE UserMarkId = ?", (old_id,))
                    cursor.execute("DELETE FROM UserMark WHERE UserMarkId = ?", (old_id,))
                    self._record_dropped("UserMark", reason)

        merged_conn.commit()

    def _dedupe_notes_post_merge(self, merged_conn):
        cursor = merged_conn.cursor()
        cursor.execute("SELECT NoteId, Guid, LocationId, UserMarkId, LastModified FROM Note")
        rows = cursor.fetchall()
        if not rows:
            return

        note_ids = [r[0] for r in rows]
        parent = {nid: nid for nid in note_ids}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra

        by_guid = {}
        by_pair = {}
        for nid, guid, loc_id, usermark_id, _lm in rows:
            if guid:
                by_guid.setdefault(guid, []).append(nid)
            by_pair.setdefault((loc_id, usermark_id), []).append(nid)

        for ids in by_guid.values():
            for i in range(1, len(ids)):
                union(ids[0], ids[i])

        for ids in by_pair.values():
            if len(ids) <= 1:
                continue
            for i in range(1, len(ids)):
                union(ids[0], ids[i])

        row_map = {r[0]: r for r in rows}
        groups = {}
        for nid in note_ids:
            groups.setdefault(find(nid), []).append(nid)

        for ids in groups.values():
            if len(ids) <= 1:
                continue
            winner_id = max(ids, key=lambda nid: ((row_map[nid][4] or ""), nid))
            for nid in ids:
                if nid == winner_id:
                    continue
                self._remap_references_to_pk(cursor, "Note", "NoteId", nid, winner_id)
                cursor.execute("DELETE FROM Note WHERE NoteId = ?", (nid,))
                self._record_dropped("Note", "Duplicate note removed (kept latest LastModified)")

        merged_conn.commit()

    def _dedupe_inputfields_post_merge(self, merged_conn):
        cursor = merged_conn.cursor()
        cursor.execute("SELECT InputFieldId, LocationId, TextTag FROM InputField")
        rows = cursor.fetchall()
        grouped = {}
        for row in rows:
            grouped.setdefault((row[1], row[2]), []).append(row[0])

        for _key, ids in grouped.items():
            if len(ids) <= 1:
                continue
            winner_id = max(ids)
            for old_id in ids:
                if old_id == winner_id:
                    continue
                self._remap_references_to_pk(cursor, "InputField", "InputFieldId", old_id, winner_id)
                cursor.execute("DELETE FROM InputField WHERE InputFieldId = ?", (old_id,))
                self._record_dropped("InputField", "Duplicate InputField removed (same LocationId+TextTag)")

        merged_conn.commit()

    def _post_merge_dedupe(self, merged_conn):
        self._dedupe_highlights_post_merge(merged_conn)
        self._dedupe_notes_post_merge(merged_conn)
        self._dedupe_inputfields_post_merge(merged_conn)

    def _finalize_merge(self, merged_conn):
        """Finalize the merge process: update LastModified and collect media files"""
        self._post_merge_dedupe(merged_conn)
        cursor = merged_conn.cursor()
        cursor.execute(
            "UPDATE LastModified SET LastModified = strftime('%Y-%m-%dT%H:%M:%SZ', 'now');"
        )
        merged_conn.commit()

        # Collect files for archive
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

        for table_target in self.table_order:
            table = self.table_name_map.get(table_target.lower())
            if not table:
                continue
            try:
                cursor.execute(f"SELECT COUNT(*) FROM [{table}]")
                self._ensure_table_stat(table_target)["merged_count"] = cursor.fetchone()[0]
            except sqlite3.Error:
                pass

        merged_conn.close()
        self._print_stats()

    def _merge_database(self, file_path, merged_conn, table_order, identity_keys):
        """Process a single source database file and merge its tables"""
        source_conn = sqlite3.connect(file_path)
        source_cursor = source_conn.cursor()
        merged_cursor = merged_conn.cursor()
        skipped_pks = {}
        self.pk_map = {}
        self.current_file_label = path.basename(path.dirname(file_path)) or path.basename(
            file_path
        )

        for table_target in table_order:
            table = self.table_name_map.get(table_target.lower())
            if table:
                try:
                    source_cursor.execute(f"SELECT COUNT(*) FROM [{table}]")
                    src_count = source_cursor.fetchone()[0]
                except sqlite3.Error:
                    src_count = 0
                stat = self._ensure_table_stat(table_target)
                stat["source_counts"][self.current_file_label] = src_count

            self._process_table(
                table_target, source_cursor, merged_cursor, identity_keys, skipped_pks
            )

        source_conn.close()
        merged_conn.commit()

    def _process_table(
        self, table_target, source_cursor, merged_cursor, identity_keys, skipped_pks
    ):
        """Standard entry point for processing a table during merge"""
        table = self.table_name_map.get(table_target.lower())
        if not table or table not in self.primary_keys:
            return

        try:
            source_cursor.execute(f"SELECT * FROM [{table}]")
        except sqlite3.Error:
            return

        cols_source = [d[0] for d in source_cursor.description]
        rows = source_cursor.fetchall()
        self.pk_map.setdefault(table, {})
        skipped_pks.setdefault(table, set())

        merged_cursor.execute(f"PRAGMA table_info([{table}])")
        cols_target = [col[1] for col in merged_cursor.fetchall()]

        self._process_generic_table(
            table,
            table_target,
            merged_cursor,
            identity_keys,
            skipped_pks,
            cols_source,
            rows,
            cols_target,
        )

    def _process_usermark_table(
        self, table, source_cursor, merged_cursor, skipped_pks, cols_target
    ):
        """Process UserMark table with overlap detection and connected component analysis"""
        source_cursor.execute(f"SELECT * FROM [{table}]")
        rows = source_cursor.fetchall()
        cols_source = [d[0] for d in source_cursor.description]

        loc_to_usermarks = {}
        for row in rows:
            row_dict = dict(zip(cols_source, row))
            loc_to_usermarks.setdefault(row_dict.get("LocationId"), []).append(row_dict)

        source_cursor.execute("SELECT LocationId, KeySymbol FROM Location")
        loc_symbol_map = {r[0]: (r[1] or "") for r in source_cursor.fetchall()}
        sorted_loc_ids = sorted(
            loc_to_usermarks.keys(), key=lambda lid: loc_symbol_map.get(lid, "")
        )

        for loc_id in sorted_loc_ids:
            all_highlights = self._gather_highlights(
                loc_id,
                loc_to_usermarks[loc_id],
                table,
                source_cursor,
                merged_cursor,
                cols_target,
            )
            comp_list = self._find_highlight_components(all_highlights)

            for comp in comp_list:
                sig_groups = {}
                for hl in comp:
                    sig_groups.setdefault(
                        (hl["color"], tuple(hl["ranges"])), []
                    ).append(hl)

                if len(sig_groups) > 1:
                    chosen_options = self._resolve_usermark_conflict(
                        loc_id, sig_groups, merged_cursor
                    )
                else:
                    proto = list(sig_groups.values())[0][0]
                    chosen_options = [{
                        "color": proto["color"],
                        "ranges": proto["ranges"],
                        "highlights": list(sig_groups.values())[0],
                    }]

                self._apply_usermark_choice(
                    table,
                    "UserMark",
                    comp,
                    chosen_options,
                    merged_cursor,
                    source_cursor,
                    skipped_pks,
                )

    def _gather_highlights(
        self, loc_id, incoming_rows, table, source_cursor, merged_cursor, cols_target
    ):
        """Gather all existing and incoming highlights for a specific location"""
        all_highlights = []
        merged_cursor.execute(
            "SELECT UserMarkId, ColorIndex FROM UserMark WHERE LocationId = ?",
            (loc_id,),
        )
        for um_id, color in merged_cursor.fetchall():
            merged_cursor.execute(
                selectBlockRangeSql,
                (um_id,),
            )
            all_highlights.append(
                {
                    "usermark_id": um_id,
                    "color": color,
                    "ranges": sorted(merged_cursor.fetchall()),
                    "source": "current",
                    "source_label": "existing",
                }
            )

        for row_src in incoming_rows:
            old_pk = row_src.get(self.primary_keys[table][0])
            source_cursor.execute(
                selectBlockRangeSql,
                (old_pk,),
            )
            row_dict = {
                ct: row_src.get(
                    next((ks for ks in row_src if ks.lower() == ct.lower()), None)
                )
                for ct in cols_target
            }
            all_highlights.append(
                {
                    "usermark_id": old_pk,
                    "color": row_dict.get("ColorIndex"),
                    "ranges": sorted(source_cursor.fetchall()),
                    "source": "incoming",
                    "source_label": self.current_file_label,
                    "row_dict": row_dict,
                }
            )
        return all_highlights

    def _find_highlight_components(self, all_highlights):
        """Find connected components of highlights based on token overlap or identical signatures"""
        num_hl = len(all_highlights)
        adj = {i: set() for i in range(num_hl)}
        for i in range(num_hl):
            for j in range(i + 1, num_hl):
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
        return hl_components

    def _resolve_usermark_conflict(self, loc_id, sig_groups, merged_cursor):
        """Resolve highlight conflicts; supports color-priority auto-choice and multi-select overlap workflow."""
        loc_info = self.get_location_info(merged_cursor, loc_id)
        print(f"\nConflict in Highlight at {loc_info}:")
        print(
            f"  Found {sum(len(v) for v in sig_groups.values())} highlight(s) with {len(sig_groups)} unique variant(s)"
        )

        color_names = {1: "yellow", 2: "green", 3: "blue", 4: "red", 5: "orange", 6: "purple"}
        color_codes = {1: "\033[93m", 2: "\033[92m", 3: "\033[94m", 4: "\033[91m", 5: "\033[38;5;208m", 6: "\033[95m"}
        RESET = "\033[0m"

        merged_cursor.execute(selectLocationSql, (loc_id,))
        loc_res = merged_cursor.fetchone()
        if loc_res:
            print("  Fetching text context from JW.org...")

        options = []
        for idx, (sig, group) in enumerate(sig_groups.items(), 1):
            color, ranges = sig
            sources = sorted({hl.get("source_label", hl["source"]) for hl in group})
            color_name = color_names.get(color, f"color_{color}")
            color_code = color_codes.get(color, "")
            print(f"\n  Option {idx}: {color_code}{color_name}{RESET} ({len(group)} instance(s): {', '.join(sources)})")
            text = None
            if loc_res:
                full_text = []
                for r in ranges:
                    txt = self.get_highlighted_text(loc_res[0], r[1], r[2], r[3], loc_res[1], loc_res[2], loc_res[3], loc_res[4])
                    full_text.append(txt or self._format_highlight_marker(r))
                text = " [...] ".join(full_text) if full_text else None
            print(f"    Text: {color_code}{text if text else '(Text unavailable)'}{RESET}")
            options.append({"color": color, "ranges": ranges, "highlights": group, "label": f"Option {idx}: {color_name}"})

        unique_ranges = {tuple(o["ranges"]) for o in options}
        conflict_key = (loc_res, tuple(sorted((o["color"], tuple(o["ranges"])) for o in options)))

        if len(unique_ranges) == 1:
            ranked = sorted(
                options,
                key=lambda o: self.color_priority.index(o["color"]) if o["color"] in self.color_priority else len(self.color_priority)+99,
            )
            chosen = ranked[0]
            print(f"  (Auto-selected by color priority: {color_names.get(chosen['color'], chosen['color'])})")
            self.conflict_cache["UserMark"][conflict_key] = [
                (chosen["color"], tuple(chosen["ranges"]))
            ]
            return [chosen]

        cached = self.conflict_cache["UserMark"].get(conflict_key)
        if cached:
            chosen = [o for o in options if (o["color"], tuple(o["ranges"])) in cached]
            if chosen:
                print("  (Using previously resolved choice)")
                return chosen

        preferred_choice = self._preferred_choice_for_location(merged_cursor, loc_id)
        if preferred_choice:
            ordered = sorted(
                options,
                key=lambda o: min(
                    [
                        self._source_rank("UserMark", h.get("source_label", self.current_file_label))
                        for h in o["highlights"]
                    ]
                    + [9999]
                ),
            )
            chosen = ordered[0]
            print(f"  (Auto-selected by location/source preference: {chosen['label']})")
            self.conflict_cache["UserMark"][conflict_key] = [(chosen["color"], tuple(chosen["ranges"]))]
            return [chosen]

        if self.conflict_policy == "prompt":
            questionary = self._get_questionary()
            if questionary is not None:
                choices = [questionary.Choice(title=o["label"], value=i) for i, o in enumerate(options)]
                selected = questionary.checkbox(
                    "Choose one or more highlight variants to keep (non-selected items map to nearest selected)",
                    choices=choices,
                ).ask()
                if not selected:
                    selected = [0]
            else:
                raw = input("Choose option numbers to keep (comma-separated): ").strip()
                selected = []
                for t in raw.split(","):
                    t=t.strip()
                    if t.isdigit() and 1 <= int(t) <= len(options):
                        selected.append(int(t)-1)
                if not selected:
                    selected = [0]
            chosen = [options[i] for i in sorted(set(selected))]
        elif self.conflict_policy in ("incoming", "merged"):
            incoming = [o for o in options if any(h["source"] == "incoming" for h in o["highlights"])]
            chosen = incoming[:1] if incoming else [options[0]]
        elif self.conflict_policy == "current":
            current = [o for o in options if any(h["source"] == "current" for h in o["highlights"])]
            chosen = current[:1] if current else [options[0]]
        else:
            raise RuntimeError(f"Unsupported conflict policy for UserMark: {self.conflict_policy}")

        self.conflict_cache["UserMark"][conflict_key] = [
            (o["color"], tuple(o["ranges"])) for o in chosen
        ]
        return chosen

    def _highlight_anchor(self, highlight):
        starts = [r[2] for r in highlight.get("ranges", [])]
        return min(starts) if starts else 0

    def _apply_usermark_choice(
        self,
        table,
        table_target,
        comp,
        chosen_options,
        merged_cursor,
        source_cursor,
        skipped_pks,
    ):
        """Apply chosen highlight variants and remap discarded highlights to nearest chosen variant."""
        chosen_hls = []
        for option in chosen_options:
            chosen_hls.extend(option["highlights"])
        chosen_ids = {h["usermark_id"] for h in chosen_hls}

        selected_leads = []
        comp_existing = [h for h in comp if h["source"] == "current"]

        for option in chosen_options:
            lead = next((h for h in option["highlights"] if h["source"] == "current"), None)
            if lead is None:
                lead = option["highlights"][0]

            lead_id = lead["usermark_id"]
            if lead["source"] == "incoming":
                row_dict = lead["row_dict"].copy()
                if isinstance(row_dict.get(self.primary_keys[table][0]), int):
                    del row_dict[self.primary_keys[table][0]]

                existing_guid_pk = None
                if row_dict.get("UserMarkGuid"):
                    merged_cursor.execute(
                        f"SELECT {self.primary_keys[table][0]} FROM [{table}] WHERE UserMarkGuid = ?",
                        (row_dict.get("UserMarkGuid"),),
                    )
                    row = merged_cursor.fetchone()
                    if row:
                        existing_guid_pk = row[0]

                if existing_guid_pk is not None:
                    lead_id = existing_guid_pk
                    merged_cursor.execute(
                        f"UPDATE [{table}] SET ColorIndex = ?, LocationId = ? WHERE {self.primary_keys[table][0]} = ?",
                        (row_dict.get("ColorIndex"), row_dict.get("LocationId"), lead_id),
                    )
                else:
                    cols = ", ".join([f"[{k}]" for k in row_dict.keys()])
                    merged_cursor.execute(
                        f"INSERT INTO [{table}] ({cols}) VALUES ({', '.join(['?'] * len(row_dict))})",
                        list(row_dict.values()),
                    )
                    lead_id = merged_cursor.lastrowid

                merged_cursor.execute("DELETE FROM BlockRange WHERE UserMarkId = ?", (lead_id,))
                for r in option["ranges"]:
                    merged_cursor.execute(
                        "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                        list(r) + [lead_id],
                    )
                self.pk_map[table][lead["usermark_id"]] = lead_id
            else:
                merged_cursor.execute("UPDATE UserMark SET ColorIndex = ? WHERE UserMarkId = ?", (option["color"], lead_id))
                merged_cursor.execute("DELETE FROM BlockRange WHERE UserMarkId = ?", (lead_id,))
                for r in option["ranges"]:
                    merged_cursor.execute(
                        "INSERT INTO BlockRange (BlockType, Identifier, StartToken, EndToken, UserMarkId) VALUES (?, ?, ?, ?, ?)",
                        list(r) + [lead_id],
                    )

            selected_leads.append({"usermark_id": lead_id, "ranges": option["ranges"]})

        if not selected_leads:
            return

        for hl in comp:
            if hl["usermark_id"] in chosen_ids:
                continue
            nearest = min(selected_leads, key=lambda x: abs(self._highlight_anchor({"ranges": x["ranges"]}) - self._highlight_anchor(hl)))
            target_id = nearest["usermark_id"]
            if hl["source"] == "incoming":
                self.pk_map[table][hl["usermark_id"]] = target_id
            else:
                merged_cursor.execute("UPDATE Note SET UserMarkId = ? WHERE UserMarkId = ?", (target_id, hl["usermark_id"]))
                merged_cursor.execute("DELETE FROM BlockRange WHERE UserMarkId = ?", (hl["usermark_id"],))
                merged_cursor.execute("DELETE FROM UserMark WHERE UserMarkId = ?", (hl["usermark_id"],))

        incoming_hls = [h for h in comp if h["source"] == "incoming"]
        skipped_pks.setdefault("BlockRange", set())
        for hl in incoming_hls:
            source_cursor.execute("SELECT BlockRangeId FROM BlockRange WHERE UserMarkId = ?", (hl["usermark_id"],))
            for (br_id,) in source_cursor.fetchall():
                skipped_pks["BlockRange"].add(br_id)

        deduped = max(0, len(comp) - len(chosen_hls))
        if deduped:
            self._inc_stat(table_target, "duplicates_by_file", self.current_file_label, deduped)
            self._record_dropped(table_target, "Merged/discarded highlight variant mapped to closest kept variant", deduped)

    def _process_generic_table(
        self,
        table,
        table_target,
        merged_cursor,
        identity_keys,
        skipped_pks,
        cols_source,
        rows,
        cols_target,
    ):
        """Process rows for a standard table with deduplication and conflict handling"""
        for row in rows:
            row_dict_src = dict(zip(cols_source, row))
            old_pk = row_dict_src.get(self.primary_keys[table][0])
            if old_pk in skipped_pks.get(table, set()):
                self._record_dropped(table_target, "Skipped after UserMark conflict merge")
                continue

            row_dict = {
                ct: row_dict_src.get(
                    next((ks for ks in row_dict_src if ks.lower() == ct.lower()), None)
                )
                for ct in cols_target
            }
            self._remap_fks(table, row_dict)

            existing_pk = self._find_existing_pk(
                table, table_target, row_dict, identity_keys, merged_cursor
            )

            if existing_pk is not None:
                self._inc_stat(
                    table_target,
                    "duplicates_by_file",
                    self.current_file_label,
                )
                self._record_dropped(table_target, "Duplicate (deduplicated)")
                if old_pk is not None:
                    self.pk_map[table][old_pk] = existing_pk
            else:
                new_pk = self._insert_row(table, table_target, row_dict, merged_cursor)
                if old_pk is not None and new_pk is not None:
                    self.pk_map[table][old_pk] = new_pk
                    self._inc_stat(table_target, "new_by_file", self.current_file_label)

    def _remap_fks(self, table, row_dict):
        """Remap foreign keys in the row_dict based on pk_map"""
        table_lower = table.lower()
        if table_lower in self.fk_map:
            for col_name, val in row_dict.items():
                col_lower = col_name.lower()
                if col_lower in self.fk_map[table_lower]:
                    to_table, _ = self.fk_map[table_lower][col_lower]
                    to_table_canonical = self.table_name_map.get(
                        to_table.lower(), to_table
                    )
                    if val in self.pk_map.get(to_table_canonical, {}):
                        row_dict[col_name] = self.pk_map[to_table_canonical][val]

    def _find_existing_pk(
        self, table, table_target, row_dict, identity_keys, merged_cursor
    ):
        """Find an existing row in the merged database with the same identity"""
        id_cols = identity_keys.get(table_target)
        if not id_cols:
            return None

        conditions = []
        vals = []
        for c in id_cols:
            if row_dict.get(c) is None:
                conditions.append(f"[{c}] IS ?")
            elif table_target == "Tag" and c == "Name":
                conditions.append(f"[{c}] = ? COLLATE NOCASE")
            else:
                conditions.append(f"[{c}] = ?")
            vals.append(row_dict.get(c))

        query = f"SELECT {self.primary_keys[table][0]} FROM [{table}] WHERE {' AND '.join(conditions)}"
        merged_cursor.execute(query, vals)
        res = merged_cursor.fetchone()
        return res[0] if res else None

    def _insert_row(self, table, table_target, row_dict, merged_cursor):
        """Insert a row into the merged database, handling special cases like TagMap positions"""
        insert_dict = row_dict.copy()
        if table_target == "Note":
            self.note_bases[row_dict.get("Guid")] = {
                "title": row_dict.get("Title"),
                "content": row_dict.get("Content"),
            }

        pk_name = self.primary_keys[table][0]
        if len(self.primary_keys[table]) == 1 and isinstance(
            insert_dict.get(pk_name), int
        ):
            del insert_dict[pk_name]

        cols = ", ".join([f"[{k}]" for k in insert_dict.keys()])
        placeholders = ", ".join(["?"] * len(insert_dict))
        query = f"INSERT INTO [{table}] ({cols}) VALUES ({placeholders})"

        try:
            merged_cursor.execute(query, list(insert_dict.values()))
            return merged_cursor.lastrowid
        except sqlite3.IntegrityError as e:
            if table_target == "TagMap" and "TagMap.TagId, TagMap.Position" in str(e):
                tag_id, position = insert_dict.get("TagId"), insert_dict.get("Position")
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
        except sqlite3.Error as e:
            self.output["errors"].append((table, query, e))
        return None

    def _resolve_generic_conflict(
        self, table, table_target, merged_cursor, existing_pk, row_dict, cols_target
    ):
        """Handle conflicts for Bookmark, InputField, and Note via 3-way merge or user prompt"""
        merged_cursor.execute(
            f"SELECT * FROM [{table}] WHERE {self.primary_keys[table][0]} = ?",
            (existing_pk,),
        )
        current_row = dict(zip(cols_target, merged_cursor.fetchone()))

        diffs = {
            c: (current_row.get(c), row_dict[c])
            for c in row_dict
            if c not in self.primary_keys[table] and row_dict[c] != current_row.get(c)
        }
        if not diffs:
            return "identical"

        if table_target == "Note":
            return self._handle_note_merge(
                table, merged_cursor, existing_pk, row_dict, current_row
            )

        loc_info = self.get_location_info(merged_cursor, current_row.get("LocationId"))
        print(f"\nConflict in {table_target} at {loc_info}:")
        for col, (old_v, new_v) in diffs.items():
            print(f"  {col}: current='{old_v}' vs incoming='{new_v}'")

        options = ["c", "i"]
        merged_val = None
        if table_target == "InputField":
            options.append("m")
            merged_val = self.merge_text(
                None, current_row.get("Value"), row_dict.get("Value")
            )
            print(f"  Merged value: '{merged_val}'")

        preferred_choice = self._preferred_choice_for_location(
            merged_cursor, current_row.get("LocationId")
        )
        if preferred_choice == "incoming":
            print(
                f"  (Auto-selected by location preference: incoming from {self.current_file_label})"
            )
            choice = "i"
        elif preferred_choice == "current":
            print("  (Auto-selected by location preference: keep current)")
            choice = "c"
        elif self.conflict_policy == "current":
            choice = "c"
        elif self.conflict_policy == "incoming":
            choice = "i"
        elif self.conflict_policy == "merged":
            if "m" in options:
                choice = "m"
            else:
                choice = "c"
        else:
            choice = ""

        # Caching and Choice
        merged_cursor.execute(
            selectLocationSql,
            (current_row.get("LocationId"),),
        )
        loc_res = merged_cursor.fetchone()
        conflict_key = (
            table_target,
            loc_res,
            current_row.get("Slot" if table_target == "Bookmark" else "TextTag"),
            tuple(sorted(diffs.items())),
        )

        if not choice:
            choice = self.conflict_cache[table_target].get(conflict_key, "")
        if choice:
            print(f"  (Using previously resolved choice: {choice})")
        else:
            if self.conflict_policy != "prompt":
                raise RuntimeError(
                    f"Non-interactive conflict policy '{self.conflict_policy}' produced no valid choice for {table_target}"
                )
            while choice not in options:
                choice = input(
                    f"Keep (c)urrent, (i)ncoming{', or (m)erged' if 'm' in options else ''}? "
                ).lower()
            self.conflict_cache[table_target][conflict_key] = choice

        if choice == "i":
            set_clause = ", ".join([f"[{k}] = ?" for k in diffs.keys()])
            merged_cursor.execute(
                f"UPDATE [{table}] SET {set_clause} WHERE {self.primary_keys[table][0]} = ?",
                [row_dict[k] for k in diffs.keys()] + [existing_pk],
            )
            return "used_incoming"
        if choice == "m" and table_target == "InputField":
            merged_cursor.execute(
                f"UPDATE [{table}] SET Value = ? WHERE {self.primary_keys[table][0]} = ?",
                (merged_val, existing_pk),
            )
            return "merged"
        return "kept_current"

    def _n_way_merge_note_variants(self, variants):
        if not variants:
            return ("", "")
        merged_title = variants[0][0] or ""
        merged_content = variants[0][1] or ""
        for title, content in variants[1:]:
            merged_title = self.merge_text(None, merged_title, title or "")
            merged_content = self.merge_text(None, merged_content, content or "")
        return merged_title, merged_content

    def _handle_note_merge(
        self, table, merged_cursor, existing_pk, row_dict, current_row
    ):
        """Resolve note conflicts by showing deduplicated n-way variants plus smart merged choice."""
        guid = row_dict.get("Guid")

        if row_dict.get("Title") == current_row.get("Title") and row_dict.get("Content") == current_row.get("Content"):
            return "identical"

        merged_cursor.execute(selectLocationSql, (current_row.get("LocationId"),))
        loc_res = merged_cursor.fetchone()
        conflict_id = (guid, loc_res)
        variant_map = self.note_conflict_variants.setdefault(conflict_id, {})

        current_variant = (current_row.get("Title") or "", current_row.get("Content") or "")
        incoming_variant = (row_dict.get("Title") or "", row_dict.get("Content") or "")
        variant_map.setdefault(current_variant, set()).add("existing")
        variant_map.setdefault(incoming_variant, set()).add(self.current_file_label or "incoming")

        dedup_variants = sorted(variant_map.items(), key=lambda kv: (kv[0][0], kv[0][1]))
        merged_title, merged_content = self._n_way_merge_note_variants([v for v, _ in dedup_variants])

        loc_info = self.get_location_info(merged_cursor, current_row.get("LocationId"))
        print(f"\nConflict in Note at {loc_info} (GUID: {guid}):")

        preferred_choice = self._preferred_choice_for_location(merged_cursor, current_row.get("LocationId"))
        if preferred_choice == "incoming":
            choice = "incoming"
        elif preferred_choice == "current":
            choice = "current"
        elif self.conflict_policy == "current":
            choice = "current"
        elif self.conflict_policy == "incoming":
            choice = "incoming"
        elif self.conflict_policy == "merged":
            choice = "smart_merged"
        else:
            choice = ""

        options = []
        for idx, (variant, sources) in enumerate(dedup_variants, 1):
            title, content = variant
            label = f"Variant {idx} (sources: {', '.join(sorted(sources))})"
            print(f"  {label}: title='{title}' content='{content[:120]}'")
            options.append((label, variant))

        smart_label = "Smart merged variant"
        print(f"  {smart_label}: title='{merged_title}' content='{merged_content[:120]}'")

        if not choice:
            questionary = self._get_questionary()
            if questionary is not None:
                q_choices = [questionary.Choice(title=lbl, value=var) for lbl, var in options]
                q_choices.append(questionary.Choice(title=smart_label, value=(merged_title, merged_content, "smart")))
                selected = questionary.select("Choose note value to keep", choices=q_choices).ask()
                if isinstance(selected, tuple) and len(selected) == 3:
                    choice = "smart_merged"
                else:
                    choice = selected
            else:
                for i, (lbl, _) in enumerate(options, 1):
                    print(f"    {i}. {lbl}")
                print(f"    {len(options)+1}. {smart_label}")
                picked = None
                while picked is None:
                    raw = input("Choose variant number: ").strip()
                    if raw.isdigit():
                        pos = int(raw)
                        if 1 <= pos <= len(options):
                            picked = options[pos-1][1]
                        elif pos == len(options) + 1:
                            choice = "smart_merged"
                            picked = (merged_title, merged_content)
                if choice != "smart_merged":
                    choice = picked
        elif self.conflict_policy != "prompt" and not choice:
            raise RuntimeError("Non-interactive note conflict resolution produced no choice")

        final_t, final_c = current_variant
        resolution = "kept_current"
        if choice == "incoming":
            final_t, final_c = incoming_variant
            resolution = "used_incoming"
        elif choice == "current":
            final_t, final_c = current_variant
            resolution = "kept_current"
        elif choice == "smart_merged":
            final_t, final_c = merged_title, merged_content
            resolution = "merged"
        elif isinstance(choice, tuple):
            final_t, final_c = choice[0], choice[1]
            resolution = "merged"

        latest_ts = max(row_dict.get("LastModified") or "", current_row.get("LastModified") or "")
        merged_cursor.execute(
            f"UPDATE [{table}] SET Title = ?, Content = ?, LastModified = ? WHERE {self.primary_keys[table][0]} = ?",
            (final_t, final_c, latest_ts, existing_pk),
        )
        return resolution

    def process_databases(self, database_files):
        """Process databases table-by-table across all sources."""
        merged_conn = self._initialize_merge(database_files)
        self.note_conflict_variants = {}
        self._maybe_configure_location_preferences(database_files)

        file_labels = {
            db_path: (path.basename(path.dirname(db_path)) or path.basename(db_path))
            for db_path in database_files
        }

        pk_maps_by_file = {db_path: {} for db_path in database_files}
        skipped_by_file = {db_path: {} for db_path in database_files}

        for table_target in tqdm(self.table_order, desc="Merging tables"):
            table = self.table_name_map.get(table_target.lower())
            if not table:
                continue

            ordered_files = sorted(
                database_files,
                key=lambda dbp: self._source_rank(table_target, file_labels[dbp]),
            )

            for db_path in ordered_files:
                self.current_file_label = file_labels[db_path]
                self.pk_map = pk_maps_by_file[db_path]
                skipped_pks = skipped_by_file[db_path]

                source_conn = sqlite3.connect(db_path)
                source_cursor = source_conn.cursor()
                merged_cursor = merged_conn.cursor()

                try:
                    source_cursor.execute(f"SELECT COUNT(*) FROM [{table}]")
                    src_count = source_cursor.fetchone()[0]
                except sqlite3.Error:
                    src_count = 0
                stat = self._ensure_table_stat(table_target)
                stat["source_counts"][self.current_file_label] = src_count

                self._process_table(
                    table_target,
                    source_cursor,
                    merged_cursor,
                    self.identity_keys,
                    skipped_pks,
                )
                source_conn.close()
                merged_conn.commit()

        self._finalize_merge(merged_conn)

    def create_jwl_file(self):
        """Create JWL file from the merged database in the working folder

        Returns:
            None
        """
        merged_dir = path.join(self.working_folder, "merged")
        manifest_file_path = path.join(merged_dir, "manifest.json")
        all_unzip_folder_names = [
            directory
            for directory in listdir(self.working_folder)
            if directory != "merged"
            and path.isdir(path.join(self.working_folder, directory))
        ]
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

        self.clean_temp_files()

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

    def _format_highlight_marker(self, block_range):
        block_type, identifier, start_token, end_token = block_range
        return (
            f"[Position: block={block_type}, pid={identifier}, tokens={start_token}-{end_token}]"
        )

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
                        "User-Agent": self.user_agent,
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
                            "User-Agent": self.user_agent,
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
                    "User-Agent": self.user_agent,
                }

                r = requests.get(url, headers=headers, timeout=5)

                if urlparse(r.url).path.count("/") <= 2:
                    raise ValueError(f"Invalid redirect to {r.url}")

                html_content = r.text
                self.doc_cache[(docid, lang_code)] = html_content
            except Exception as e:
                print(f"Error fetching content: {e}")
                return None

        parser = PExtractor(identifier)
        parser.feed(html_content)
        full_text = parser.text

        if not full_text:
            return f"[Text unavailable for pid={identifier}, tokens={start_token}-{end_token}]"

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
                selectBlockRangeSql,
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

    def clean_temp_files(self, force=False):
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

    def unzip_file(self, file_path):
        """Unzip a file

        Args:
            file_path (str): Path to the file to unzip

        Returns:
            str: Path to the unzipped file
        """
        basename = path.splitext(path.basename(file_path))[0]
        unzip_path = path.join(self.working_folder, basename)
        unpack_archive(file_path, extract_dir=unzip_path, format="zip")
        return unzip_path

    def get_first_db_file(self, unzip_path):
        """Get the first database file in the unzipped folder

        Args:
            unzip_path (str): Path to the unzipped folder

        Returns:
            str: Path to the first database file
        """
        db_files = glob(unzip_path + "/*.db")
        if db_files:
            return db_files[0]
        else:
            return None

    def get_jwl_files(self):
        """Get the list of JW Library backup files to merge

        Returns:
            list: List of JW Library backup database files
        """
        file_paths = []
        if args.file is not None or args.folder is not None:
            if args.file:
                file_paths.extend(args.file)
            if args.folder:
                folder_files = []
                for file in listdir(args.folder):
                    if not file.lower().endswith(".jwlibrary"):
                        continue
                    folder_files.append(path.join(args.folder, file))
                file_paths.extend(sorted(folder_files, key=lambda p: p.lower()))
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
        normalized = []
        seen = set()
        for fp in file_paths:
            nfp = path.normpath(fp)
            if nfp not in seen:
                seen.add(nfp)
                normalized.append(nfp)
        file_paths = sorted(normalized, key=lambda p: p.lower())

        if not file_paths or len(file_paths) == 1:
            print("Not enough JW Library backups found to work with!")
            print()
            if len(file_paths) > 0:
                print("Provided arguments:")
                provided = []
                if args.file:
                    provided.extend(args.file)
                if args.folder:
                    provided.append(args.folder)
                print("\n".join([f"- {p}" for p in provided]))
            exit()
        self.clean_temp_files(force=True)
        print(
            "JW Library backup files to be merged:\n"
            + "\n".join(["- " + file_path for file_path in file_paths])
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

    def _create_test_db(self, db_path, data_ops=None):
        """Create a test database with schema and optional data"""
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()

        # Define Schema (Simplified based on usage)
        schema = [
            "CREATE TABLE IF NOT EXISTS Location (LocationId INTEGER PRIMARY KEY, BookNumber INTEGER, ChapterNumber INTEGER, DocumentId INTEGER, Track INTEGER, IssueTagNumber INTEGER, KeySymbol TEXT, MepsLanguage INTEGER, Type INTEGER, Title TEXT)",
            "CREATE TABLE IF NOT EXISTS Tag (TagId INTEGER PRIMARY KEY, Type INTEGER, Name TEXT)",
            "CREATE TABLE IF NOT EXISTS UserMark (UserMarkId INTEGER PRIMARY KEY, ColorIndex INTEGER, LocationId INTEGER, UserMarkGuid TEXT)",
            "CREATE TABLE IF NOT EXISTS BlockRange (BlockRangeId INTEGER PRIMARY KEY, BlockType INTEGER, Identifier INTEGER, StartToken INTEGER, EndToken INTEGER, UserMarkId INTEGER)",
            "CREATE TABLE IF NOT EXISTS Note (NoteId INTEGER PRIMARY KEY, Guid TEXT, Title TEXT, Content TEXT, LastModified TEXT, LocationId INTEGER, UserMarkId INTEGER)",
            "CREATE TABLE IF NOT EXISTS Bookmark (BookmarkId INTEGER PRIMARY KEY, PublicationLocationId INTEGER, Slot INTEGER, Title TEXT, Snippet TEXT, LocationId INTEGER)",
            "CREATE TABLE IF NOT EXISTS InputField (InputFieldId INTEGER PRIMARY KEY, LocationId INTEGER, TextTag TEXT, Value TEXT)",
            "CREATE TABLE IF NOT EXISTS TagMap (TagMapId INTEGER PRIMARY KEY, TagId INTEGER, PlaylistItemId INTEGER, LocationId INTEGER, NoteId INTEGER, Position INTEGER)",
            "CREATE TABLE IF NOT EXISTS PlaylistItem (PlaylistItemId INTEGER PRIMARY KEY, Label TEXT, ThumbnailFilePath TEXT, StoragePath TEXT)",
            "CREATE TABLE IF NOT EXISTS IndependentMedia (IndependentMediaId INTEGER PRIMARY KEY, Hash TEXT, FilePath TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemAccuracy (PlaylistItemAccuracyId INTEGER PRIMARY KEY, Description TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemIndependentMediaMap (PlaylistItemId INTEGER, IndependentMediaId INTEGER)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemLocationMap (PlaylistItemId INTEGER, LocationId INTEGER)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarker (PlaylistItemMarkerId INTEGER PRIMARY KEY, PlaylistItemId INTEGER, Label TEXT, StartTime TEXT, Duration TEXT)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarkerBibleVerseMap (PlaylistItemMarkerId INTEGER, VerseId INTEGER)",
            "CREATE TABLE IF NOT EXISTS PlaylistItemMarkerParagraphMap (PlaylistItemMarkerId INTEGER, MepsDocumentId INTEGER, ParagraphIndex INTEGER, MarkerIndexWithinParagraph INTEGER)",
            "CREATE TABLE IF NOT EXISTS LastModified (LastModified TEXT)",
            "INSERT INTO LastModified (LastModified) VALUES ('2026-01-29T00:00:00Z')",
        ]

        for statement in schema:
            cursor.execute(statement)

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
        """Run automated tests"""
        print("\n=== Running Automated Tests ===\n")
        import tempfile
        import shutil

        test_dir = tempfile.mkdtemp(prefix="jwl_test_")
        try:
            db1_path = path.join(test_dir, "db1.db")
            db2_path = path.join(test_dir, "db2.db")
            db3_path = path.join(test_dir, "db3.db")

            # --- Case 1: Deduplication and Simple Merge ---
            print("Test 1: Simple Deduplication...")
            data1 = {
                "Tag": [{"Type": 1, "Name": "Favorites"}],
                "Location": [{"LocationId": 1, "KeySymbol": "nwt", "Title": "Psalm 1"}],
            }
            data2 = {
                "Tag": [{"Type": 1, "Name": "Favorites"}],  # Duplicate
                "Location": [
                    {"LocationId": 1, "KeySymbol": "nwt", "Title": "Psalm 2"}
                ],  # Different Title, should merge (if identity allows) or add
            }
            self._create_test_db(db1_path, data1)
            self._create_test_db(db2_path, data2)

            # Clear previous state
            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            if not path.exists(self.working_folder):
                makedirs(self.working_folder)

            self.process_databases([db1_path, db2_path])

            # Verify Tag
            conn = sqlite3.connect(self.merged_db_path)
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM Tag")
            tag_count = cursor.fetchone()[0]
            conn.close()
            assert tag_count == 1, f"Expected 1 tag, got {tag_count}"
            print("  ✓ Tag deduplicated")

            # --- Case 2: Note 3-way Merge (Simulated) ---
            print("\nTest 2: Note 3-way Merge...")
            # We'll use mocked input to bypass the blocking input() call
            import builtins

            original_input = builtins.input
            builtins.input = lambda _: "m"  # Always choose 'merged'

            note_loc_title = "Note Loc"

            data1_note = {
                "Location": [{"LocationId": 10, "Title": note_loc_title}],
                "Note": [
                    {
                        "Guid": "note-123",
                        "Title": "Base Title",
                        "Content": "Base Content",
                        "LocationId": 10,
                    }
                ],
            }
            data2_note = {
                "Location": [{"LocationId": 10, "Title": note_loc_title}],
                "Note": [
                    {
                        "Guid": "note-123",
                        "Title": "User A Title",
                        "Content": "Base Content",
                        "LocationId": 10,
                    }
                ],
            }
            data3_note = {
                "Location": [{"LocationId": 10, "Title": note_loc_title}],
                "Note": [
                    {
                        "Guid": "note-123",
                        "Title": "Base Title",
                        "Content": "User B Content",
                        "LocationId": 10,
                    }
                ],
            }

            # Note: process_databases uses the first file as base.
            # To simulate 3-way, we need to populate note_bases which usually happens when a note is first seen.
            # But here we are merging db1, then db2, then db3.

            self._create_test_db(db1_path, data1_note)
            self._create_test_db(db2_path, data2_note)
            self._create_test_db(db3_path, data3_note)

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path, db3_path])

            conn = sqlite3.connect(self.merged_db_path)
            cursor = conn.cursor()
            cursor.execute("SELECT Title, Content FROM Note WHERE Guid = 'note-123'")
            res = cursor.fetchone()
            conn.close()
            assert res[0] == "Base Title", f"Expected 'Base Title', got '{res[0]}'"
            assert res[1] == "Base Content", (
                f"Expected 'Base Content', got '{res[1]}'"
            )
            print("  ✓ Note dedup keeps first-in row")

            builtins.input = original_input

            # --- Case 3: UserMark Overlap detection ---
            print("\nTest 3: UserMark Overlap (Identity matching)...")
            builtins.input = lambda _: "1"  # Choose Option 1

            data1_um = {
                "Location": [{"LocationId": 20, "DocumentId": 123, "MepsLanguage": 0}],
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
            }
            data2_um = {
                "Location": [{"LocationId": 20, "DocumentId": 123, "MepsLanguage": 0}],
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
            }
            self._create_test_db(db1_path, data1_um)
            self._create_test_db(db2_path, data2_um)

            if path.exists(self.merged_db_path):
                remove(self.merged_db_path)
            self.process_databases([db1_path, db2_path])

            conn = sqlite3.connect(self.merged_db_path)
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM UserMark")
            um_count = cursor.fetchone()[0]
            conn.close()
            assert um_count == 1, (
                f"Expected 1 UserMark row after post-merge highlight dedupe, got {um_count}"
            )
            print("  ✓ UserMark post-merge highlight dedupe applied")

            builtins.input = original_input

            print("\n=== All Tests Passed! ===\n")

        finally:
            import time

            def secure_delete(path_to_del, is_dir=False):
                for _ in range(5):
                    try:
                        if is_dir:
                            if path.exists(path_to_del):
                                shutil.rmtree(path_to_del)
                        else:
                            if path.exists(path_to_del):
                                remove(path_to_del)
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
