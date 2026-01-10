import sqlite3
import os

db_path = 'working/merged.db'
if not os.path.exists(db_path):
    print(f"File not found: {db_path}")
    exit(1)

conn = sqlite3.connect(db_path)
cursor = conn.cursor()

tables = ['TagMap', 'PlaylistItem', 'Tag']
with open('schema_dump.txt', 'w') as f:
    for table in tables:
        f.write(f"TABLE: {table}\n")
        cursor.execute(f"PRAGMA table_info({table})")
        cols = cursor.fetchall()
        for col in cols:
            f.write(f"  {col[1]} ({col[2]}) PK={col[5]}\n")
        f.write("\n")

        cursor.execute(f"SELECT sql FROM sqlite_master WHERE name='{table}'")
        sql = cursor.fetchone()
        if sql:
            f.write(f"SQL: {sql[0]}\n\n")
        f.write("-" * 40 + "\n\n")

print("Schema dumped to schema_dump.txt")
