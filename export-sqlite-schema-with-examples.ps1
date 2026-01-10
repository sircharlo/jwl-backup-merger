param (
    [Parameter(Mandatory = $true)]
    [string]$DbPath
)

$DbPath = Resolve-Path $DbPath
$folder = Split-Path $DbPath
$dbName = [System.IO.Path]::GetFileNameWithoutExtension($DbPath)
$out = Join-Path $folder "$dbName-schema-with-examples.txt"

Remove-Item $out -ErrorAction SilentlyContinue

# Tables
$tables = sqlite3 $DbPath "
SELECT name
FROM sqlite_master
WHERE type='table'
  AND name NOT LIKE 'sqlite_%';
"

foreach ($table in $tables) {
    if (-not $table.Trim()) { continue }

    "TABLE: $table" | Out-File $out -Append

    # Columns (name, type, pk)
    $cols = sqlite3 $DbPath "PRAGMA table_info([$table]);" |
    ForEach-Object {
        $p = $_ -split "\|"
        [PSCustomObject]@{
            Name = $p[1]
            Type = $p[2]
            IsPK = ($p[5] -ne "0")
        }
    }

    # Foreign keys
    $fks = sqlite3 $DbPath "PRAGMA foreign_key_list([$table]);" |
    ForEach-Object {
        $p = $_ -split "\|"
        [PSCustomObject]@{
            From      = $p[3]
            RefTable  = $p[2]
            RefColumn = $p[4]
        }
    }

    # First row
    $header = ($cols | ForEach-Object { $_.Name }) -join ","
    $rowRaw = sqlite3 $DbPath -csv "SELECT * FROM [$table] LIMIT 1;"

    if ($rowRaw) {
        $firstRow = ($header + "`n" + $rowRaw) | ConvertFrom-Csv
    }
    else {
        $firstRow = $null
    }

    foreach ($col in $cols) {
        $value = if ($firstRow) { $firstRow.$($col.Name) } else { "NULL" }

        $markers = @()
        if ($col.IsPK) {
            $markers += "PK"
        }

        $fk = $fks | Where-Object { $_.From -eq $col.Name }
        if ($fk) {
            $markers += "FK → $($fk.RefTable).$($fk.RefColumn)"
        }

        $markerText = if ($markers.Count) { " [" + ($markers -join ", ") + "]" } else { "" }

        "  $($col.Name) ($($col.Type))${markerText}: $value" |
        Out-File $out -Append
    }

    "" | Out-File $out -Append
}

Write-Host "Export completed : $out"
