#!/usr/bin/env bash
# Assemble the Pages site from Isabelle's browser_info.
#   usage: site.sh BROWSER_INFO_DIR OUT_DIR
# Keeps the sessions of chapter "Developments" only.  Theories and ML files of the Isabelle
# distribution (Pure, HOL, HOLCF, HOL-Library, HOLCF-Library, HOL-Eisbach, ...) are linked to
# the Isabelle website instead of being published here: browser_info presents distribution
# theories a session loads itself (e.g. HOL-Library.FSet) as local copies.
set -euo pipefail

info=$1
out=$2
base=https://isabelle.in.tum.de/website-Isabelle2025-2/dist/library

rm -rf "$out"
mkdir -p "$out"
cp -r "$info/fonts" "$out/"
cp -r "$info/Developments" "$out/"

for dir in "$out"/Developments/*/; do
  # Drop local copies of distribution theories and ML files, and their index entries.
  sed -E -i '/<li><a href="[A-Za-z-]+\.[A-Za-z0-9_'"'"']+\.html">/d' "$dir/index.html"
  find "$dir" -maxdepth 1 -name '*.*.html' -delete
  rm -rf "$dir/ISABELLE_HOME"
done

find "$out/Developments" -name '*.html' -print0 | xargs -0 sed -E -i \
  -e 's#href="\.\./\.\./(Pure|HOL)/#href="'"$base"'/\1/#g' \
  -e 's#href="(\.\./[A-Za-z_-]+/)?(HOL-[A-Za-z_]+|HOLCF-Library)\.([^"#]+)\.html#href="'"$base"'/HOL/\2/\3.html#g' \
  -e 's#href="(\.\./[A-Za-z_-]+/)?ISABELLE_HOME/src/HOL/Eisbach/#href="'"$base"'/HOL/HOL-Eisbach/ISABELLE_HOME/src/HOL/Eisbach/#g' \
  -e 's#href="(\.\./[A-Za-z_-]+/)?ISABELLE_HOME/src/HOL/Library/#href="'"$base"'/HOL/HOL-Library/ISABELLE_HOME/src/HOL/Library/#g' \
  -e 's#href="(\.\./[A-Za-z_-]+/)?ISABELLE_HOME/src/HOL/HOLCF/Library/#href="'"$base"'/HOL/HOLCF-Library/ISABELLE_HOME/src/HOL/HOLCF/Library/#g'

cat > "$out/index.html" <<'EOF'
<!doctype html><html><head><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=Developments/index.html">
<title>Isabelle Developments</title></head>
<body><p><a href="Developments/index.html">Isabelle Developments</a></p></body></html>
EOF
touch "$out/.nojekyll"
