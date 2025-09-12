#!/bin/sh
# stats.sh — Compute formalisation statistics for the ICGT paper.
# Usage: ./stats.sh

DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$DIR" || exit 1

count_pat() {
    # grep -c returns 1 on no match; suppress that
    grep -c "$1" "$2" 2>/dev/null || true
}

echo "=== GP2-HOL Formalisation Statistics ==="
echo ""

# Theory files
files=$(ls *Script.sml 2>/dev/null)
nfiles=$(echo "$files" | wc -l | tr -d ' ')

echo "Theory files ($nfiles):"
echo "---"
total_lines=0
total_thm=0
total_triv=0
total_def=0
printf "%-40s %6s %6s %6s %6s\n" "File" "Lines" "Thm" "Triv" "Def"
printf "%-40s %6s %6s %6s %6s\n" "----" "-----" "---" "----" "---"
for f in $files; do
    lines=$(wc -l < "$f" | tr -d ' ')
    thm=$(count_pat "^Theorem" "$f")
    triv=$(count_pat "^Triviality" "$f")
    def=$(count_pat "^Definition" "$f")
    printf "%-40s %6s %6s %6s %6s\n" "$f" "$lines" "$thm" "$triv" "$def"
    total_lines=$((total_lines + lines))
    total_thm=$((total_thm + thm))
    total_triv=$((total_triv + triv))
    total_def=$((total_def + def))
done
printf "%-40s %6s %6s %6s %6s\n" "----" "-----" "---" "----" "---"
printf "%-40s %6s %6s %6s %6s\n" "TOTAL" "$total_lines" "$total_thm" "$total_triv" "$total_def"

echo ""
echo "=== Summary ==="
echo "Theories:                  $nfiles"
echo "Total lines:               $total_lines"
echo "Theorems:                  $total_thm"
echo "Trivialities:              $total_triv"
echo "Definitions:               $total_def"
echo "Theorems + Trivialities:   $((total_thm + total_triv))"

echo ""
echo "=== Case Study (Transitive_closureScript.sml) ==="
cs_lines=0; cs_thm=0; cs_triv=0; cs_def=0
if [ -f Transitive_closureScript.sml ]; then
    cs_lines=$(wc -l < Transitive_closureScript.sml | tr -d ' ')
    cs_thm=$(count_pat "^Theorem" Transitive_closureScript.sml)
    cs_triv=$(count_pat "^Triviality" Transitive_closureScript.sml)
    cs_def=$(count_pat "^Definition" Transitive_closureScript.sml)
    echo "Lines:                     $cs_lines"
    echo "Theorems:                  $cs_thm"
    echo "Trivialities:              $cs_triv"
    echo "Definitions:               $cs_def"
    echo "Theorems + Trivialities:   $((cs_thm + cs_triv))"
else
    echo "(file not found)"
fi

echo ""
echo "=== Formalisation excl. case study ==="
rest_lines=$((total_lines - cs_lines))
rest_thm=$((total_thm - cs_thm))
rest_triv=$((total_triv - cs_triv))
rest_def=$((total_def - cs_def))
rest_files=$((nfiles - 1))
echo "Theories:                  $rest_files"
echo "Lines:                     $rest_lines"
echo "Theorems:                  $rest_thm"
echo "Trivialities:              $rest_triv"
echo "Definitions:               $rest_def"
echo "Theorems + Trivialities:   $((rest_thm + rest_triv))"
