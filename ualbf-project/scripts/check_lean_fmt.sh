#!/bin/bash
set -e
BAD_FILES=0
cd "$(dirname "$0")/../lean4-proofs"

while IFS= read -r file; do
    awk '
        { 
        sub(/[ \t]+$/, "");  # Remove trailing whitespace
        gsub(/\t/, "    ");  # Replace tabs with 4 spaces
        print
        }
    ' "$file" > "$file.fmt"
    
    if ! diff -u "$file" "$file.fmt" > /dev/null; then
        echo "Formatting error in $file"
        BAD_FILES=1
    fi
    rm "$file.fmt"
done < <(find . -type d -name ".lake" -prune -o -type f -name "*.lean" -print)

if [ $BAD_FILES -ne 0 ]; then
    echo "Lean formatting checks failed. Please fix the files listed above."
    exit 1
fi

echo "Lean formatting checks passed."
