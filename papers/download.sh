#!/usr/bin/env bash
# Re-fetch the bounded-gaps literature. Idempotent.
# PDFs land in papers/pdf/, arXiv LaTeX source extracts to papers/src/<id>/.
# Both are .gitignored.

set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$HERE/pdf" "$HERE/src"

dl() {  # dl <url> <dest>
  if [[ -f "$2" ]]; then
    echo "skip: $2 exists"
  else
    echo "fetch: $2"
    curl -sL --max-time 120 -o "$2" "$1"
  fi
}

# PDFs
dl "https://annals.math.princeton.edu/wp-content/uploads/annals-v179-n3-p07-p.pdf" "$HERE/pdf/zhang-2014-bounded-gaps.pdf"
dl "https://arxiv.org/pdf/1311.4600"     "$HERE/pdf/maynard-2015-small-gaps.pdf"
dl "https://arxiv.org/pdf/1407.4897"     "$HERE/pdf/polymath8b-2014-variants.pdf"
dl "https://arxiv.org/pdf/1410.8400"     "$HERE/pdf/granville-2015-survey.pdf"
dl "https://arxiv.org/pdf/math/0508185"  "$HERE/pdf/gpy-2009-primes-in-tuples-I.pdf"

# arXiv LaTeX source
dl "https://arxiv.org/e-print/1311.4600"    "$HERE/src/maynard-1311.4600.tar.gz"
dl "https://arxiv.org/e-print/1407.4897"    "$HERE/src/polymath8b-1407.4897.tar.gz"
dl "https://arxiv.org/e-print/1410.8400"    "$HERE/src/granville-1410.8400.tar.gz"
dl "https://arxiv.org/e-print/math/0508185" "$HERE/src/gpy-math-0508185.tar.gz"

# Extract (arXiv source may be tar.gz or a single .tex.gz)
cd "$HERE/src"
for f in *.tar.gz; do
  name="${f%.tar.gz}"
  if [[ -d "$name" ]]; then
    echo "skip extract: $name/ exists"
    continue
  fi
  mkdir -p "$name"
  if tar tzf "$f" >/dev/null 2>&1; then
    tar xzf "$f" -C "$name"
    echo "extracted tarball: $name"
  else
    gunzip -c "$f" > "$name/main.tex"
    echo "extracted single .tex: $name"
  fi
done

echo "done. inventory:"
du -sh "$HERE/pdf/"* "$HERE/src/"*/ 2>/dev/null | sort -k 2
