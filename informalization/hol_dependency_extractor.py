#!/usr/bin/env python3
"""
hol_dependency_extractor.py  —  v5  (imports‑aware)

Features
========
1. Build a cached index of all theorems & definitions in a HOL Light tree:
      • store entire let‑binding block
      • store first back‑quoted formal statement
2. Extract dependencies from
      • a whole .ml file    (--deps FILE.ml)
      • a code fragment     (--from-text FILE | --from-string "…")
3. Restrict dependency reporting to specific imported files
      (--imports Library/binomial.ml Library/iter.ml)
4. Pretty text (Markdown) or JSON output
5. Choose what to display for each dependency: full block (default) or just
   the formal statement  (--show formal)

Typical use
-----------
# build index once
python hol_dependency_extractor.py --build-index /path/to/HOLLight

# deps for a file, but only those living in Library/binomial.ml
python hol_dependency_extractor.py --deps 100/combinations.ml \
       --imports Library/binomial.ml --show formal
"""

import argparse
import json
import os
import pickle
import re
import sys
from typing import Dict, Set

CACHE_FILE = ".hol_index.pkl"

# ----------------------------------------------------------------------
# Regexes
# ----------------------------------------------------------------------
BLOCK_RE = re.compile(r"(let\s+([A-Za-z0-9_']+)\s*=([\s\S]*?));;", re.DOTALL)
BACKTICK_RE = re.compile(r"`([^`]+)`", re.DOTALL)
DEF_FUNS = ("new_definition", "define")

# ----------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------
def classify_block(block: str) -> str:
    """Return 'theorem' | 'definition' | ''."""
    body = block.split("=", 1)[1]
    if "prove" in body:
        return "theorem"
    if any(f in body for f in DEF_FUNS):
        return "definition"
    return ""


def extract_blocks(path: str):
    """Return two dicts (theorems, definitions) from one .ml file."""
    try:
        text = open(path, encoding="utf-8", errors="ignore").read()
    except Exception as e:
        sys.stderr.write(f"[warn] Could not read {path}: {e}\n")
        return {}, {}

    rel = os.path.relpath(path)
    thm_idx, def_idx = {}, {}
    for full, name, _ in BLOCK_RE.findall(text):
        if len(name) == 1:                     # skip one‑letter names
            continue
        kind = classify_block(full)
        m = BACKTICK_RE.search(full)
        if not m:                              # require a formal term
            continue
        formal = " ".join(m.group(1).split())  # squash whitespace
        meta = {"file": rel, "block": full + ";;", "formal": formal}
        if kind == "theorem":
            thm_idx[name] = meta
        elif kind == "definition":
            def_idx[name] = meta
    return thm_idx, def_idx


def build_index(root: str) -> Dict[str, Dict[str, Dict[str, str]]]:
    thm_idx, def_idx = {}, {}
    for subdir, _, files in os.walk(root):
        for fn in files:
            if fn.endswith(".ml"):
                t, d = extract_blocks(os.path.join(subdir, fn))
                thm_idx.update(t)
                def_idx.update(d)
    return {"theorems": thm_idx, "definitions": def_idx}


def restrict_index(index: Dict, allowed: list[str]) -> Dict:
    """Return copy of index containing only entries whose file is allowed."""
    if not allowed:
        return index
    new = {"theorems": {}, "definitions": {}}
    for kind in ("theorems", "definitions"):
        for name, meta in index[kind].items():
            f = meta["file"]
            for allow in allowed:
                if allow in f or allow in os.path.basename(f):
                    new[kind][name] = meta
    return new


# ----------------------------------------------------------------------
# Dependency extraction
# ----------------------------------------------------------------------
def _scan(text: str, index: Dict, kind: str):
    out = {}
    for name, meta in index[kind].items():
        if re.search(rf"\b{name}\b", text):
            out[name] = meta
    return out


def deps_from_text(text: str, index: Dict):
    return {"theorems": _scan(text, index, "theorems"),
            "definitions": _scan(text, index, "definitions")}

# ----------------------------------------------------------------------
# Output helpers
# ----------------------------------------------------------------------
def _emit(name: str, meta: Dict, show: str):
    content = meta["block"] if show == "block" else meta["formal"]
    tag = "hol" if show == "block" else ""
    indented = "\n".join("  " + l for l in content.splitlines())
    return f"- **{name}** *(in `{meta['file']}`)*\n\n```{tag}\n{indented}\n```\n"


def print_report(title: str, deps: Dict, show: str):
    print(f"\n### Dependencies for {title}\n")
    if not deps["theorems"] and not deps["definitions"]:
        print("_No dependencies detected._")
        return

    if deps["theorems"]:
        print("#### Theorems\n")
        for n, meta in sorted(deps["theorems"].items()):
            print(_emit(n, meta, show))
    if deps["definitions"]:
        print("#### Definitions\n")
        for n, meta in sorted(deps["definitions"].items()):
            print(_emit(n, meta, show))


# ----------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="HOL Light dependency extractor (v5)")
    # indexing
    ap.add_argument("--build-index", metavar="HOL_ROOT",
                    help="Build & cache index from this HOL Light tree")
    ap.add_argument("--rebuild", action="store_true",
                    help="Force rebuild even if cache exists")
    # dependency sources
    ap.add_argument("--deps", metavar="FILE.ml",
                    help="Analyse dependencies of a full .ml file")
    ap.add_argument("--from-text", metavar="FILE",
                    help="Analyse dependencies of code fragment in FILE ('-' for stdin)")
    ap.add_argument("--from-string", metavar="STR",
                    help="Analyse dependencies of STR")
    # filters & output
    ap.add_argument("--imports", metavar="PATH", nargs="+",
                    help="Only include deps from these files (space or comma separated)")
    ap.add_argument("--json", action="store_true",
                    help="Emit JSON instead of pretty text")
    ap.add_argument("--show", choices=["block", "formal"], default="block",
                    help="Show full block (default) or just formal statement")
    args = ap.parse_args()

    # ------------------------------------------------------------------ index
    if args.build_index:
        sys.stderr.write("[info] Building index …\n")
        index_all = build_index(args.build_index)
        pickle.dump(index_all, open(CACHE_FILE, "wb"))
        sys.stderr.write(f"[info] Indexed "
                         f"{len(index_all['theorems'])} theorems + "
                         f"{len(index_all['definitions'])} definitions → {CACHE_FILE}\n")
    if not os.path.exists(CACHE_FILE):
        sys.stderr.write("ERROR: cache missing. Run with --build-index first.\n")
        sys.exit(1)
    index_all = pickle.load(open(CACHE_FILE, "rb"))

    # ------------------------------------------------------------------ import filter
    allowed_files = set()
    if args.imports:
        for token in args.imports:
            allowed_files.update([p.strip() for p in token.split(",") if p.strip()])
    index = restrict_index(index_all, allowed_files)

    # ------------------------------------------------------------------ choose source text
    source_text = None
    title = ""
    if args.deps:
        source_text = open(args.deps, encoding="utf-8", errors="ignore").read()
        title = f"`{args.deps}`"
    elif args.from_text:
        if args.from_text == "-":
            source_text = sys.stdin.read()
            title = "stdin"
        else:
            source_text = open(args.from_text, encoding="utf-8").read()
            title = f"fragment `{args.from_text}`"
    elif args.from_string:
        source_text = args.from_string
        title = "provided string"
    else:
        ap.error("Specify one of --deps, --from-text, --from-string")

    # ------------------------------------------------------------------ extract + output
    deps = deps_from_text(source_text, index)
    if args.json:
        json.dump(deps, sys.stdout, indent=2)
    else:
        print_report(title, deps, show=args.show)


if __name__ == "__main__":
    main()
