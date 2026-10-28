# Isabelle/HOLCF Developments

Alex's Isabelle/HOLCF developments. Two sessions, both built on `HOLCF`.

## CRITICAL: editing theory files

Two modes; find out which one is live before touching a `.thy`.

**Headless (ic2)** — when no jEdit is running and an `isabelle ic2` server is up
(`isabelle ic2 server status`). ic2 is a persistent PIDE server that rechecks files
from disk, so edit `.thy` files with the filesystem tools, keep them pure ASCII
(`\<forall>` escapes, never raw Unicode), and check with
`isabelle ic2 check --command-timeout 120 /abs/X.thy` + `isabelle ic2 check status`.
Start it from this directory with
`isabelle ic2 server start --daemon --mcp -l HOLCF -d HOLCF-extra -d DataAnalyticsLang`.
Docs: `~/Isabelle/AutoCorrode/ic2/README.md` and `SKILL.md`.

**Interactive (jEdit + I/Q)** — when jEdit is running: **NEVER** read/write/create
`.thy` files with the filesystem tools (`Read`/`Edit`/`Write`/`Bash cat`).
**ALWAYS** use the **Isabelle/Q (I/Q) MCP server** so edits go through the live
jEdit instance and PIDE state stays in sync. Filesystem tools are fine for non-`.thy`
files (`ROOT`, `.tex`, `.bib`, docs).

- No authentication needed: a hook applies the I/Q token. If I/Q hangs or the
  connection closes, ask the user to run `/mcp reconnect Isabelle_Q`.
- REPL tools (`repl_*`) require `repl_connect` first.
- Proof-engineering workflow & style: follow
  `~/Isabelle/AutoCorrode/iq/iq_guidance.md` (surgical, structured, incremental
  apply-style 1-2 tactics at a time; Isar top-down with `sorry` scaffolding).
  Full tool reference: `~/Isabelle/AutoCorrode/iq/README.md`.

## Repository layout

### `HOLCF-extra/` — HOLCF library extensions
ROOT builds: `Top`, `FiniteCF`, `Bounded_Complete`, `Directed`.
Other theories present (WIP / not yet in ROOT): `Cpo_Topology`, `Interval_Space`,
`Attr_Space`, `Koenigs`, `LowerPD_Representation`, `UpperPD_Representation`,
`Compact_Cfun`, `Definitions`, `Repro`/`Repro2` (minimal-repro scratch).

### `DataAnalyticsLang/` — a domain-theoretic data-analytics language
ROOT builds: `Typing`, `Domain`, `Interp`. Depends on session `HOLCF-extra`.
Other theories present (WIP): `Subdomain`, `StrongIdeal`, `Row`, `Valsets`.
Theme: powerdomains for partial information / approximate queries (cf. the
Buneman–Jung–Ohori & Libkin papers indexed below).

## Building
`isabelle build -d DataAnalyticsLang -d HOLCF-extra DataAnalyticsLang` (or per-session; there is
no top-level `ROOT`, so `-d .` fails). Building alongside a live jEdit/PIDE session can exhaust
memory; close jEdit (and stop the ic2 server) first. Add `-o document=pdf` to also build the PDF
documents into `output/` (the ROOTs no longer turn them on). HOLCF must be available as a heap image.
CI (`.github/workflows/html.yml`) builds both sessions with HTML and PDF on every push to `main` and
deploys them to https://electronicru.github.io/Isabelle-Developments/.

## Housekeeping
Working tree contains editor cruft — emacs autosave `#Foo.thy#` and backup
`Foo.thy~` files. These are not tracked / not authoritative; ignore them when
reasoning about sources, and prefer a `.gitignore` for them.

## Reference material (background reading, not code)
- `~/Documents/Articles/INDEX.md` — papers (domain theory/powerdomains, posets &
  LCA algorithms, effects/control, type theory, interaction combinators, …).
- `~/Documents/books/CS/INDEX.md` — books (Huffman's *HOLCF '11* thesis, Gunter &
  Escardó on powerdomains, CLRS, architecture texts).
- Isabelle 2025-2 sources (read-only): `~/Isabelle/Distrib/Isabelle2025-2`.
