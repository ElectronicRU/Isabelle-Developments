# Isabelle/HOLCF Developments

Alex's Isabelle/HOLCF developments. Two sessions, both built on `HOLCF`.

## CRITICAL: editing theory files

**NEVER** read/write/create Isabelle theory (`.thy`) files with the filesystem
tools (`Read`/`Edit`/`Write`/`Bash cat`). **ALWAYS** use the **Isabelle/Q (I/Q)
MCP server** so edits go through the live jEdit instance and PIDE state stays in
sync. Filesystem tools are fine for non-`.thy` files (`ROOT`, `.tex`, `.bib`, docs).

- First call each session: `mcp__Isabelle_Q__authenticate`. Pass the **literal
  value** of `$IQ_AUTH_TOKEN` (shell `$VAR` is NOT expanded inside MCP args).
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
Other theories present (WIP): `Subdomain`, `StrongIdeal`, `ValsetBase`, `Valsets`.
Theme: powerdomains for partial information / approximate queries (cf. the
Buneman–Jung–Ohori & Libkin papers indexed below).

## Building
`isabelle build -d DataAnalyticsLang -d HOLCF-extra DataAnalyticsLang` (or per-session; there is
no top-level `ROOT`, so `-d .` fails). Building alongside a live jEdit/PIDE session can exhaust
memory; close jEdit first. Both
produce PDF documents into `output/`. HOLCF must be available as a heap image.

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
