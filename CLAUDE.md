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
ROOT builds: `Top`, `FiniteCF`, `Bounded_Complete`, `Pointed_Profinite`, `Kleene_Logic`,
`Distributive`, `Filter_Sum`, `DI`, `Lattice_Complete`, `Algebraic_Lattice`, `Domain_Order`,
`Domain_Order_Derive`, `Directed`, `Definitions`, `MUB_Closure`, `Deflations`, `Koenigs`,
`LowerPD_Representation`, `UpperPD_Representation`, `Cpo_Topology`, `BagPD`, `MixPD`; session
`HOLCF-extra-Examples` (in `Examples/`) has the derivation use cases.
Not in ROOT: `Interval_Space`, `Attr_Space`, `Repro`/`Repro2` (minimal-repro scratch).

### `DataAnalyticsLang/` — a domain-theoretic data-analytics language
Depends on session `HOLCF-extra`. ROOT builds, in dependency order:
- foundations: `Typing` (an old generic lattice-subtyping locale, *not* the query
  language's type system), `Domain`, `Interp`, `Subdomain`, `Algebraic_Semi_Factor`, `Row`;
- datasets and levels of detail: `Slicer`, `Schema` (class of row types with schema rules),
  `Views` (row keys, key support), `Frame`, `LOD` (semi-factor LODs, small = finitary);
- values: `Value`, `Option_PD` (results: presence/absence in the Smyth powerdomain), `SplitPD`
  (partial datasets: Hoare rows + Smyth possible keys);
- rigid expression semantics: `Content_Law`, `Expr_Combinators`, `Aggregate`;
- the query language: `Ast` (untyped AST: Dim, Col, Lit, Call, Aggr, GroupBy, For, Where),
  `Ast_Semantics` (`asem`; `wf` checks arities and row-level WHERE only, no value typing);
- the extended semantics over partial datasets: `Split_Content` (selection, guards on splits),
  `Split_Semantics` (sound, monotone and continuous combinators), `Key_Mix` (guard contents as key
  mixes in `HOLCF-extra/MixPD`), `Split_Csem` (extended semantics factors through contents, and the
  content semantics is monotone; all combinators incl. aggregates), `Split_Exact` (exactness at saturated
  datasets without row guards), `Ast_Split_Semantics` (`asem_ext`; exact on `WHERE`-free ASTs).

Not in ROOT: `Separated_Principal`, `SlicerToy`. A type system for the AST and the SQL lowering
are planned, not started. Theme: powerdomains for partial information / approximate queries
(cf. the Buneman–Jung–Ohori & Libkin papers indexed below).

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
