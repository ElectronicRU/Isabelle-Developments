---
name: isabelle-q
description: Interface with Isabelle/HOLCF through the Isabelle/Q (I/Q) MCP server — authenticate, read and edit .thy files via the live jEdit/PIDE session, inspect proof state, goals and diagnostics, and run proof exploration (sledgehammer, find_theorems, Isar try-steps) or the I/R REPL. Use whenever working with Isabelle theory files or proofs in this project.
---

# Isabelle/Q (I/Q)

I/Q exposes a running Isabelle/jEdit instance as an MCP server (`mcp__Isabelle_Q__*`).
All theory-file access goes through the live editor so PIDE proof state stays in sync.

**Authoritative references (read-only, available in this session):**
- `~/Isabelle/AutoCorrode/iq/README.md` — full tool surface, security model, params.
- `~/Isabelle/AutoCorrode/iq/iq_guidance.md` — proof-engineering style (surgical,
  incremental, Isar top-down with `sorry` scaffolds).
Consult them when a tool's behavior is unclear or you need detail beyond this skill.

## Golden rules

1. **Never** read or edit existing `.thy` files with `Read`/`Edit`/`Write`/`cat`/`sed`.
   Always use I/Q tools, so edits go through the live jEdit/PIDE buffer and stay in sync.
   (Filesystem tools are fine for `ROOT`, `.tex`, `.bib`, docs.)
   - **Exception — creating a brand-new `.thy`:** since I/Q has no copy-file primitive,
     you *may* create a new theory file with filesystem ops (e.g. `cp` an existing
     theory, or `Write` a fresh one) **provided you then `open_file` it in jEdit** before
     reading/editing it further. After that, the no-filesystem rule applies again: all
     subsequent edits go through I/Q. Never use filesystem ops on a `.thy` that is
     already open/tracked in jEdit.
   - **Exception — VCS operations:** `jj`/`git` commands that rewrite tracked `.thy`
     files on disk (`jj restore`/`revert`/`abandon`/`new`, `git checkout`/`restore`/
     `stash`, rebases, etc.) are fine — they're whole-file VCS ops, not hand edits. The
     editor is set to auto-reload changed buffers, so jEdit picks the new content up;
     **after any such op, re-sync and verify via I/Q** (`read_file` to confirm the buffer
     matches disk, `get_diagnostics`/`get_processing_status` to confirm it reprocessed)
     before making further I/Q edits. If a buffer didn't reload, reopen it / ask the user
     to reload rather than editing a stale buffer.
2. **Authenticate first** every session — see below. Nothing else works until you do.
3. **A file must be tracked before you can read/edit it.** `read_file`/`write_file`
   fail with "No file found" until you `open_file` it (it then becomes `tracked`).
4. **Explore before you commit.** Use `explore` (query=`proof`) to try a tactic
   non-invasively; only `write_file` once it works. Don't rewrite whole proof scripts —
   edit incrementally, 1–2 tactics at a time (see `iq_guidance.md`).
5. After an edit, **check it landed**: inspect the returned `file_summary`
   (`errors`, `commands_failed`) — `edits_failed=0` does NOT mean the theory is clean,
   since commands outside the edited range may have broken.

## Session start: authenticate

The token lives in the `IQ_AUTH_TOKEN` environment variable; you do not need the user
to supply it. Retrieve it and pass it (MCP args do **not** expand shell `$VAR`):

```
Bash:  printenv IQ_AUTH_TOKEN
mcp__Isabelle_Q__authenticate(token=<that literal value>)
```

Auth persists for the connection. If a later call returns "Not authenticated", just
re-authenticate.

## Tool catalog

### Files & documents
- `list_files` — list tracked files (`filter_open`, `filter_theory`).
- `open_file` — open/track an existing file; `create_if_missing=true` (+ optional
  `content`, `overwrite_if_exists`) to create. **Run before read/edit.**
- `read_file` — `mode="Line"` (`start_line`/`end_line`, 1-based, negatives count from
  end) or `mode="Search"` (`pattern` literal substring + `context_lines`).
- `write_file` — edit; `command` ∈ {`str_replace` (`old_str` unique + `new_str`),
  `insert` (`insert_line` + `new_str`), `line` (`start_line`/`end_line` + `new_str`)}.
  `check_context_scope` ∈ {`command`,`block`(default),`proof`,`file`} controls how wide
  it waits/rechecks. Returns `commands`, `edit_summary`, theory-scoped `file_summary`.
- `save_file` — persist one file or all modified buffers.
- `set_auto_save` — toggle/query auto-save (on by default → every `write_file` hits disk).
- `get_processing_status` — is the file done processing?
- `get_document_info` / `get_command_info` — theory/command status, errors, proof states.

### Introspection (read-only)
All take a `command_selection` ∈ {`current` (caret), `file_offset`(+`path`,`offset`),
`file_pattern`(+`path`,`pattern` — must match exactly once)}.
- `get_context_info` — command metadata + proof-context status + nested goal state. The
  workhorse for "what's the current goal here".
- `get_diagnostics` — `severity` ∈ {`error`,`warning`}, `scope` ∈ {`selection`,`file`}.
  Set `wait_until_processed=true` to force full processing first. Check `file_summary`.
- `get_sorry_positions` — locate `sorry` placeholders.
- `get_proof_blocks` — extract proof block(s); `scope` ∈ {`selection`,`file`}.
- `get_proof_context` — local `print_context` at a selection.
- `get_entities` — list lemmas/defs/funs with line+offset.
- `get_definitions` — `get_defs` for given names.
- `get_type_at_selection` — type introspection at a command/offset.
- `resolve_command_target` — resolve a selection to a concrete command.

### Non-invasive exploration
- `explore` — `query` ∈ {`proof`,`sledgehammer`,`find_theorems`} + `command_selection`
  (query is applied *after* the anchor command). For `proof`, `arguments` is the Isar
  text (e.g. `"by simp"`, `"apply blast"`) — requires `Isar_Explore.thy` imported. For
  `find_theorems`, `arguments` is the query (e.g. `"name:map"`); optional `max_results`.
  For `sledgehammer`, `arguments` is an optional prover list. Does not modify the file.

### I/R REPL (interactive Isar)
Call `repl_connect` once first. Then per named session (`repl` id):
- `repl_init`(`repl`,`theories`) / `repl_init_from_source` — create a REPL.
- `repl_step`(`repl`,`isar_text`) — run next step. **If a step fails, state is
  unchanged — do NOT `repl_back` to undo a failed step.**
- `repl_state` / `repl_show` / `repl_text` — inspect goal / session / accumulated text.
- `repl_back` (undo last *successful* step), `repl_truncate`, `repl_edit` + `repl_replay`.
- `repl_fork` / `repl_merge` — branch and inline sub-REPLs.
- `repl_sledgehammer` / `repl_find_theorems` — proof search on the current goal.
- `repl_list`, `repl_focus`, `repl_remove`, `repl_timeout`, `repl_raw` (raw ML).

## Common workflows

**Read a theory.** `open_file` → `read_file(mode=Line)` or `get_entities` for an overview.

**Inspect a goal.** `get_context_info(command_selection=file_pattern, pattern="lemma foo")`
to see the goal state; `get_proof_context` for local facts.

**Develop a proof in place.** `open_file` → put a `sorry` scaffold via `write_file` →
at each hole, `explore(query=proof, arguments="by ...")` until it works → `write_file`
the working step (`str_replace` the `sorry`) → re-check `file_summary` errors. Stuck?
`explore(query=sledgehammer)` or `explore(query=find_theorems, arguments="…")`.

**Heavier proof search.** Use the REPL: `repl_connect` → `repl_init` with the imports →
`repl_step` through the structure → `repl_sledgehammer` on hard goals → transcribe the
result back into the file with `write_file`.

## Gotchas
- `$VAR` is never expanded in MCP args — always pass literal values.
- "No file found matching …" → you forgot `open_file`.
- `read_file` requires `mode`; values are `"Line"`/`"Search"` (capitalized).
- A clean `edits_failed=0` can still sit on a broken theory — always read `file_summary`.
- Repo theories not in a `ROOT` (e.g. several HOLCF-extra/DataAnalyticsLang WIP files)
  still open fine individually via `open_file`.
