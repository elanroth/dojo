# Dojo — phone-evaluation PWA for the Lean dojo

An installable, offline-capable static page for checking that Lean says what it claims. Lean's
kernel checks proofs; it cannot check that a definition means the right thing. **Review** is that
human check, on a phone. The other rooms are the original evaluation harness.

Live: `https://elanroth.github.io/dojo/` · Plan of record: `maimonides/EXECPLAN.md` § P11, decision D39.

## What it is

| Room | Does | From |
|---|---|---|
| **Review** | The statement of a target theorem and every definition it rests on, leaves first; verdicts that expire when the Lean changes | — |
| **Read** | English prose beside the Lean; tap any term for its signature, location and toolchain | Folio |
| **Decide** | Four curated meaning-sensitive questions, graded with source citations | Pocket |
| **Map** | The real 14-node import DAG; tap a node for role, declaration count, imports | Atlas |
| **Carry** | Offline pack picker with a live size budget | Satchel |
| **Notes** | Type a note, attach a marked-up screenshot, export to Markdown | — |

Workbench (the Lean editor) was deliberately dropped.

Controls marked **◌** are not implemented; tapping one says what it would do. Nothing compiles,
dispatches a job, or syncs.

## How review works

Only the theorem's statement and the definitions it mentions, transitively, can make it say the
wrong thing, so those are the queue: 15 of 205 declarations for `ulm_theorem`. Definitions used only
in proofs are listed separately, and proofs are left to `lake build`.

A verdict (approve, flag with a note, or not sure) is appended to a ledger on the device and records
what was read. It goes stale when any of these changes: the declaration's Lean, the variables and
options in scope, anything in its dependency closure, the toolchain or the Mathlib revision. Comments,
docstrings, formatting and theorem proofs do not invalidate it.

The extractor reads source text and does not elaborate, so it over-approximates dependencies rather
than proving them. An instance joins the closure of anything its header mentions. It can still miss
what only elaboration reveals, such as an instance that does not name a reviewed definition.

## Update the review data

```bash
node scripts/build-review.mjs ../UlmsTheorem --slug elanroth/UlmsTheorem --target ulm_theorem
```

It refuses a source that is not a public repo at a clean, pushed commit. Then bump `CACHE` in `sw.js`
and deploy. Check an exported ledger on the Mac (exits 0 only if everything is approved and current):

```bash
node scripts/check-reviews.mjs dojo-reviews-2026-11-03.json
```

Run the tests:

```bash
node --test tests/review.test.mjs tests/ulm-data.test.mjs
```

## Content provenance

Everything is read from disk, not recalled:

- Project Lean — `~/pure/research/ulm` (`elanroth/UlmsTheorem`), toolchain `leanprover/lean4:v4.30.0-rc1`
- Mathlib signatures — that repo's pinned `.lake/packages/mathlib`, commit `389a421660`
- DAG — 14 files, 205 declarations, zero `sorry`, counted per file

**Publication rule: this site is public. Only `elanroth/UlmsTheorem` content may appear here.**
`ACM`, `acm-v2-proofs` and `acm-v3-proofs` are private repositories and are excluded. Re-check
visibility before quoting any new source.

## Privacy

Static page. No backend, no analytics, no telemetry. Notes and screenshots live in IndexedDB on the
device and never leave it. Review verdicts are stored the same way and leave only when exported, so
export them now and then: clearing Safari's site data deletes them. Export goes through the Web Share sheet, falling back to a download.

## Develop

```bash
python3 -m http.server 4173 --directory .
```

A service worker needs a real origin, so `file://` will not do. After changing any precached file,
**bump `CACHE` in `sw.js`** — the version string is what makes an update land on an installed app.

Regenerate icons (no image libraries required):

```bash
node scripts/make-icons.mjs
```

## Install on iPhone

Safari → Share → Add to Home Screen. Once installed it opens with no network.
