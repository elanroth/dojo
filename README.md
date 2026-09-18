# Dojo — phone-evaluation PWA for the Lean dojo

An installable, offline-capable static page for answering one question: **is the Lean dojo good
enough on a phone to be worth building properly?**

Live: `https://elanroth.github.io/dojo/` · Plan of record: `maimonides/EXECPLAN.md` § P11, decision D39.

## What it is

Four rooms, synthesised from the five P10 design studies:

| Room | Does | From |
|---|---|---|
| **Read** | English prose beside the Lean; tap any term for its signature, location and toolchain | Folio |
| **Decide** | Four curated meaning-sensitive questions, graded with source citations | Pocket |
| **Map** | The real 14-node import DAG; tap a node for role, declaration count, imports | Atlas |
| **Carry** | Offline pack picker with a live size budget | Satchel |
| **Notes** | Type a note, attach a marked-up screenshot, export to Markdown | — |

Workbench (the Lean editor) was deliberately dropped.

Controls marked **◌** are not implemented; tapping one says what it would do. Nothing compiles,
dispatches a job, or syncs.

## Content provenance

Everything is read from disk, not recalled:

- Project Lean — `~/pure/research/ulm` (`elanroth/UlmsTheorem`), toolchain `leanprover/lean4:v4.30.0-rc1`
- Mathlib signatures — that repo's pinned `.lake/packages/mathlib`, commit `389a421660`
- DAG — 14 files, 173 declarations, zero `sorry`, counted per file

**Publication rule: this site is public. Only `elanroth/UlmsTheorem` content may appear here.**
`ACM`, `acm-v2-proofs` and `acm-v3-proofs` are private repositories and are excluded. Re-check
visibility before quoting any new source.

## Privacy

Static page. No backend, no analytics, no telemetry. Notes and screenshots live in IndexedDB on the
device and never leave it. Export goes through the Web Share sheet, falling back to a download.

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
