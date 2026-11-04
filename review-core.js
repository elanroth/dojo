/* Review logic with no DOM and no storage, shared by the app and
 * scripts/check-reviews.mjs so the phone and the Mac cannot disagree.
 *
 * The ledger is append-only: a new verdict never rewrites an old one, and the
 * latest event for a declaration decides its state. */

export const LEDGER_FORMAT = 'dojo-review-ledger/1';
const VERDICTS = new Set(['approved', 'flagged', 'unsure']);

export const indexDecls = data => new Map(data.decls.map(d => [d.name, d]));

/* Own hashes of everything this declaration rests on: the record of what was
 * actually read, which later says exactly what changed. */
export function closureHashes(decl, byName) {
  return Object.fromEntries(decl.closure.map(n => [n, byName.get(n)?.ownHash ?? null]));
}

/* A new verdict must outrank every earlier one for its declaration, even if the
 * device clock has since moved backwards. */
export function nextTimestamp(events, repo, declName, now = Date.now()) {
  let t = now;
  for (const e of events) if (e.repo === repo && e.decl === declName && e.at >= t) t = e.at + 1;
  return t;
}

export function makeEvent(decl, verdict, note, data, at = Date.now(), { checkedSource = false } = {}) {
  if (!VERDICTS.has(verdict)) throw new Error('unknown verdict: ' + verdict);
  const text = (note || '').trim();
  if (verdict === 'flagged' && !text) throw new Error('a flag needs a note saying what is wrong');
  return {
    id: 'v' + at + '-' + Math.random().toString(36).slice(2, 8),
    repo: data.repo, decl: decl.name, verdict, note: text, at, checkedSource: !!checkedSource,
    ownHash: decl.ownHash, deepHash: decl.deepHash,
    closure: closureHashes(decl, indexDecls(data)),
    code: decl.code, scope: decl.scope,
    rev: data.rev, toolchain: data.toolchain, mathlib: data.mathlib,
  };
}

export function latestEvents(events, repo) {
  const out = new Map();
  for (const e of events) {
    if (e.repo !== repo) continue;
    const cur = out.get(e.decl);
    if (!cur || e.at > cur.at || (e.at === cur.at && e.id > cur.id)) out.set(e.decl, e);
  }
  return out;
}

/* Why a past verdict no longer covers the current source, or null if it does. */
export function staleReason(decl, ev, data) {
  const reasons = [];
  if (ev.ownHash !== decl.ownHash) reasons.push({ type: 'own' });
  if (ev.deepHash !== decl.deepHash) {
    const byName = indexDecls(data);
    const now = closureHashes(decl, byName);
    const was = ev.closure || {};
    const changed = [...new Set([...Object.keys(now), ...Object.keys(was)])]
      .filter(n => now[n] !== was[n]).sort();
    if (changed.length || ev.ownHash === decl.ownHash) reasons.push({ type: 'deps', changed });
  }
  if (ev.toolchain !== data.toolchain) reasons.push({ type: 'toolchain', from: ev.toolchain, to: data.toolchain });
  if (ev.mathlib !== data.mathlib) reasons.push({ type: 'mathlib', from: ev.mathlib, to: data.mathlib });
  return reasons.length ? reasons : null;
}

export function statusOf(decl, latest, data) {
  const ev = latest.get(decl.name);
  if (!ev) return { state: 'unreviewed', event: null };
  const stale = staleReason(decl, ev, data);
  if (ev.verdict === 'unsure') return { state: 'unsure', event: ev, stale };
  if (stale) return { state: 'stale', event: ev, stale };
  return { state: ev.verdict, event: ev };
}

/* The declarations behind a target, leaves first, the target last. */
export function trustBase(target, data) {
  const byName = indexDecls(data);
  const t = byName.get(target);
  if (!t) throw new Error('target not in data: ' + target);
  const missing = t.closure.filter(n => !byName.has(n));
  if (missing.length) throw new Error('closure names missing from data: ' + missing.join(', '));
  return [...t.closure.map(n => byName.get(n)), t];
}

export function summarize(target, events, data) {
  const latest = latestEvents(events, data.repo);
  const base = trustBase(target, data).map(decl => ({ decl, status: statusOf(decl, latest, data) }));
  const count = s => base.filter(x => x.status.state === s).length;
  const approved = base.filter(x => x.status.state === 'approved');
  const counts = {
    total: base.length, approved: approved.length, flagged: count('flagged'),
    stale: count('stale'), unsure: count('unsure'), unreviewed: count('unreviewed'),
    imported: approved.filter(x => x.status.event.imported).length,
    sourced: approved.filter(x => x.status.event.checkedSource).length,
    sorry: base.filter(x => x.decl.hasSorry).length,
  };
  return { base, counts, trusted: counts.approved === counts.total && !counts.sorry };
}

/* What to read next: anything changed first, then new work, then the ones you
 * were unsure of, oldest first. Flagged items wait for a code change, so they are
 * not offered. Mid-session, `includeUnsure: false` ends the run instead of
 * circling back through items you already passed on. */
export function nextInQueue(target, events, data, { after = null, includeUnsure = true } = {}) {
  const items = summarize(target, events, data).base.filter(x => x.decl.name !== after);
  const changed = items.find(x => x.status.state === 'stale' || (x.status.state === 'unsure' && x.status.stale));
  if (changed) return changed.decl;
  const fresh = items.find(x => x.status.state === 'unreviewed');
  if (fresh) return fresh.decl;
  if (!includeUnsure) return null;
  const unsure = items.filter(x => x.status.state === 'unsure')
    .sort((a, b) => a.status.event.at - b.status.event.at);
  return unsure.length ? unsure[0].decl : null;
}

const MAX_FUTURE_MS = 24 * 3600 * 1000;
const withoutImportMark = ({ imported, ...e }) => JSON.stringify(e);

/* Imported files are untrusted input. Keep only well-formed events, refuse future
 * dates (one could outrank every later verdict), and refuse an id that appears
 * twice with different content, since either copy could be the wrong one. */
export function parseLedger(json, now = Date.now()) {
  const raw = typeof json === 'string' ? JSON.parse(json) : json;
  if (!raw || raw.format !== LEDGER_FORMAT || !Array.isArray(raw.events)) {
    throw new Error('not a dojo review ledger');
  }
  const str = v => typeof v === 'string';
  const opt = v => v === undefined || str(v);
  const wellFormed = e => e && str(e.id) && str(e.repo) && str(e.decl) &&
    VERDICTS.has(e.verdict) && Number.isSafeInteger(e.at) && e.at <= now + MAX_FUTURE_MS &&
    str(e.ownHash) && str(e.deepHash) &&
    opt(e.note) && opt(e.code) && opt(e.rev) && opt(e.toolchain) && (e.mathlib === null || opt(e.mathlib)) &&
    (e.scope === undefined || (Array.isArray(e.scope) && e.scope.every(str))) &&
    (e.closure === undefined || (e.closure && typeof e.closure === 'object' && !Array.isArray(e.closure)));
  const good = raw.events.filter(wellFormed);
  const byId = new Map();
  const conflicted = new Set();
  for (const e of good) {
    const seen = byId.get(e.id);
    if (seen && withoutImportMark(seen) !== withoutImportMark(e)) conflicted.add(e.id);
    else if (!seen) byId.set(e.id, e);
  }
  for (const id of conflicted) byId.delete(id);
  return { events: [...byId.values()], skipped: raw.events.length - good.length, conflicts: conflicted.size };
}

/* Split parsed events against what is stored. Nothing already stored is replaced. */
export function planImport(incoming, stored) {
  const have = new Map(stored.map(e => [e.id, e]));
  const fresh = [];
  let same = 0, conflicts = 0;
  for (const e of incoming) {
    const old = have.get(e.id);
    if (!old) fresh.push({ ...e, imported: true });
    else if (withoutImportMark(old) === withoutImportMark(e)) same++;
    else conflicts++;
  }
  return { fresh, same, conflicts };
}

export const serializeLedger = (events, data, exportedAt) => JSON.stringify({
  format: LEDGER_FORMAT, repo: data.repo, rev: data.rev, exportedAt,
  events: [...events].sort((a, b) => a.at - b.at),
}, null, 1) + '\n';

/* Line diff for showing what changed since a verdict. An LCS is plenty at the
 * size of one declaration. */
export function lineDiff(before, after) {
  const a = before.split('\n'), b = after.split('\n');
  const dp = Array.from({ length: a.length + 1 }, () => new Array(b.length + 1).fill(0));
  for (let i = a.length - 1; i >= 0; i--) {
    for (let j = b.length - 1; j >= 0; j--) {
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const out = [];
  let i = 0, j = 0;
  while (i < a.length || j < b.length) {
    if (i < a.length && j < b.length && a[i] === b[j]) { out.push({ t: ' ', s: a[i] }); i++; j++; }
    else if (i < a.length && (j === b.length || dp[i + 1][j] >= dp[i][j + 1])) out.push({ t: '-', s: a[i++] });
    else out.push({ t: '+', s: b[j++] });
  }
  return out;
}

export function describeStale(reasons) {
  return reasons.map(r => {
    if (r.type === 'own') return 'Its Lean or the assumptions in scope changed.';
    if (r.type === 'deps') return r.changed.length
      ? 'Depends on something that changed: ' + r.changed.join(', ') + '.'
      : 'Something it depends on changed.';
    if (r.type === 'toolchain') return 'Lean toolchain changed: ' + r.from + ' to ' + r.to + '.';
    if (r.type === 'mathlib') return 'Mathlib changed: ' + String(r.from).slice(0, 10) + ' to ' + String(r.to).slice(0, 10) + '.';
    return 'Changed.';
  });
}
