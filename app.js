import { MATHLIB_REV, TOOLCHAIN, REPO, GLOSSARY, READING, QUESTIONS, DAG, THEOREM, PACKS } from './data.js';
import { REVIEW } from './review-data.js';
import { SOURCES } from './review-sources.js';
import {
  describeStale, latestEvents, lineDiff, makeEvent, nextInQueue, nextTimestamp, parseLedger, planImport,
  serializeLedger, statusOf, summarize,
} from './review-core.js';

const $ = s => document.querySelector(s);
const el = (t, c, x) => { const n = document.createElement(t); if (c) n.className = c; if (x != null) n.textContent = x; return n; };
const esc = s => String(s).replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

let ROOM = 'review';
let NOTES = [];

const ROOMS = {
  review: { title: REVIEW.targets[0], eyebrow: 'Checking' },
  read:   { title: 'Ulm invariants',     eyebrow: 'Read' },
  decide: { title: 'Practice questions', eyebrow: 'Decide' },
  map:    { title: 'Ulm dependency map', eyebrow: 'Map' },
  carry:  { title: 'Offline satchel',    eyebrow: 'Carry' },
  notes:  { title: 'Change requests',    eyebrow: 'Notes' },
};

/* ───────────────────────── storage: IndexedDB ─────────────────────────
 * Notes, screenshot blobs and review verdicts live on the device. Nothing leaves
 * the phone unless exported: this is a static site with no backend, by design. */
const DB_NAME = 'ulm-dojo', STORE = 'notes', VERDICT_STORE = 'verdicts';
let _open = null;
function idb() {
  if (_open) return _open;
  _open = new Promise((res, rej) => {
    const r = indexedDB.open(DB_NAME, 2);
    r.onupgradeneeded = () => {
      const stores = r.result.objectStoreNames;
      if (!stores.contains(STORE)) r.result.createObjectStore(STORE, { keyPath: 'id' });
      if (!stores.contains(VERDICT_STORE)) r.result.createObjectStore(VERDICT_STORE, { keyPath: 'id' });
    };
    r.onblocked = () => toast('Close other Dojo windows so its storage can update.', 6000);
    r.onsuccess = () => {
      const db = r.result;
      db.onversionchange = () => { db.close(); _open = null; };
      db.onclose = () => { _open = null; };
      res(db);
    };
    r.onerror = () => { _open = null; rej(r.error); };
  });
  return _open;
}
function runTx(db, mode, fn, store) {
  return new Promise((res, rej) => {
    const t = db.transaction(store, mode);
    const out = fn(t.objectStore(store));
    const failed = e => rej(t.error || (e && e.target && e.target.error) || new Error('storage error'));
    t.onabort = failed;
    t.onerror = failed;
    t.oncomplete = () => res(out && out.result !== undefined ? out.result : out);
  });
}
async function tx(mode, fn, store = STORE) {
  try {
    return await runTx(await idb(), mode, fn, store);
  } catch (e) {
    // WebKit can drop the connection while the app is suspended.
    if (e && e.name === 'InvalidStateError') { _open = null; return runTx(await idb(), mode, fn, store); }
    throw e;
  }
}
const loadNotes = () => tx('readonly', s => s.getAll());
const putNote   = n  => tx('readwrite', s => s.put(n));
const dropNote  = id => tx('readwrite', s => s.delete(id));
const loadVerdicts = () => tx('readonly', s => s.getAll(), VERDICT_STORE);
const putVerdicts  = es => tx('readwrite', s => { es.forEach(e => s.put(e)); }, VERDICT_STORE);

/* ───────────────────────── chrome ───────────────────────── */
function toast(html, ms = 3400) {
  const old = $('.toast'); if (old) old.remove();
  const t = el('div', 'toast'); t.innerHTML = html;
  document.body.appendChild(t);
  setTimeout(() => t.isConnected && t.remove(), ms);
}
/* Nothing that isn't built silently does nothing — it says what it would do. */
const stub = (what, would) => toast('<b>' + esc(what) + '</b><br>' + esc(would) + ' — not built yet.');

function sheet(build) {
  const scrim = el('div', 'scrim'), s = el('div', 'sheet');
  s.appendChild(el('div', 'grab'));
  const onKey = e => { if (e.key === 'Escape') close(); };
  const close = () => { scrim.remove(); document.removeEventListener('keydown', onKey); };
  build(s, close);
  scrim.appendChild(s);
  scrim.addEventListener('click', e => { if (e.target === scrim) close(); });
  document.addEventListener('keydown', onKey);
  document.body.appendChild(scrim);
}
const provRow = (dl, k, v) => { const d = el('div'); d.appendChild(el('dt', null, k)); d.appendChild(el('dd', null, v)); dl.appendChild(d); };

const mathlibDocs = name => 'https://leanprover-community.github.io/mathlib4_docs/find/?pattern=' + encodeURIComponent(name) + '#doc';

function docsLink(name) {
  const a = el('a', 'act primary link', 'Look up in Mathlib docs');
  a.href = mathlibDocs(name); a.target = '_blank'; a.rel = 'noopener';
  return a;
}

function termSheet(key) {
  const g = GLOSSARY[key];
  if (!g) { unknownTermSheet(key); return; }
  sheet(s => {
    s.appendChild(el('h2', null, g.qual.split('.').pop()));
    s.appendChild(el('p', 'qual', g.qual));
    const dl = el('dl', 'prov');
    provRow(dl, 'Origin', g.origin === 'project' ? REPO : 'Mathlib @ ' + MATHLIB_REV);
    provRow(dl, 'Location', g.file);
    s.appendChild(dl);
    const pre = el('pre', 'lean wrap'); pre.textContent = g.sig; s.appendChild(pre);
    const gloss = el('div', 'gloss'); gloss.innerHTML = rich(g.gloss); s.appendChild(gloss);
    if (g.warn) {
      const w = el('p', 'disclaim');
      w.innerHTML = '<span class="pill warn">caution</span> ' + esc(g.warn);
      s.appendChild(w);
    }
    if (g.origin === 'mathlib') {
      const row = el('div', 'row'); row.style.marginTop = '14px';
      row.appendChild(docsLink(g.qual));
      s.appendChild(row);
      s.appendChild(el('p', 'disclaim', 'The docs show current Mathlib, which may differ from the version this project pins (' + MATHLIB_REV + ').'));
    }
  });
}

function unknownTermSheet(name) {
  sheet(s => {
    s.appendChild(el('h2', null, name));
    s.appendChild(el('p', 'qual', 'Not defined in this project'));
    s.appendChild(el('p', 'gloss', 'This comes from Lean or Mathlib, and the dojo has no note on it yet.'));
    const row = el('div', 'row');
    row.appendChild(docsLink(name));
    s.appendChild(row);
    s.appendChild(el('p', 'disclaim', 'The docs show current Mathlib, which may differ from the version this project pins (' + MATHLIB_REV + ').'));
  });
}

/* Docstring markup to HTML. Escapes first, so only the tags added here survive. */
const SCRIPT_BASE = /(?<![\p{L}\p{N}_'])(dim|[\p{L}⋂⋃∑∏⨅⨆])([_^])(\{[^{}]*\}|\([^()]*\)|[\p{L}\p{N}])/gu;
const math = html => html.replace(SCRIPT_BASE, (m, base, mark, group) => {
  const inner = /^[{(]/.test(group) ? group.slice(1, -1) : group;
  const tag = mark === '_' ? 'sub' : 'sup';
  return base + '<' + tag + '>' + inner + '</' + tag + '>';
});
function inline(text) {
  return text.split('`').map((part, i) => {
    if (i % 2) return '<code>' + math(esc(part)) + '</code>';
    return math(esc(part)).replace(/\*\*([^*]+)\*\*/g, '<b>$1</b>').replace(/\*([^*\s][^*]*)\*/g, '<em>$1</em>');
  }).join('');
}
function rich(text) {
  return text.split(/\n\s*\n/).map(p => '<p>' + inline(p.replace(/\s*\n\s*/g, ' ')) + '</p>').join('');
}

/* ───────────────────────── REVIEW ─────────────────────────
 * The kernel checks proofs. It cannot check that a definition means the right
 * thing, so this room is that check: the statement of the target theorem and the
 * definitions it rests on, simplest first. */
const TARGET = REVIEW.targets[0];
const DECLS = new Map(REVIEW.decls.map(d => [d.name, d]));
const STATE_LABEL = {
  approved: ['Approved', 'ok'], flagged: ['Flagged', 'stop'], stale: ['Changed', 'warn'],
  unsure: ['Not sure', 'warn'], unreviewed: ['To review', ''],
};
const NEVER_LINK = new Set(['Type', 'Prop', 'Sort']);
const DOUBLE_TAP_MS = 500;
const MAX_IMPORT_BYTES = 5 * 1024 * 1024;

let VERDICTS = [];
let STORAGE_OK = true;
let CARD = null;
let BACK = [];
let RECORDING = false;
let SHOWN = { name: null, at: 0 };
const DRAFTS = new Map();
const COMPARED = new Set();

const shortName = n => n.startsWith('instance#') ? 'instance in ' + n.split('#')[1].split('/').pop() : n;
const statusFor = d => statusOf(d, latestEvents(VERDICTS, REVIEW.repo), REVIEW);
const statePill = st => el('span', 'pill ' + STATE_LABEL[st][1], STATE_LABEL[st][0]);
const sourceUrl = d => 'https://github.com/' + REVIEW.repo + '/blob/' + REVIEW.rev + '/' + d.file + '#L' + d.line + '-L' + d.endLine;
const richBlock = (cls, text) => { const n = el('div', cls); n.innerHTML = rich(text); return n; };
const shownScope = d => d.scope.filter(l => !/^set_option\b/.test(l));

function openCard(name, { from = null } = {}) {
  if (from) BACK.push(from); else BACK = [];
  CARD = name;
  if (ROOM === 'review') { renderReview(); window.scrollTo(0, 0); } else go('review');
}

function renderReview() {
  if (CARD && DECLS.has(CARD)) renderCard(DECLS.get(CARD)); else renderQueue();
}

/* Dim what is proof rather than meaning: tactic blocks and primed structure fields
 * such as `zero_mem'`. Dimmed, never hidden, since tactics can also build data. */
function proofLines(code) {
  let block = null;
  return code.split('\n').map(line => {
    const indent = line.length - line.trimStart().length;
    if (block !== null && indent <= block) block = null;
    const inBlock = block !== null;
    const field = /^\s+[\p{L}_][\p{L}\p{N}_.]*'\s*:=/u.test(line);
    if (!inBlock && (field || /:=\s*by\s*$/.test(line))) block = indent;
    return inBlock || field;
  });
}

/* One Lean block: each source line keeps its indent when it wraps, known names are
 * tappable, and everything goes through text nodes. */
function leanBlock(code, d = null, open = {}) {
  const pre = el('pre', 'lean wrap');
  const local = new Map();
  if (d) for (const dep of d.deps) { local.set(dep, dep); local.set(dep.split('.').pop(), dep); }
  const dim = proofLines(code);
  code.split('\n').forEach((line, n) => {
    const text = line.trimStart();
    const row = el('span', 'line' + (dim[n] ? ' proof' : ''));
    row.style.setProperty('--indent', (line.length - text.length) + 'ch');
    let at = 0;
    if (d) {
      for (const m of text.matchAll(/[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*/gu)) {
        const tok = m[0];
        if (text[m.index - 1] === '.') continue;
        const project = local.get(tok);
        const g = GLOSSARY[tok];
        const known = g && g.origin === 'mathlib';
        const other = /^[A-Z][\p{L}\p{N}_]+/u.test(tok) && !NEVER_LINK.has(tok);
        if (!project && !known && !other) continue;
        row.appendChild(document.createTextNode(text.slice(at, m.index)));
        const b = el('button', 'term', tok);
        b.onclick = () => {
          if (open.before) open.before();
          if (project) declSheet(project); else termSheet(tok);
        };
        row.appendChild(b);
        at = m.index + tok.length;
      }
    }
    row.appendChild(document.createTextNode(text.slice(at) || ' '));
    pre.appendChild(row);
  });
  return pre;
}

function queueRow(d) {
  const b = el('button', 'queue-row');
  b.append(el('b', null, shortName(d.name)), statePill(statusFor(d).state), el('small', null, d.kind + ' · ' + d.file.split('/').pop() + ':' + d.line));
  b.onclick = () => openCard(d.name);
  return b;
}

function trustSentence(c) {
  const parts = [];
  if (c.flagged) parts.push(c.flagged + ' flagged');
  if (c.stale) parts.push(c.stale + ' changed since you read them');
  if (c.unsure) parts.push(c.unsure + ' not sure');
  if (c.unreviewed) parts.push(c.unreviewed + ' still to read');
  return parts.length ? parts.join(', ') + '.' : '';
}

function alertBox(cls, title, body) {
  const a = el('div', 'alert ' + cls);
  a.append(el('div', 'meta', title), el('p', null, body));
  return a;
}

function renderQueue() {
  const v = $('#view-review'); v.textContent = '';
  const { base, counts, trusted } = summarize(TARGET, VERDICTS, REVIEW);

  v.appendChild(el('p', 'intro', 'Lean checks that the proof is valid. It can’t check that these definitions say what the math should. That part is yours.'));
  if (!STORAGE_OK) v.appendChild(alertBox('stop', 'Can’t read saved verdicts', 'This browser isn’t letting the app use its storage, so your verdicts may exist but can’t be shown, and new ones won’t save. Try reopening the installed app.'));
  if (REVIEW.unchecked) v.appendChild(alertBox('stop', 'Test data', 'This build skipped the publication checks. Verdicts here mean nothing.'));

  const t = el('div', 'card trust' + (trusted ? ' done' : ''));
  t.appendChild(el('div', 'meta', 'The theorem you’re checking'));
  const target = DECLS.get(TARGET);
  if (target.doc) t.appendChild(richBlock('claim', target.doc));
  t.appendChild(leanBlock(target.code));
  const budget = el('div', 'budget'); budget.style.marginTop = '12px';
  budget.append(el('span', null, 'Approved'), el('span', null, counts.approved + ' of ' + counts.total));
  t.appendChild(budget);
  const bar = el('div', 'bar'), fill = el('i');
  fill.style.width = (counts.approved / counts.total * 100) + '%';
  bar.appendChild(fill); t.appendChild(bar);
  if (trusted) {
    t.appendChild(el('p', null, 'You’ve approved everything this statement rests on. Lean checks the proof separately, with lake build.'));
  } else {
    const line = trustSentence(counts);
    if (line) t.appendChild(el('p', null, line));
  }
  if (counts.sorry) t.appendChild(el('p', null, counts.sorry + ' of these contain sorry, so this can’t count as checked.'));
  if (counts.imported) t.appendChild(el('p', null, counts.imported + ' of the approvals came from an imported file, not from reading them here.'));
  if (counts.approved) t.appendChild(el('p', 'disclaim', counts.sourced + ' of ' + counts.approved + ' approvals were compared with the book.'));
  const next = nextInQueue(TARGET, VERDICTS, REVIEW);
  if (next) {
    const row = el('div', 'row'); row.style.marginTop = '12px';
    const go1 = el('button', 'act primary', 'Review next: ' + shortName(next.name));
    go1.onclick = () => openCard(next.name);
    row.appendChild(go1); t.appendChild(row);
  } else if (counts.flagged) {
    t.appendChild(el('p', null, 'Only flagged items are left. They clear when the Lean changes or you review them again.'));
  }
  v.appendChild(t);

  const list = el('div', 'card section');
  list.appendChild(el('div', 'meta', 'What it rests on, simplest first'));
  base.forEach(({ decl }) => list.appendChild(queueRow(decl)));
  v.appendChild(list);

  const others = REVIEW.decls.filter(d => !d.root);
  if (others.length) {
    const o = el('details', 'card section');
    o.appendChild(el('summary', null, 'Other definitions (' + others.length + ')'));
    o.appendChild(el('p', 'disclaim', 'The theorem’s statement doesn’t depend on these, so a wrong one can’t change what it says. Proofs may still use them, and Lean checks that.'));
    others.forEach(d => o.appendChild(queueRow(d)));
    v.appendChild(o);
  }

  const led = el('div', 'card section');
  led.appendChild(el('div', 'meta', 'Your verdicts'));
  const mine = VERDICTS.filter(e => e.repo === REVIEW.repo).length;
  led.appendChild(el('p', 'lede', mine + ' saved on this phone only. Export them now and then to keep a copy, or to check them on the Mac.'));
  const row = el('div', 'row'); row.style.marginTop = '11px';
  const ex = el('button', 'act', 'Export'); ex.onclick = exportLedger;
  const im = el('button', 'act', 'Import'); im.onclick = () => $('#ledger-file').click();
  row.append(ex, im); led.appendChild(row);
  const elsewhere = VERDICTS.length - mine;
  if (elsewhere) led.appendChild(el('p', 'disclaim', elsewhere + ' more belong to another repository and aren’t counted here.'));
  for (const [name, e] of latestEvents(VERDICTS, REVIEW.repo)) {
    if (!DECLS.has(name)) led.appendChild(el('p', 'disclaim', 'Your ' + e.verdict + ' verdict on ' + name + ' has no match, because that declaration no longer exists.' + (e.note ? ' Your note: ' + e.note : '')));
  }
  v.appendChild(led);

  const sorries = Object.keys(REVIEW.sorries).length;
  const risky = Object.keys(REVIEW.risky).length;
  const about = el('details', 'section');
  about.appendChild(el('summary', null, 'About this data'));
  about.appendChild(el('p', 'disclaim', REVIEW.repo + ' at ' + REVIEW.rev.slice(0, 7) + ', ' + REVIEW.toolchain + ', Mathlib ' + (REVIEW.mathlib || '?').slice(0, 10) + '. ' +
    (sorries ? 'sorry in ' + sorries + ' file(s). ' : 'No sorry. ') + (REVIEW.axioms.length ? REVIEW.axioms.length + ' axiom(s). ' : 'No axioms. ') +
    (risky ? 'Unusual features in ' + risky + ' file(s). ' : '') +
    'The list comes from reading the source text, without running Lean, so Lean could still use something it misses. Mathlib’s own definitions are not in the queue.'));
  v.appendChild(about);
}

function sourceBlock(d) {
  const wrap = el('div', 'section');
  wrap.appendChild(el('div', 'meta', 'The source'));
  const src = SOURCES[d.name];
  if (src) {
    wrap.appendChild(richBlock('claim', src.passage));
    wrap.appendChild(el('p', 'disclaim', (src.kind === 'quote' ? 'Quoted from ' : 'Paraphrase of ') + src.cite + '. This is what the Lean should match.'));
    return wrap;
  }
  const refs = [...new Set(REVIEW.refs[d.file] || Object.values(REVIEW.refs).flat())];
  wrap.appendChild(el('p', 'claim none', refs.length
    ? 'No passage linked yet. This project cites: ' + refs.join('; ') + '.'
    : 'No source is linked for this one yet.'));
  return wrap;
}

function claimBlock(d) {
  const wrap = el('div', 'section');
  wrap.appendChild(el('div', 'meta', 'What it claims'));
  if (d.doc) {
    wrap.appendChild(richBlock('claim', d.doc));
    wrap.appendChild(el('p', 'disclaim', 'From the docstring, written alongside the code. It’s a claim to test, not evidence.'));
  } else if (d.kind === 'instance') {
    wrap.appendChild(el('p', 'claim none', 'This gives a type its algebraic structure. Is it the usual structure, the one a mathematician would assume?'));
  } else {
    wrap.appendChild(el('p', 'claim none', 'No docstring. Judge the Lean against the math you expect.'));
  }
  const g = GLOSSARY[d.name];
  if (g && g.origin === 'project') {
    wrap.appendChild(el('div', 'meta', 'Dojo note')).style.marginTop = '11px';
    wrap.appendChild(richBlock('claim', g.gloss));
    if (g.warn) wrap.appendChild(el('p', 'disclaim', g.warn));
  }
  return wrap;
}

function diffBlock(before, after) {
  const pre = el('pre', 'lean wrap diff'); pre.style.marginTop = '9px';
  lineDiff(before, after).forEach(l => pre.appendChild(
    el('span', l.t === '+' ? 'add' : l.t === '-' ? 'del' : null, l.t + ' ' + l.s)));
  return pre;
}

function staleBlock(d, st) {
  const a = el('div', 'alert'); a.style.marginTop = '13px';
  a.appendChild(el('div', 'meta', 'Changed since your “' + st.event.verdict + '” on ' + new Date(st.event.at).toLocaleDateString()));
  describeStale(st.stale).forEach(s => a.appendChild(el('p', null, s)));
  if (st.event.note) a.appendChild(el('p', null, 'Your note: ' + st.event.note));
  if (st.event.code && st.event.code !== d.code) a.appendChild(diffBlock(st.event.code, d.code));
  const oldScope = (st.event.scope || []).join('\n');
  if (st.event.scope && oldScope !== d.scope.join('\n')) a.appendChild(diffBlock(oldScope, d.scope.join('\n')));
  return a;
}

function verdictPrompt(d) {
  if (d.kind === 'theorem' || d.kind === 'lemma') return 'Does this say the theorem you expect, with the right hypotheses? Lean has checked the proof of whatever it says, so this statement is the part to get right.';
  if (d.kind === 'instance') return 'Is this the standard structure? A nonstandard one could quietly change what later definitions mean.';
  return 'Does this Lean mean what the math should mean? Check the hypotheses and the edge cases.';
}

function renderCard(d) {
  const v = $('#view-review'); v.textContent = '';
  if (SHOWN.name !== d.name) SHOWN = { name: d.name, at: Date.now() };
  const st = statusFor(d);
  const back = el('button', 'back', BACK.length ? '‹ Back to ' + shortName(BACK.at(-1)) : '‹ All definitions');
  back.onclick = () => { CARD = BACK.pop() || null; renderReview(); window.scrollTo(0, 0); };
  v.appendChild(back);
  if (!STORAGE_OK) v.appendChild(alertBox('stop', 'Can’t save', 'Storage isn’t available, so verdicts won’t be kept.'));

  const c = el('div', 'card');
  const { base } = summarize(TARGET, VERDICTS, REVIEW);
  const pos = base.findIndex(x => x.decl.name === d.name);
  c.appendChild(el('div', 'meta', pos >= 0 ? (pos + 1) + ' of ' + base.length : 'Not needed for ' + TARGET));
  const head = el('div', 'card-head');
  head.append(el('h2', null, shortName(d.name)), statePill(st.state));
  c.appendChild(head);
  const src = el('a', 'srcline', d.kind + ' · ' + d.file + ':' + d.line);
  src.href = sourceUrl(d); src.target = '_blank'; src.rel = 'noopener';
  c.appendChild(src);
  if (st.stale) c.appendChild(staleBlock(d, st));
  if (st.state === 'flagged') {
    const a = alertBox('stop', 'You flagged this', st.event.note || '(no note)');
    a.style.marginTop = '13px';
    c.appendChild(a);
  }
  if (d.hasSorry) {
    const a = alertBox('stop', 'Contains sorry', 'Part of this declaration is unproved.');
    a.style.marginTop = '13px';
    c.appendChild(a);
  }
  c.appendChild(sourceBlock(d));
  c.appendChild(claimBlock(d));

  const lean = el('div', 'section');
  const isThm = d.kind === 'theorem' || d.kind === 'lemma';
  lean.appendChild(el('div', 'meta', isThm ? 'The Lean (statement only)' : 'The Lean'));
  const block = leanBlock(d.code, d);
  block.style.marginTop = '9px';
  lean.appendChild(block);
  if (block.querySelector('.proof')) lean.appendChild(el('p', 'disclaim', 'Dimmed lines are proof steps. Read the rest first.'));
  if (d.kind === 'instance') lean.appendChild(el('p', 'disclaim', 'Lean can use an instance silently wherever the types match, without the code naming it.'));
  c.appendChild(lean);

  const scope = shownScope(d);
  if (scope.length) {
    const s = el('div', 'section');
    s.appendChild(el('div', 'meta', 'Assumed here'));
    const pre = leanBlock(scope.join('\n'));
    pre.style.marginTop = '9px';
    s.appendChild(pre);
    c.appendChild(s);
  }
  if (d.deps.length) {
    const u = el('div', 'section');
    u.appendChild(el('div', 'meta', 'Rests on'));
    const chips = el('div', 'chips');
    d.deps.forEach(n => {
      const dep = DECLS.get(n);
      const b = el('button', 'chip');
      b.append(el('i', 'mark ' + statusFor(dep).state), el('span', null, shortName(n)));
      b.onclick = () => declSheet(n);
      chips.appendChild(b);
    });
    u.appendChild(chips);
    c.appendChild(u);
  }
  v.appendChild(c);

  const f = el('div', 'card section');
  f.appendChild(el('div', 'meta', 'Your verdict'));
  f.appendChild(el('p', 'lede', verdictPrompt(d)));
  const lab = el('label', 'check');
  const box = el('input'); box.type = 'checkbox'; box.checked = COMPARED.has(d.name);
  box.onchange = () => { if (box.checked) COMPARED.add(d.name); else COMPARED.delete(d.name); };
  lab.append(box, el('span', null, 'I compared this with the book'));
  f.appendChild(lab);
  const ta = el('textarea'); ta.id = 'verdict-note';
  ta.placeholder = 'Note (needed to flag)';
  ta.value = DRAFTS.get(d.name) || '';
  ta.oninput = () => { if (ta.value) DRAFTS.set(d.name, ta.value); else DRAFTS.delete(d.name); };
  f.appendChild(ta);
  const hint = el('p', 'hint'); hint.hidden = true;
  f.appendChild(hint);
  const row = el('div', 'verdicts');
  const yes = el('button', 'act primary', 'Means the right thing');
  const no = el('button', 'act danger', 'Flag mismatch');
  const unsure = el('button', 'act', 'Not sure');
  const buttons = [yes, no, unsure];
  yes.onclick = () => record(d, 'approved', ta.value, buttons);
  no.onclick = () => {
    if (!ta.value.trim()) { hint.textContent = 'Say what looks wrong first, then flag it.'; hint.hidden = false; ta.focus(); return; }
    record(d, 'flagged', ta.value, buttons);
  };
  unsure.onclick = () => record(d, 'unsure', ta.value, buttons);
  row.append(...buttons);
  f.appendChild(row);
  f.appendChild(el('p', 'disclaim', 'Approving says you read it. It doesn’t say it compiles.'));
  v.appendChild(f);

  const hist = VERDICTS.filter(e => e.repo === REVIEW.repo && e.decl === d.name).sort((a, b) => b.at - a.at);
  if (hist.length) {
    const h = el('div', 'card section');
    h.appendChild(el('div', 'meta', 'History'));
    hist.forEach(e => h.appendChild(el('div', 'hist',
      new Date(e.at).toLocaleString() + ' · ' + e.verdict + (e.imported ? ' · imported' : '') + (e.checkedSource ? ' · compared with book' : '') + (e.note ? ' · ' + e.note : ''))));
    v.appendChild(h);
  }
}

function declSheet(name) {
  const d = DECLS.get(name);
  if (!d) { unknownTermSheet(name); return; }
  sheet((s, close) => {
    const head = el('div', 'card-head');
    head.append(el('h2', null, shortName(d.name)), statePill(statusFor(d).state));
    s.appendChild(head);
    s.appendChild(el('p', 'qual', d.kind + ' · ' + d.file + ':' + d.line));
    if (d.doc) s.appendChild(richBlock('gloss', d.doc));
    s.appendChild(leanBlock(d.code, d, { before: close }));
    const row = el('div', 'row'); row.style.marginTop = '14px';
    const o = el('button', 'act primary', 'Review this one');
    o.onclick = () => { close(); openCard(d.name, { from: CARD && CARD !== d.name ? CARD : null }); };
    row.appendChild(o); s.appendChild(row);
  });
}

async function record(d, verdict, note, buttons) {
  // A double tap must not approve the card that replaces this one.
  if (RECORDING || Date.now() - SHOWN.at < DOUBLE_TAP_MS) return;
  RECORDING = true;
  buttons.forEach(b => { b.disabled = true; });
  let ev;
  try {
    ev = makeEvent(d, verdict, note, REVIEW, nextTimestamp(VERDICTS, REVIEW.repo, d.name), { checkedSource: COMPARED.has(d.name) });
    // Never show a verdict as recorded unless it reached storage.
    await putVerdicts([ev]);
  } catch (e) {
    RECORDING = false;
    buttons.forEach(b => { b.disabled = false; });
    toast('<b>Not saved.</b> The phone refused the write, so nothing was recorded.', 5000);
    return;
  }
  RECORDING = false;
  VERDICTS.push(ev);
  DRAFTS.delete(d.name);
  COMPARED.delete(d.name);
  navigator.storage?.persist?.().catch(() => {});
  if (BACK.length) CARD = BACK.pop();
  else CARD = d.root ? (nextInQueue(TARGET, VERDICTS, REVIEW, { after: d.name, includeUnsure: false })?.name ?? null) : null;
  renderReview();
  window.scrollTo(0, 0);
  toast(esc(shortName(d.name)) + ': ' + esc(verdict) + '. Saved.', 2200);
}

async function exportLedger() {
  if (!STORAGE_OK) { toast('Can’t read your saved verdicts, so there’s nothing safe to export.'); return; }
  if (!VERDICTS.length) { toast('No verdicts to export yet.'); return; }
  const stamp = new Date().toISOString().slice(0, 10);
  const text = serializeLedger(VERDICTS, REVIEW, new Date().toISOString());
  const how = await shareFile(new File([text], 'dojo-reviews-' + stamp + '.json', { type: 'application/json' }), 'Dojo reviews');
  if (how === 'downloaded') toast('Couldn’t open the share sheet, so the file went to Downloads. Check it arrived.', 5000);
}

function confirmImport(parsed) {
  const plan = planImport(parsed.events, VERDICTS);
  const ignored = parsed.skipped + parsed.conflicts + plan.conflicts;
  const forHere = plan.fresh.filter(e => e.repo === REVIEW.repo);
  const before = summarize(TARGET, VERDICTS, REVIEW).counts.approved;
  const after = summarize(TARGET, [...VERDICTS, ...plan.fresh], REVIEW).counts.approved;
  sheet((s, close) => {
    s.appendChild(el('h2', null, 'Import these verdicts?'));
    const dl = el('dl', 'prov');
    provRow(dl, 'New', String(plan.fresh.length));
    provRow(dl, 'Already here', String(plan.same));
    if (ignored) provRow(dl, 'Ignored', ignored + ' (damaged, dated in the future, or conflicting)');
    if (plan.fresh.length !== forHere.length) provRow(dl, 'Other repo', (plan.fresh.length - forHere.length) + ' (saved, not counted)');
    provRow(dl, 'Approved', before + ' now, ' + after + ' after');
    s.appendChild(dl);
    s.appendChild(el('p', 'disclaim', 'Anything imported counts toward the theorem and is marked as imported, because you didn’t read it here. Only import a file you trust.'));
    const row = el('div', 'row'); row.style.marginTop = '12px';
    const go1 = el('button', 'act primary', plan.fresh.length ? 'Import ' + plan.fresh.length : 'Nothing new');
    go1.disabled = !plan.fresh.length;
    go1.onclick = async () => {
      go1.disabled = true;
      try {
        await putVerdicts(plan.fresh);
      } catch (e) {
        close();
        toast('<b>Import failed.</b> Nothing was added.', 5000);
        return;
      }
      plan.fresh.forEach(x => VERDICTS.push(x));
      close();
      renderReview();
      toast('Imported ' + plan.fresh.length + '.');
    };
    const no = el('button', 'act', 'Cancel');
    no.onclick = close;
    row.append(go1, no);
    s.appendChild(row);
  });
}

$('#ledger-file')?.addEventListener('change', async e => {
  const f = e.target.files && e.target.files[0];
  e.target.value = '';
  if (!f) return;
  if (!STORAGE_OK) { toast('Can’t read your saved verdicts, so importing isn’t safe right now.'); return; }
  if (f.size > MAX_IMPORT_BYTES) { toast('<b>Import failed.</b> That file is too large to be a review ledger.', 5000); return; }
  try {
    confirmImport(parseLedger(await f.text()));
  } catch (err) {
    toast('<b>Import failed.</b> That isn’t a Dojo review file.', 5000);
  }
});

/* ───────────────────────── READ ───────────────────────── */
function renderRead() {
  const v = $('#view-read'); v.textContent = '';
  v.appendChild(el('div', 'meta', 'Source'));
  v.appendChild(el('p', 'lede', READING.source));

  const card = el('div', 'card'); card.style.marginTop = '13px';
  const prose = el('div', 'prose');
  READING.english.forEach(par => {
    const p = el('p');
    p.innerHTML = math(par).replace(/\{(\w+)\}/g, (m, k) => {
      const g = GLOSSARY[k] || GLOSSARY[Object.keys(GLOSSARY).find(x => x.endsWith('.' + k))];
      if (!g) return '<i>' + esc(k) + '</i>';
      return '<button class="term" data-term="' + k + '" aria-pressed="false">' + esc(g.qual.split('.').pop()) + '</button>';
    });
    prose.appendChild(p);
  });
  card.appendChild(prose);
  v.appendChild(card);

  const lc = el('div', 'card'); lc.style.marginTop = '13px';
  lc.appendChild(el('div', 'meta', 'The Lean beside it'));
  const pre = el('pre', 'lean wrap'); pre.style.marginTop = '9px';
  READING.lean.forEach(seg => {
    if (seg.k) {
      const b = el('button', 'term'); b.dataset.term = seg.k;
      b.setAttribute('aria-pressed', 'false'); b.textContent = seg.t;
      pre.appendChild(b);
    } else pre.appendChild(document.createTextNode(seg.t));
  });
  lc.appendChild(pre);
  lc.appendChild(el('div', 'srcline', READING.leanSrc + '  ·  ' + TOOLCHAIN));
  v.appendChild(lc);

  const row = el('div', 'row'); row.style.marginTop = '13px';
  const b1 = el('button', 'act stub', 'Check this file');
  b1.onclick = () => stub('Check this file', 'Sends UlmInvariants.lean to the Lean server on the Mac and returns goals and diagnostics');
  const b2 = el('button', 'act', 'Review this definition');
  b2.onclick = () => openCard('ulmInvariant');
  row.append(b1, b2);
  v.appendChild(row);
  v.appendChild(el('p', 'disclaim', 'Tap any highlighted term — in the prose or in the Lean — to see where it is defined.'));

  v.querySelectorAll('.term').forEach(b => {
    b.onclick = () => {
      v.querySelectorAll('.term').forEach(o => o.setAttribute('aria-pressed', String(o.dataset.term === b.dataset.term)));
      termSheet(b.dataset.term);
    };
  });
}

/* ───────────────────────── DECIDE ───────────────────────── */
let qi = 0, answered = [], optionOrder = [];
/* Shuffle once per run, so the right answer isn't always first and coming back to
 * a question doesn't move anything. */
function orderFor(i) {
  if (!optionOrder[i]) {
    const idx = QUESTIONS[i].opts.map((_, k) => k);
    for (let k = idx.length - 1; k > 0; k--) {
      const j = Math.floor(Math.random() * (k + 1));
      [idx[k], idx[j]] = [idx[j], idx[k]];
    }
    optionOrder[i] = idx;
  }
  return optionOrder[i];
}
function renderDecide() {
  const v = $('#view-decide'); v.textContent = '';
  const prog = el('div', 'progress');
  QUESTIONS.forEach((_, i) => { const b = el('i'); if (answered[i] != null) b.className = 'on'; prog.appendChild(b); });
  v.appendChild(prog);

  if (qi >= QUESTIONS.length) {
    const c = el('div', 'card');
    c.appendChild(el('h2', null, 'Session done'));
    c.appendChild(el('p', 'lede', answered.filter(Boolean).length + ' of ' + QUESTIONS.length +
      ' first-try. Four decisions is a phone session; the queue is curated, not generated.'));
    const row = el('div', 'row'); row.style.marginTop = '13px';
    const again = el('button', 'act', 'Run it again');
    again.onclick = () => { qi = 0; answered = []; optionOrder = []; renderDecide(); };
    const send = el('button', 'act stub primary', 'Record to project');
    send.onclick = () => stub('Record to project', 'Writes these decisions into the jobs DB against the current Git revision of ' + REPO);
    row.append(again, send);
    c.appendChild(row);
    v.appendChild(c);
    return;
  }

  const Q = QUESTIONS[qi];
  const c = el('div', 'card');
  c.appendChild(el('div', 'meta', 'Question ' + (qi + 1) + ' of ' + QUESTIONS.length));
  c.appendChild(el('p', 'q', Q.q));
  c.appendChild(el('div', 'sep'));
  const wrap = el('div'); wrap.style.marginTop = '12px';
  const opts = orderFor(qi).map(k => Q.opts[k]);
  const reveal = () => {
    wrap.querySelectorAll('.choice').forEach((x, i) => {
      x.dataset.state = opts[i].ok ? 'right' : 'wrong';
      x.appendChild(el('small', null, opts[i].why));
    });
    prog.children[qi].className = 'on';
    const nav = el('div', 'row'); nav.style.marginTop = '13px';
    const cite = el('div', 'srcline', Q.cite); cite.style.flex = '1 1 100%';
    const next = el('button', 'act primary', qi === QUESTIONS.length - 1 ? 'Finish' : 'Next');
    next.onclick = () => { qi++; renderDecide(); };
    nav.append(cite, next);
    c.appendChild(nav);
    return next;
  };
  opts.forEach(o => {
    const b = el('button', 'choice');
    b.appendChild(el('span', null, o.t));
    b.onclick = () => {
      if (answered[qi] != null) return;
      answered[qi] = !!o.ok;
      reveal().scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    };
    wrap.appendChild(b);
  });
  c.appendChild(wrap);
  v.appendChild(c);
  if (answered[qi] != null) reveal();
}

/* ───────────────────────── MAP ───────────────────────── */
let sel = null;
function renderMap() {
  const v = $('#view-map'); v.textContent = '';
  const decls = DAG.reduce((a, n) => a + n.d, 0);
  v.appendChild(el('p', 'lede', 'Real import edges from ' + REPO + '. ' + DAG.length + ' files, ' +
    decls + ' declarations, no sorry — counted from source.'));

  const dag = el('div', 'dag');
  DAG.forEach(n => {
    const lv = el('div', 'lvl');
    const b = el('button', 'node');
    b.appendChild(el('span', 'dot' + (n.d === 0 ? ' empty' : '')));
    b.appendChild(el('span', null, n.id.replace(/^Lib\./, '')));
    b.setAttribute('aria-pressed', String(sel === n.id));
    b.onclick = () => { sel = n.id; renderMap(); nodeSheet(n); };
    lv.appendChild(b);
    if (n.dep.length) lv.appendChild(el('span', 'up', '↑ ' + n.dep.map(x => x.replace(/^Lib\./, '')).join('  ·  ')));
    dag.appendChild(lv);
  });
  v.appendChild(dag);

  const c = el('div', 'card'); c.style.marginTop = '13px';
  c.appendChild(el('div', 'meta', 'What it all builds to'));
  const pre = el('pre', 'lean'); pre.style.marginTop = '9px'; pre.textContent = THEOREM;
  c.appendChild(pre);
  c.appendChild(el('div', 'srcline', 'Lib/Ulm/Theorem.lean:52–63'));
  v.appendChild(c);

  const row = el('div', 'row'); row.style.marginTop = '13px';
  const b = el('button', 'act stub', 'Show reverse dependencies');
  b.onclick = () => stub('Reverse dependencies', 'Shows which files need rechecking if the selected file changed');
  row.appendChild(b);
  v.appendChild(row);
}
function nodeSheet(n) {
  sheet((s, close) => {
    s.appendChild(el('h2', null, n.id.replace(/^Lib\./, '')));
    s.appendChild(el('p', 'qual', n.id));
    const dl = el('dl', 'prov');
    provRow(dl, 'Role', n.role);
    provRow(dl, 'Declares', n.d === 0 ? 'nothing — import/re-export only' : n.d + ' declarations');
    provRow(dl, 'Imports', n.dep.length ? n.dep.join(', ') : 'Mathlib only');
    provRow(dl, 'Sorry', 'none');
    s.appendChild(dl);
    const row = el('div', 'row');
    const q = el('button', 'act stub primary', 'Queue for practice');
    q.onclick = () => { close(); stub('Queue for practice', 'Adds a curated question about this file to the Decide queue'); };
    const o = el('button', 'act stub', 'Open the file');
    o.onclick = () => { close(); stub('Open the file', 'Fetches this file from the Mac and shows it in Read'); };
    row.append(q, o);
    s.appendChild(row);
  });
}

/* ───────────────────────── CARRY ───────────────────────── */
function renderCarry() {
  const v = $('#view-carry'); v.textContent = '';
  const online = navigator.onLine;
  const net = el('div', 'net' + (online ? '' : ' off'));
  net.appendChild(el('i')); net.appendChild(el('span', null, online ? 'Online' : 'Offline'));
  v.appendChild(net);
  v.appendChild(el('p', 'lede', 'Pick what survives losing the Mac. Once this app has loaded online, its files are stored on the phone and it opens in airplane mode.'));

  const c = el('div', 'card'); c.style.marginTop = '12px';
  PACKS.forEach(p => {
    const it = el('div', 'item');
    it.appendChild(el('div', 'name', p.name));
    const sw = el('button', 'sw');
    sw.setAttribute('role', 'switch');
    sw.setAttribute('aria-checked', String(p.on));
    sw.setAttribute('aria-label', p.name);
    sw.onclick = () => { p.on = !p.on; renderCarry(); };
    it.appendChild(sw);
    it.appendChild(el('div', 'sub', p.sub + '  ·  ' + p.mb.toFixed(2) + ' MB'));
    c.appendChild(it);
  });
  v.appendChild(c);

  const total = PACKS.filter(p => p.on).reduce((a, b) => a + b.mb, 0);
  const bc = el('div', 'card'); bc.style.marginTop = '13px';
  const b1 = el('div', 'budget');
  b1.append(el('span', null, 'Selected'), el('span', null, total.toFixed(2) + ' MB'));
  bc.appendChild(b1);
  const bar = el('div', 'bar'); const fill = el('i');
  fill.style.width = Math.min(100, total / 5 * 100) + '%';
  bar.appendChild(fill); bc.appendChild(bar);
  bc.appendChild(el('p', 'disclaim', 'For scale: the full Mathlib olean cache is about 7 GB per checkout — three orders of magnitude more than anything on this screen. That is why the offline pack carries cited signatures, not a compiler.'));
  v.appendChild(bc);

  const row = el('div', 'row'); row.style.marginTop = '13px';
  const d = el('button', 'act primary stub', 'Download satchel');
  d.onclick = () => stub('Download satchel', 'Caches the selected packs and records the base Git revision they came from');
  const s3 = el('button', 'act stub', 'Show a conflicting return edit');
  s3.onclick = () => stub('Conflict preview', 'Shows a phone edit and a desktop edit to the same declaration side by side — both kept, never auto-merged');
  row.append(d, s3);
  v.appendChild(row);
}

/* ───────────────────────── NOTES ───────────────────────── */
let pendingBlob = null, noteDraft = '', noteFrom = null, NOTES_OK = true;
function renderNotes() {
  const v = $('#view-notes'); v.textContent = '';
  v.appendChild(el('p', 'lede', 'What you want changed. Screenshot on the phone, mark it up in Photos, then attach it here. Notes stay on this phone.'));
  if (!NOTES_OK) { const a = alertBox('stop', 'Can’t read saved notes', 'Your notes may still exist, but this browser isn’t letting the app read them.'); a.style.marginTop = '12px'; v.appendChild(a); }

  const c = el('div', 'card'); c.style.marginTop = '12px';
  const ta = el('textarea'); ta.id = 'note-text';
  ta.placeholder = 'What should be different? Which screen?';
  ta.value = noteDraft;
  ta.oninput = () => { noteDraft = ta.value; };
  c.appendChild(ta);
  const lbl = el('button', 'file-btn'); lbl.id = 'file-label';
  lbl.textContent = pendingBlob ? '✓  Screenshot attached — add a note and save' : '＋  Attach a marked-up screenshot';
  lbl.onclick = () => $('#shot').click();
  c.appendChild(lbl);
  const row = el('div', 'row'); row.style.marginTop = '11px';
  const save = el('button', 'act primary', 'Save note');
  save.onclick = () => saveNote(ta);
  const ex = el('button', 'act', 'Export all');
  ex.onclick = exportNotes;
  row.append(save, ex);
  c.appendChild(row);
  v.appendChild(c);

  v.appendChild(el('div', 'meta', NOTES.length ? NOTES.length + ' note' + (NOTES.length === 1 ? '' : 's') : 'No notes yet'))
   .style.marginTop = '20px';

  const list = el('div', 'stack'); list.style.marginTop = '10px';
  NOTES.slice().sort((a, b) => b.at - a.at).forEach(n => {
    const it = el('div', 'note-item');
    const top = el('div', 'row');
    top.append(el('span', 'pill', n.room || '?'), el('span', 'meta', new Date(n.at).toLocaleString()));
    it.appendChild(top);
    it.appendChild(el('div', null, n.text || '(no text)'));
    if (n.blob) {
      const im = el('img'); im.alt = 'attached screenshot';
      im.src = URL.createObjectURL(n.blob);
      it.appendChild(im);
    }
    const del = el('button', 'act', 'Delete'); del.style.flex = '0 0 auto';
    del.onclick = async () => {
      if (del.dataset.armed !== 'yes') { del.dataset.armed = 'yes'; del.textContent = 'Tap again to delete'; return; }
      try { await dropNote(n.id); } catch (err) { toast('Not deleted: storage error.'); return; }
      NOTES = NOTES.filter(x => x.id !== n.id);
      renderNotes();
    };
    const r2 = el('div', 'row'); r2.appendChild(del);
    it.appendChild(r2);
    list.appendChild(it);
  });
  v.appendChild(list);
}

$('#shot').addEventListener('change', e => {
  const f = e.target.files && e.target.files[0];
  e.target.value = '';
  if (!f) return;
  pendingBlob = f;
  const lbl = $('#file-label');
  if (lbl) lbl.textContent = '✓  Screenshot attached — add a note and save';
});

async function saveNote(ta) {
  const text = ta.value.trim();
  if (!text && !pendingBlob) { toast('Write something or attach a screenshot first.'); return; }
  const note = { id: 'n' + Date.now() + Math.random().toString(36).slice(2, 6), text, room: noteFrom || ROOM, at: Date.now(), blob: pendingBlob || null };
  // Keep the draft unless the note really saved.
  try { await putNote(note); } catch (err) { toast('<b>Not saved.</b> Storage error, so your text is still here.', 5000); return; }
  NOTES.push(note);
  pendingBlob = null; noteDraft = ''; noteFrom = null;
  navigator.storage?.persist?.().catch(() => {});
  renderNotes();
}

/* Share sheet is the only reliable way to get a file off iOS Safari. */
async function shareFile(files, title) {
  const list = Array.isArray(files) ? files : [files];
  if (navigator.canShare && navigator.canShare({ files: list })) {
    try { await navigator.share({ files: list, title }); return 'shared'; } catch (e) { if (e.name === 'AbortError') return 'cancelled'; }
  }
  const url = URL.createObjectURL(list[0]);
  const a = el('a'); a.href = url; a.download = list[0].name; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 4000);
  return 'downloaded';
}

async function exportNotes() {
  if (!NOTES.length) { toast('Nothing to export yet.'); return; }
  const shots = [];
  const body = NOTES.slice().sort((a, b) => a.at - b.at).map(n => {
    let line = '## ' + (n.room || '?') + '  ·  ' + new Date(n.at).toISOString() + '\n\n' + (n.text || '');
    if (n.blob) {
      const name = 'dojo-note-' + (shots.length + 1) + '.' + ((n.blob.type || 'image/png').split('/')[1] || 'png');
      shots.push(new File([n.blob], name, { type: n.blob.type || 'image/png' }));
      line += '\n\n(screenshot: ' + name + ')';
    }
    return line;
  }).join('\n\n---\n\n');
  const md = new File(['# Ulm Dojo — change requests\n\n' + body + '\n'], 'dojo-notes.md', { type: 'text/markdown' });
  const how = await shareFile([md, ...shots], 'Dojo notes');
  if (how === 'downloaded' && shots.length) toast('Only the text could be saved here. Screenshots stay in the app.', 5000);
}

/* ───────────────────────── shell ───────────────────────── */
const RENDER = { review: renderReview, read: renderRead, decide: renderDecide, map: renderMap, carry: renderCarry, notes: renderNotes };
function go(room) {
  ROOM = room;
  document.documentElement.dataset.room = room;
  $('#room-title').textContent = ROOMS[room].title;
  $('#room-eyebrow').textContent = ROOMS[room].eyebrow;
  document.querySelectorAll('.nav button').forEach(b => b.setAttribute('aria-current', String(b.dataset.room === room)));
  Object.keys(RENDER).forEach(r => { $('#view-' + r).hidden = r !== room; });
  RENDER[room]();
  window.scrollTo(0, 0);
}
document.querySelectorAll('.nav button').forEach(b => { b.onclick = () => go(b.dataset.room); });

$('#btn-note').onclick = () => {
  const from = ROOM;
  if (from !== 'notes') {
    noteFrom = from;
    if (!noteDraft) noteDraft = '[' + from[0].toUpperCase() + from.slice(1) + '] ';
  }
  go('notes');
  const ta = $('#note-text');
  if (ta) { ta.focus(); ta.setSelectionRange(ta.value.length, ta.value.length); }
};

$('#btn-about').onclick = () => sheet(s => {
  s.appendChild(el('h2', null, 'What this is'));
  s.appendChild(el('p', 'gloss', 'A way to check that Lean says what it claims. Lean checks proofs, but it can’t tell whether a definition means the right thing. Review is that check, done by you.'));
  const dl = el('dl', 'prov');
  provRow(dl, 'Review', 'Built from ' + REVIEW.repo + ' at ' + REVIEW.rev.slice(0, 7) + '.');
  provRow(dl, 'Other tabs', 'Read, Decide, Map and Carry are earlier experiments. Controls marked ◌ aren’t built yet, and say what they would do.');
  provRow(dl, 'Not done', 'Nothing here compiles Lean. Run lake build for the proofs.');
  provRow(dl, 'Privacy', 'No account, no analytics. Notes and verdicts leave this phone only when you export them.');
  s.appendChild(dl);
  s.appendChild(el('p', 'disclaim', 'To install: Safari share menu, then Add to Home Screen. After it has loaded online once, it opens offline.'));
  const row = el('div', 'row'); row.style.marginTop = '10px';
  const u = el('button', 'act', 'Check for update');
  u.onclick = async () => {
    const r = await navigator.serviceWorker?.getRegistration();
    if (!r) { toast('Updates aren’t available in this browser view.'); return; }
    try { await r.update(); toast('Checked. If there’s a new version, you’ll be asked to reload.'); }
    catch (e) { toast('Couldn’t check: you may be offline.'); }
  };
  row.appendChild(u);
  s.appendChild(row);
});

window.addEventListener('online',  () => { if (ROOM === 'carry') renderCarry(); });
window.addEventListener('offline', () => { if (ROOM === 'carry') renderCarry(); });

go('review');
loadNotes()
  .then(n => { NOTES = n || []; })
  .catch(() => { NOTES_OK = false; })
  .then(() => { if (ROOM === 'notes') renderNotes(); });
loadVerdicts()
  .then(v => { VERDICTS = v || []; })
  .catch(() => { STORAGE_OK = false; })
  .then(() => { if (ROOM === 'review') renderReview(); });

if ('serviceWorker' in navigator) {
  const hadController = !!navigator.serviceWorker.controller;
  navigator.serviceWorker.addEventListener('controllerchange', () => {
    if (hadController) toast('New version ready. Close and reopen the app to use it.', 8000);
  });
  window.addEventListener('load', () => navigator.serviceWorker.register('sw.js').catch(() => {}));
  // A Home Screen app can stay suspended for days, so check when it comes back.
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState !== 'visible') return;
    navigator.serviceWorker.getRegistration().then(r => r && r.update()).catch(() => {});
  });
}
