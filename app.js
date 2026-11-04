import { MATHLIB_REV, TOOLCHAIN, REPO, GLOSSARY, READING, QUESTIONS, DAG, THEOREM, PACKS } from './data.js';
import { REVIEW } from './review-data.js';
import {
  describeStale, latestEvents, lineDiff, makeEvent, nextInQueue, parseLedger, serializeLedger,
  statusOf, summarize,
} from './review-core.js';

const $ = s => document.querySelector(s);
const el = (t, c, x) => { const n = document.createElement(t); if (c) n.className = c; if (x != null) n.textContent = x; return n; };
const esc = s => String(s).replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

let ROOM = 'review';
let NOTES = [];

const ROOMS = {
  review: { title: 'Behind ' + REVIEW.targets[0], eyebrow: 'Review' },
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
let _db = null;
function idb() {
  if (_db) return Promise.resolve(_db);
  return new Promise((res, rej) => {
    const r = indexedDB.open(DB_NAME, 2);
    r.onupgradeneeded = () => {
      const stores = r.result.objectStoreNames;
      if (!stores.contains(STORE)) r.result.createObjectStore(STORE, { keyPath: 'id' });
      if (!stores.contains(VERDICT_STORE)) r.result.createObjectStore(VERDICT_STORE, { keyPath: 'id' });
    };
    r.onblocked = () => toast('Close other Dojo windows so its storage can update.', 6000);
    r.onsuccess = () => {
      _db = r.result;
      _db.onversionchange = () => { _db.close(); _db = null; };
      res(_db);
    };
    r.onerror = () => rej(r.error);
  });
}
async function tx(mode, fn, store = STORE) {
  const db = await idb();
  return new Promise((res, rej) => {
    const t = db.transaction(store, mode);
    const out = fn(t.objectStore(store));
    t.onabort = () => rej(t.error);
    t.oncomplete = () => res(out && out.result !== undefined ? out.result : out);
    t.onerror = () => rej(t.error);
  });
}
const loadNotes = () => tx('readonly', s => s.getAll()).catch(() => []);
const putNote   = n  => tx('readwrite', s => s.put(n));
const dropNote  = id => tx('readwrite', s => s.delete(id));
const loadVerdicts = () => tx('readonly', s => s.getAll(), VERDICT_STORE);
const putVerdict   = e  => tx('readwrite', s => s.put(e), VERDICT_STORE);

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
  const close = () => scrim.remove();
  build(s, close);
  scrim.appendChild(s);
  scrim.addEventListener('click', e => { if (e.target === scrim) close(); });
  document.addEventListener('keydown', function esc2(e) {
    if (e.key === 'Escape') { close(); document.removeEventListener('keydown', esc2); }
  });
  document.body.appendChild(scrim);
}
const provRow = (dl, k, v) => { const d = el('div'); d.appendChild(el('dt', null, k)); d.appendChild(el('dd', null, v)); dl.appendChild(d); };

function termSheet(key) {
  const g = GLOSSARY[key];
  if (!g) { toast('No glossary entry for <b>' + esc(key) + '</b>.'); return; }
  sheet(s => {
    s.appendChild(el('h2', null, g.qual.split('.').pop()));
    s.appendChild(el('p', 'qual', g.qual));
    const dl = el('dl', 'prov');
    provRow(dl, 'Origin', g.origin === 'project' ? REPO : 'Mathlib @ ' + MATHLIB_REV);
    provRow(dl, 'Location', g.file);
    provRow(dl, 'Toolchain', TOOLCHAIN);
    s.appendChild(dl);
    const pre = el('pre', 'lean'); pre.textContent = g.sig; s.appendChild(pre);
    s.appendChild(el('p', 'gloss', g.gloss));
    if (g.warn) {
      const w = el('p', 'disclaim');
      w.innerHTML = '<span class="pill warn">caution</span> ' + esc(g.warn);
      s.appendChild(w);
    }
    const row = el('div', 'row'); row.style.marginTop = '14px';
    const d = el('button', 'act stub primary', 'Open in Mathlib docs');
    d.onclick = () => stub('Mathlib docs', 'Opens ' + g.qual + ' on leanprover-community.github.io pinned to ' + MATHLIB_REV);
    row.appendChild(d);
    const a = el('button', 'act stub', 'Explain this');
    a.onclick = () => stub('Explain this', 'Asks Claude for a gloss through the Mac — a public static page cannot hold an API key, so this needs the proxy in P11.3');
    row.appendChild(a);
    s.appendChild(row);
    s.appendChild(el('p', 'disclaim', 'The signature above was read verbatim from the checkout on disk. It is not re-verified at view time.'));
  });
}

/* ───────────────────────── REVIEW ─────────────────────────
 * The kernel checks proofs. It cannot check that a definition means the right
 * thing, so this room is that check: the statement of the target theorem and the
 * definitions it rests on, leaves first. */
const TARGET = REVIEW.targets[0];
const DECLS = new Map(REVIEW.decls.map(d => [d.name, d]));
const STATE_LABEL = {
  approved: ['Approved', 'ok'], flagged: ['Flagged', 'stop'], stale: ['Changed', 'warn'],
  unsure: ['Not sure', 'warn'], unreviewed: ['To review', ''],
};
let VERDICTS = [];
let STORAGE_OK = true;
let CARD = null;

const shortName = n => n.startsWith('instance#') ? 'instance ' + n.split('#').pop() + ' in ' + n.split('#')[1].split('/').pop() : n;
const statusFor = d => statusOf(d, latestEvents(VERDICTS, REVIEW.repo), REVIEW);
const statePill = st => el('span', 'pill ' + STATE_LABEL[st][1], STATE_LABEL[st][0]);
const sourceUrl = d => 'https://github.com/' + REVIEW.repo + '/blob/' + REVIEW.rev + '/' + d.file + '#L' + d.line + '-L' + d.endLine;

function openCard(name) {
  CARD = name;
  if (ROOM === 'review') { renderReview(); window.scrollTo(0, 0); } else go('review');
}

function renderReview() {
  if (CARD && DECLS.has(CARD)) renderCard(DECLS.get(CARD)); else renderQueue();
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
  return parts.join(', ') + '.';
}

function renderQueue() {
  const v = $('#view-review'); v.textContent = '';
  const { base, counts, trusted } = summarize(TARGET, VERDICTS, REVIEW);

  if (!STORAGE_OK) {
    const a = el('div', 'alert stop'); a.style.marginBottom = '13px';
    a.append(el('div', 'meta', 'Storage unavailable'), el('p', null, 'This browser is not letting the app save, so verdicts would be lost. Try the installed app, outside private browsing.'));
    v.appendChild(a);
  }

  const t = el('div', 'card trust' + (trusted ? ' done' : ''));
  t.appendChild(el('div', 'meta', 'The statement you are checking'));
  const pre = el('pre', 'lean wrap'); pre.style.marginTop = '9px'; pre.textContent = DECLS.get(TARGET).code;
  t.appendChild(pre);
  const budget = el('div', 'budget'); budget.style.marginTop = '12px';
  budget.append(el('span', null, 'Approved and current'), el('span', null, counts.approved + ' of ' + counts.total));
  t.appendChild(budget);
  const bar = el('div', 'bar'), fill = el('i');
  fill.style.width = (counts.approved / counts.total * 100) + '%';
  bar.appendChild(fill); t.appendChild(bar);
  t.appendChild(el('p', null, trusted
    ? 'You have read everything this statement rests on and approved its meaning. Lean checks the proof separately, with lake build.'
    : trustSentence(counts)));
  const next = nextInQueue(TARGET, VERDICTS, REVIEW);
  if (next) {
    const row = el('div', 'row'); row.style.marginTop = '12px';
    const go1 = el('button', 'act primary', 'Review next: ' + shortName(next.name));
    go1.onclick = () => openCard(next.name);
    row.appendChild(go1); t.appendChild(row);
  } else if (counts.flagged) {
    t.appendChild(el('p', null, 'Only flagged items remain. They clear when the Lean changes or you re-review them.'));
  }
  v.appendChild(t);

  const list = el('div', 'card section');
  list.appendChild(el('div', 'meta', 'Behind this theorem, leaves first'));
  base.forEach(({ decl }) => list.appendChild(queueRow(decl)));
  v.appendChild(list);

  const others = REVIEW.decls.filter(d => !d.root);
  if (others.length) {
    const o = el('details', 'card section');
    o.appendChild(el('summary', null, 'Other definitions (' + others.length + ')'));
    o.appendChild(el('p', 'disclaim', TARGET + '’s statement does not mention these, so a wrong one here cannot make it say the wrong thing. Proofs may still use them; Lean checks that.'));
    others.forEach(d => o.appendChild(queueRow(d)));
    v.appendChild(o);
  }

  const led = el('div', 'card section');
  led.appendChild(el('div', 'meta', 'Your verdicts'));
  led.appendChild(el('p', 'lede', VERDICTS.length + ' saved on this device only. Export them to keep a copy or to check them on the Mac.'));
  const row = el('div', 'row'); row.style.marginTop = '11px';
  const ex = el('button', 'act', 'Export'); ex.onclick = exportLedger;
  const im = el('button', 'act', 'Import'); im.onclick = () => $('#ledger-file').click();
  row.append(ex, im); led.appendChild(row);
  v.appendChild(led);

  const sorries = Object.keys(REVIEW.sorries).length;
  v.appendChild(el('p', 'disclaim', REVIEW.repo + ' @ ' + REVIEW.rev.slice(0, 7) + ' · ' + REVIEW.toolchain + ' · Mathlib ' + (REVIEW.mathlib || '?').slice(0, 10) +
    ' · ' + (sorries ? 'sorry in ' + sorries + ' file(s)' : 'no sorry') + ' · ' + (REVIEW.axioms.length ? REVIEW.axioms.length + ' axiom(s)' : 'no axioms') +
    '. Dependencies are read from source text, not elaborated, so Lean could still use something this list misses.'));
}

/* Lean with its known names tappable. Everything goes through text nodes. */
function leanWithTerms(d) {
  const pre = el('pre', 'lean wrap'); pre.style.marginTop = '9px';
  const code = d.code;
  const local = new Map();
  for (const dep of d.deps) { local.set(dep, dep); local.set(dep.split('.').pop(), dep); }
  let at = 0;
  for (const m of code.matchAll(/[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*/gu)) {
    const tok = m[0];
    const project = code[m.index - 1] === '.' ? null : local.get(tok);
    const g = GLOSSARY[tok];
    if (!project && !(g && g.origin === 'mathlib')) continue;
    pre.appendChild(document.createTextNode(code.slice(at, m.index)));
    const b = el('button', 'term', tok);
    b.onclick = () => project ? declSheet(project) : termSheet(tok);
    pre.appendChild(b);
    at = m.index + tok.length;
  }
  pre.appendChild(document.createTextNode(code.slice(at)));
  return pre;
}

function claimBlock(d) {
  const wrap = el('div', 'section');
  wrap.appendChild(el('div', 'meta', 'What it claims'));
  if (d.doc) {
    wrap.appendChild(el('p', 'claim', d.doc));
    wrap.appendChild(el('p', 'disclaim', 'From the docstring: written with the code, so it is a claim to test, not independent evidence.'));
  } else {
    wrap.appendChild(el('p', 'claim none', 'No docstring. Judge the Lean against the mathematics you expect.'));
  }
  const g = GLOSSARY[d.name];
  if (g && g.origin === 'project') {
    wrap.appendChild(el('div', 'meta', 'Dojo note')).style.marginTop = '11px';
    wrap.appendChild(el('p', 'claim', g.gloss));
    if (g.warn) wrap.appendChild(el('p', 'disclaim', g.warn));
  }
  return wrap;
}

function staleBlock(d, st) {
  const a = el('div', 'alert'); a.style.marginTop = '13px';
  a.appendChild(el('div', 'meta', 'Changed since your ' + st.event.verdict + ' verdict on ' + new Date(st.event.at).toLocaleDateString()));
  describeStale(st.stale).forEach(s => a.appendChild(el('p', null, s)));
  if (st.event.note) a.appendChild(el('p', null, 'Your note: ' + st.event.note));
  if (st.event.code && st.event.code !== d.code) {
    const pre = el('pre', 'lean wrap diff'); pre.style.marginTop = '9px';
    lineDiff(st.event.code, d.code).forEach(l => pre.appendChild(
      el('span', l.t === '+' ? 'add' : l.t === '-' ? 'del' : null, l.t + ' ' + l.s)));
    a.appendChild(pre);
  }
  return a;
}

function renderCard(d) {
  const v = $('#view-review'); v.textContent = '';
  const st = statusFor(d);
  const back = el('button', 'back', '‹ All definitions');
  back.onclick = () => { CARD = null; renderReview(); window.scrollTo(0, 0); };
  v.appendChild(back);

  const c = el('div', 'card');
  const head = el('div', 'card-head');
  head.append(el('h2', null, shortName(d.name)), statePill(st.state));
  c.appendChild(head);
  const src = el('a', 'srcline', d.kind + ' · ' + d.file + ':' + d.line);
  src.href = sourceUrl(d); src.target = '_blank'; src.rel = 'noopener'; src.style.display = 'block';
  c.appendChild(src);
  if (st.stale && st.state === 'stale') c.appendChild(staleBlock(d, st));
  if (st.state === 'flagged') {
    const a = el('div', 'alert stop'); a.style.marginTop = '13px';
    a.append(el('div', 'meta', 'You flagged this'), el('p', null, st.event.note));
    c.appendChild(a);
  }
  if (d.hasSorry) {
    const a = el('div', 'alert stop'); a.style.marginTop = '13px';
    a.append(el('div', 'meta', 'Contains sorry'), el('p', null, 'Part of this declaration is unproved.'));
    c.appendChild(a);
  }
  c.appendChild(claimBlock(d));

  const lean = el('div', 'section');
  lean.appendChild(el('div', 'meta', 'The Lean' + (d.kind === 'theorem' || d.kind === 'lemma' ? ' (statement only: the kernel checks the proof)' : '')));
  lean.appendChild(leanWithTerms(d));
  c.appendChild(lean);
  if (d.kind === 'instance') c.appendChild(el('p', 'disclaim', 'An instance: Lean can use this silently wherever the types match, without the code naming it.'));

  if (d.scope.length) {
    const s = el('div', 'section');
    s.appendChild(el('div', 'meta', 'Also in scope'));
    const pre = el('pre', 'lean wrap'); pre.style.marginTop = '9px'; pre.textContent = d.scope.join('\n');
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
  f.appendChild(el('p', 'lede', 'Does this Lean mean what the mathematics should mean? Check the hypotheses and the edge cases. Approving says you read it, not that it compiles.'));
  const ta = el('textarea'); ta.id = 'verdict-note'; ta.style.marginTop = '10px';
  ta.placeholder = 'Note (required to flag)';
  f.appendChild(ta);
  const row = el('div', 'verdicts');
  const yes = el('button', 'act primary', 'Means the right thing');
  yes.onclick = () => record(d, 'approved', ta.value);
  const no = el('button', 'act danger', 'Flag mismatch');
  no.onclick = () => {
    if (!ta.value.trim()) { toast('Say what looks wrong, then flag.'); ta.focus(); return; }
    record(d, 'flagged', ta.value);
  };
  const unsure = el('button', 'act', 'Not sure');
  unsure.onclick = () => record(d, 'unsure', ta.value);
  row.append(yes, no, unsure);
  f.appendChild(row);
  v.appendChild(f);

  const hist = VERDICTS.filter(e => e.repo === REVIEW.repo && e.decl === d.name).sort((a, b) => b.at - a.at);
  if (hist.length) {
    const h = el('div', 'card section');
    h.appendChild(el('div', 'meta', 'History'));
    hist.forEach(e => h.appendChild(el('div', 'hist',
      new Date(e.at).toLocaleString() + ' · ' + e.verdict + ' · ' + (e.rev || '').slice(0, 7) + (e.note ? ' · ' + e.note : ''))));
    v.appendChild(h);
  }
}

function declSheet(name) {
  const d = DECLS.get(name);
  if (!d) { toast('Not in the review data.'); return; }
  sheet((s, close) => {
    const head = el('div', 'card-head');
    head.append(el('h2', null, shortName(d.name)), statePill(statusFor(d).state));
    s.appendChild(head);
    s.appendChild(el('p', 'qual', d.kind + ' · ' + d.file + ':' + d.line));
    if (d.doc) s.appendChild(el('p', 'gloss', d.doc));
    const pre = el('pre', 'lean wrap'); pre.textContent = d.code; s.appendChild(pre);
    const row = el('div', 'row'); row.style.marginTop = '14px';
    const o = el('button', 'act primary', 'Review this one');
    o.onclick = () => { close(); openCard(d.name); };
    row.appendChild(o); s.appendChild(row);
  });
}

async function record(d, verdict, note) {
  let ev;
  try { ev = makeEvent(d, verdict, note, REVIEW); } catch (e) { toast(esc(e.message)); return; }
  // Never show a verdict as recorded unless it reached storage.
  try { await putVerdict(ev); } catch (e) { toast('<b>Not saved.</b> Storage refused the write, so nothing was recorded.', 5000); return; }
  VERDICTS.push(ev);
  navigator.storage?.persist?.().catch(() => {});
  const next = d.root ? nextInQueue(TARGET, VERDICTS, REVIEW, d.name) : null;
  CARD = next ? next.name : null;
  renderReview();
  window.scrollTo(0, 0);
  toast(esc(shortName(d.name)) + ': ' + esc(verdict) + '. Saved on this device.', 2200);
}

async function exportLedger() {
  if (!VERDICTS.length) { toast('No verdicts to export yet.'); return; }
  const stamp = new Date().toISOString().slice(0, 10);
  const text = serializeLedger(VERDICTS, REVIEW, new Date().toISOString());
  await shareFile(new File([text], 'dojo-reviews-' + stamp + '.json', { type: 'application/json' }), 'Dojo reviews');
}

$('#ledger-file').addEventListener('change', async e => {
  const f = e.target.files && e.target.files[0];
  e.target.value = '';
  if (!f) return;
  try {
    const { events, skipped } = parseLedger(await f.text());
    const have = new Set(VERDICTS.map(x => x.id));
    const fresh = events.filter(x => !have.has(x.id));
    for (const x of fresh) await putVerdict(x);
    VERDICTS.push(...fresh);
    renderReview();
    toast('Imported ' + fresh.length + ' new verdict(s)' + (skipped ? ', ignored ' + skipped + ' malformed' : '') + '.');
  } catch (err) {
    toast('<b>Import failed.</b> ' + esc(err.message || 'Unreadable file.'), 5000);
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
    p.innerHTML = par.replace(/\{(\w+)\}/g, (m, k) => {
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
  const pre = el('pre', 'lean'); pre.style.marginTop = '9px';
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
let qi = 0, answered = [];
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
    again.onclick = () => { qi = 0; answered = []; renderDecide(); };
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
  Q.opts.forEach(o => {
    const b = el('button', 'choice');
    b.appendChild(el('span', null, o.t));
    b.onclick = () => {
      if (b.dataset.state) return;
      wrap.querySelectorAll('.choice').forEach((x, i) => {
        x.dataset.state = Q.opts[i].ok ? 'right' : 'wrong';
        x.appendChild(el('small', null, Q.opts[i].why));
      });
      answered[qi] = !!o.ok;
      prog.children[qi].className = 'on';
      const nav = el('div', 'row'); nav.style.marginTop = '13px';
      const cite = el('div', 'srcline', Q.cite); cite.style.flex = '1 1 100%';
      const next = el('button', 'act primary', qi === QUESTIONS.length - 1 ? 'Finish' : 'Next');
      next.onclick = () => { qi++; renderDecide(); };
      nav.append(cite, next);
      c.appendChild(nav);
      next.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    };
    wrap.appendChild(b);
  });
  c.appendChild(wrap);
  v.appendChild(c);
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
    b.onclick = () => { const wasSel = sel === n.id; sel = wasSel ? null : n.id; renderMap(); if (!wasSel) nodeSheet(n); };
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
  v.appendChild(el('p', 'lede', 'Pick what survives losing the Mac. This page itself is already cached by its service worker — reload it in airplane mode and it opens.'));

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
let pendingBlob = null;
function renderNotes() {
  const v = $('#view-notes'); v.textContent = '';
  v.appendChild(el('p', 'lede', 'What you want changed. Screenshot on the phone, mark it up in Photos, then attach it here. Notes stay on this device — there is no backend.'));

  const c = el('div', 'card'); c.style.marginTop = '12px';
  const ta = el('textarea'); ta.id = 'note-text';
  ta.placeholder = 'What should be different? Which screen?';
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
      im.onload = () => URL.revokeObjectURL(im.src);
      it.appendChild(im);
    }
    const del = el('button', 'act', 'Delete'); del.style.flex = '0 0 auto';
    del.onclick = async () => { NOTES = NOTES.filter(x => x.id !== n.id); await dropNote(n.id); renderNotes(); };
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
  const note = { id: 'n' + Date.now() + Math.random().toString(36).slice(2, 6), text, room: ROOM, at: Date.now(), blob: pendingBlob || null };
  NOTES.push(note);
  pendingBlob = null;
  try { await putNote(note); } catch (err) { toast('Shown here but not saved — storage error.'); }
  renderNotes();
}

/* Share sheet is the only reliable way to get a file off iOS Safari. */
async function shareFile(file, title) {
  if (navigator.canShare && navigator.canShare({ files: [file] })) {
    try { await navigator.share({ files: [file], title }); return true; } catch (e) { if (e.name === 'AbortError') return false; }
  }
  const url = URL.createObjectURL(file);
  const a = el('a'); a.href = url; a.download = file.name; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 4000);
  return true;
}

async function exportNotes() {
  if (!NOTES.length) { toast('Nothing to export yet.'); return; }
  const body = NOTES.slice().sort((a, b) => a.at - b.at)
    .map(n => '## ' + (n.room || '?') + '  ·  ' + new Date(n.at).toISOString() + '\n\n' + (n.text || '') +
      (n.blob ? '\n\n(screenshot attached in the app — export images separately)' : '')).join('\n\n---\n\n');
  const md = '# Ulm Dojo — change requests\n\n' + body + '\n';
  await shareFile(new File([md], 'dojo-notes.md', { type: 'text/markdown' }), 'Dojo notes');
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
  go('notes');
  const ta = $('#note-text');
  if (ta) { ta.value = '[' + ROOMS[from].eyebrow + '] '; ta.focus(); ta.setSelectionRange(ta.value.length, ta.value.length); }
};

$('#btn-about').onclick = () => sheet(s => {
  s.appendChild(el('h2', null, 'What this is'));
  s.appendChild(el('p', 'gloss', 'A phone tool for checking that Lean says what it claims. Lean’s kernel checks proofs; it cannot check that a definition means the right thing. Review is that human check. The other rooms are the original evaluation harness.'));
  const dl = el('dl', 'prov');
  provRow(dl, 'Real', 'Review is generated from ' + REVIEW.repo + ' @ ' + REVIEW.rev.slice(0, 7) + ': every declaration, hash and dependency. Verdicts are saved on this device.');
  provRow(dl, 'Mathlib', 'Signatures from the pinned checkout, commit ' + MATHLIB_REV + '.');
  provRow(dl, 'Not real', 'Nothing compiles, dispatches a job, or syncs. Dependencies come from source text, not elaboration. Controls marked ◌ say what they would do.');
  provRow(dl, 'Privacy', 'Static page, no backend, no analytics. Notes and verdicts leave this device only when you export them.');
  s.appendChild(dl);
  s.appendChild(el('p', 'disclaim', 'Install: Safari share menu → Add to Home Screen. Once installed it opens offline.'));
  const row = el('div', 'row'); row.style.marginTop = '10px';
  const u = el('button', 'act', 'Check for update');
  u.onclick = async () => {
    const r = await navigator.serviceWorker?.getRegistration();
    if (!r) { toast('No service worker registered in this context.'); return; }
    await r.update(); toast('Checked. A new version installs on next launch.');
  };
  row.appendChild(u);
  s.appendChild(row);
});

window.addEventListener('online',  () => { if (ROOM === 'carry') renderCarry(); });
window.addEventListener('offline', () => { if (ROOM === 'carry') renderCarry(); });

go('review');
loadNotes().then(n => { NOTES = n || []; if (ROOM === 'notes') renderNotes(); });
loadVerdicts()
  .then(v => { VERDICTS = v || []; })
  .catch(() => { STORAGE_OK = false; })
  .then(() => { if (ROOM === 'review') renderReview(); });

if ('serviceWorker' in navigator) {
  window.addEventListener('load', () => navigator.serviceWorker.register('sw.js').catch(() => {}));
}
