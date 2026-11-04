/* Text-level extraction of Lean 4 declarations for human review.
 *
 * Deliberately not an elaborator: it reads source, so it needs no Mathlib build.
 * That makes two rules matter. Dependencies are over-approximated: every plausible
 * reading of a name is kept. And anything it cannot read stops the build with
 * UnsupportedLean, because a skipped declaration would quietly shrink the queue.
 *
 * It still cannot see what only elaboration reveals, such as an instance that does
 * not name a reviewed definition. The UI says so.
 *
 * What the hashes cover:
 *   ownHash  : kind, name, comment-free whitespace-normalised text, active scope.
 *              For a theorem, the statement only: the kernel checks proofs.
 *   deepHash : the own hashes of the declaration's whole dependency closure.
 */
import { createHash } from 'node:crypto';

export class UnsupportedLean extends Error {}

const MODIFIER_RE = /^(?:private|protected|public|meta|noncomputable|unsafe|partial|nonrec|local|scoped)(?=\s)/u;
const DECL_RE = /^(class\s+inductive|def|abbrev|theorem|lemma|instance|structure|class|inductive|axiom|opaque|example)(?![\p{L}\p{N}_'.])/u;
const WORD_RE = /^#?[\p{L}_][\p{L}\p{N}_'!?]*/u;
const TOKEN_RE = /(?:«[^»]+»|[\p{L}_][\p{L}\p{N}_'!?]*)(?:\.(?:«[^»]+»|[\p{L}_][\p{L}\p{N}_'!?]*))*/gu;
const IDENT_CHAR = /[\p{L}\p{N}_'!?]/u;

const SCOPED = new Set(['variable', 'open', 'universe', 'attribute', 'set_option', 'omit', 'include', 'export',
  'notation', 'infixl', 'infixr', 'infix', 'prefix', 'postfix']);
const NOTATION = new Set(['notation', 'notation3', 'infixl', 'infixr', 'infix', 'prefix', 'postfix']);
const KNOWN = new Set([...SCOPED, 'notation3', 'namespace', 'section', 'end', 'import', 'mutual',
  'macro', 'macro_rules', 'syntax', 'elab', 'elab_rules', 'initialize', 'deriving']);
const INDENT_FORBIDDEN = new Set(['variable', 'universe', 'namespace', 'section', 'mutual', 'macro', 'macro_rules',
  'syntax', 'elab', 'elab_rules', 'initialize', ...NOTATION]);
const CONTINUATION = new Set(['deriving', 'where', 'with', 'extends', 'termination_by', 'decreasing_by', 'by']);

export const DEF_KINDS = new Set(['def', 'abbrev', 'structure', 'class', 'class inductive', 'inductive', 'axiom', 'opaque', 'instance']);
const THEOREM_KINDS = new Set(['theorem', 'lemma']);

const sha = s => createHash('sha256').update(s).digest('hex').slice(0, 16);
const normalize = s => s.replace(/\s+/g, ' ').trim();

/* Two views of a file with every offset kept. `masked` blanks comments; `scan` also
 * blanks string and char literals, so their contents can never look like syntax. */
export function maskComments(src) {
  const masked = src.split('');
  const scan = src.split('');
  const comments = [], literals = [];
  const blank = (arr, a, b) => { for (let k = a; k < b; k++) if (arr[k] !== '\n') arr[k] = ' '; };
  const literal = (a, b) => { blank(scan, a, b); literals.push([a, b]); };
  let i = 0;
  while (i < src.length) {
    const before = i ? src.slice(Math.max(0, i - 2), i) : '';
    const afterIdent = IDENT_CHAR.test([...before].pop() || '');
    if (src[i] === 'r' && !afterIdent) {
      const m = src.slice(i, i + 40).match(/^r(#*)"/);
      if (m) {
        const close = src.indexOf('"' + m[1], i + m[0].length);
        const end = close < 0 ? src.length : close + 1 + m[1].length;
        literal(i, end);
        i = end;
        continue;
      }
    }
    if (src[i] === '"') {
      const start = i++;
      while (i < src.length && src[i] !== '"') i += src[i] === '\\' ? 2 : 1;
      i++;
      literal(start, i);
    } else if (src[i] === "'" && !afterIdent) {
      const m = src.slice(i, i + 12).match(/^'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'/u);
      if (m) { literal(i, i + m[0].length); i += m[0].length; } else i++;
    } else if (src.startsWith('--', i)) {
      const nl = src.indexOf('\n', i);
      const end = nl < 0 ? src.length : nl;
      blank(masked, i, end); blank(scan, i, end);
      i = end;
    } else if (src.startsWith('/-', i)) {
      const start = i;
      const kind = src.startsWith('/--', i) && !src.startsWith('/--/', i) ? 'doc' : src.startsWith('/-!', i) ? 'module' : 'block';
      let depth = 1;
      i += 2;
      while (i < src.length && depth) {
        if (src.startsWith('/-', i)) { depth++; i += 2; }
        else if (src.startsWith('-/', i)) { depth--; i += 2; }
        else i++;
      }
      if (depth) throw new UnsupportedLean('unterminated block comment at offset ' + start);
      comments.push({ start, end: i, kind, text: src.slice(start, i) });
      blank(masked, start, i); blank(scan, start, i);
    } else i++;
  }
  return { masked: masked.join(''), scan: scan.join(''), comments, literals };
}

const OPEN = new Set(['(', '[', '{', '⟨', '⦃', '⟦']);
const CLOSE = new Set([')', ']', '}', '⟩', '⦄', '⟧']);

/* Offset where the signature stops, reading text with literals blanked. A `:=` that
 * belongs to a `let` or `have`, and a bar inside a `match` or an absolute value, are
 * part of the statement: cutting there would hide the rest of it from the reviewer. */
export function headerEnd(text) {
  let depth = 0, binders = 0, inMatch = false;
  const word = at => (text.slice(at).match(WORD_RE) || [''])[0];
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (OPEN.has(c)) { depth++; continue; }
    if (CLOSE.has(c)) { depth--; continue; }
    if (depth) continue;
    if (text.startsWith(':=', i)) {
      if (binders) { binders--; i++; continue; }
      return i;
    }
    if (c === '|' && /\n\s*$/.test(text.slice(0, i)) && !inMatch) {
      const line = text.slice(i, (text.indexOf('\n', i) + 1 || text.length + 1) - 1);
      if (/=>/.test(line)) return i;
    }
    if (IDENT_CHAR.test(c) && !IDENT_CHAR.test(text[i - 1] || ' ')) {
      const w = word(i);
      if (w === 'where') return i;
      if (w === 'let' || w === 'have') binders++;
      if (w === 'match') inMatch = true;
      i += Math.max(0, w.length - 1);
    }
  }
  return text.length;
}

function lineOf(src, offset) {
  let n = 1;
  for (let i = 0; i < offset; i++) if (src[i] === '\n') n++;
  return n;
}

/* Modifiers and attributes, then whatever word follows. */
function parseHead(t) {
  let i = 0;
  const attrs = [];
  for (;;) {
    while (/\s/.test(t[i] || '')) i++;
    if (t.startsWith('@[', i)) {
      let depth = 0, k = i + 1;
      for (; k < t.length; k++) {
        if (t[k] === '[') depth++;
        else if (t[k] === ']' && --depth === 0) break;
      }
      attrs.push(t.slice(i + 2, k));
      i = k + 1;
      continue;
    }
    const m = t.slice(i, i + 20).match(MODIFIER_RE);
    if (m) { i += m[0].length; continue; }
    break;
  }
  const rest = t.slice(i);
  const decl = rest.match(DECL_RE);
  if (decl) return { type: 'decl', kind: decl[1].replace(/\s+/, ' '), len: i + decl[0].length, attrs };
  const w = (rest.match(WORD_RE) || [''])[0];
  return { type: 'word', word: w, len: i + w.length, attrs, modified: i > 0, local: /(^|\s)(local|scoped)\s/.test(t.slice(0, i + 1)) };
}

function declName(afterKind, kind) {
  const m = afterKind.match(/^\s*(?:\(priority[^)]*\)\s*)?(«[^»]+»(?:\.(?:«[^»]+»|[^\s:({[⦃.]+))*|[^\s:({[⦃«]+)?/u);
  const name = m && m[1] && m[1].replace(/\.$/, '');
  if (!name || name === 'where') return null;
  if (kind === 'instance' && name.startsWith(':')) return null;
  return name;
}

function docBefore(src, comments, start) {
  for (let k = comments.length - 1; k >= 0; k--) {
    const c = comments[k];
    if (c.end > start) continue;
    if (src.slice(c.end, start).trim() !== '') return null;
    if (c.kind !== 'doc') return null;
    return c.text.replace(/^\/--/, '').replace(/-\/$/, '').trim();
  }
  return null;
}

function parseOpen(text) {
  const body = text.replace(/\s+in$/, '').replace(/^(?:(?:local|scoped)\s+)*(?:open|export)\s+(?:scoped\s+)?/, '');
  const opens = [], aliases = [];
  const words = body.split(/\s+/);
  let k = 0;
  for (; k < words.length; k++) {
    if (words[k] === 'hiding' || words[k] === 'renaming' || words[k].startsWith('(')) break;
    opens.push(words[k]);
  }
  const ns = opens.at(-1);
  const renaming = body.match(/\brenaming\s+(.*)$/);
  if (renaming && ns) {
    for (const pair of renaming[1].split(',')) {
      const m = pair.match(/(\S+)\s*(?:→|->)\s*(\S+)/);
      if (m) aliases.push([m[2], ns + '.' + m[1]]);
    }
  }
  return { opens, aliases };
}

/* Whitespace runs collapse, except inside literals, where a space is meaning. */
function normalizeRange(masked, literals, a, b) {
  let out = '', i = a;
  for (const [s, e] of literals) {
    if (e <= a || s >= b) continue;
    out += masked.slice(i, s).replace(/\s+/g, ' ') + masked.slice(s, e);
    i = e;
  }
  return (out + masked.slice(i, b).replace(/\s+/g, ' ')).trim();
}

function fileRefs(comments) {
  for (const c of comments) {
    if (c.kind !== 'module') continue;
    const m = c.text.match(/##\s*References\s*\n((?:[ \t]*-(?!\/)[^\n]*\n?)+)/);
    if (m) return m[1].split('\n').map(l => l.replace(/^\s*-\s*/, '').trim()).filter(Boolean);
  }
  return [];
}

/* Every declaration in one file, with its namespace and active scope. */
export function parseFile(file, src) {
  const { masked, scan, comments, literals } = maskComments(src);
  const stop = (at, why) => { throw new UnsupportedLean(file + ':' + lineOf(src, at) + ': ' + why); };

  const starts = [];
  let consumed = 0, depth = 0, depthAt = 0;
  for (let i = 0; i < scan.length;) {
    const nl = scan.indexOf('\n', i);
    const end = nl < 0 ? scan.length : nl;
    let j = i;
    while (j < end && /\s/.test(scan[j])) j++;
    if (j < end && j >= consumed) {
      for (; depthAt < j; depthAt++) {
        if (OPEN.has(scan[depthAt])) depth++;
        else if (CLOSE.has(scan[depthAt])) depth--;
      }
      const afterComment = j > i && src.slice(i, j).trim() !== '';
      const topLevel = j === i || afterComment;
      const head = parseHead(scan.slice(j, j + 400));
      const isCommand = head.type === 'decl' || KNOWN.has(head.word) || head.word.startsWith('#');
      if (topLevel && isCommand && !(head.word === 'deriving' && !/^deriving\s+instance\b/.test(scan.slice(j, j + 40)))) {
        starts.push({ at: j, ...head });
        consumed = j + head.len;
        depth = 0; depthAt = j;
      } else if (topLevel && !isCommand && depth <= 0 && !CONTINUATION.has(head.word) && !CLOSE.has(scan[j]) && !/^(?:\||:=|·)/.test(scan.slice(j, j + 2))) {
        stop(j, 'unrecognised command "' + scan.slice(j, end).trim().slice(0, 40) + '"');
      } else if (!topLevel && (head.type === 'decl' || INDENT_FORBIDDEN.has(head.word))) {
        stop(j, 'indented command "' + scan.slice(j, end).trim().slice(0, 40) + '"');
      }
    }
    i = end + 1;
  }

  const decls = [], imports = [], instanceNames = [], exportsOut = [];
  const frames = [{ type: 'file', name: '', scope: [] }];
  const anonSeen = new Map();
  let prefixText = '', prefixRaw = '', prefixOpens = [], prefixAliases = [], prefixStart = null;
  const resetPrefix = () => { prefixText = ''; prefixRaw = ''; prefixOpens = []; prefixAliases = []; prefixStart = null; };

  starts.forEach((cmd, idx) => {
    const end = idx + 1 < starts.length ? starts[idx + 1].at : masked.length;
    const maskedText = masked.slice(cmd.at, end);
    const scanText = scan.slice(cmd.at, end);
    const rawText = src.slice(cmd.at, end);
    const text = normalize(scanText);
    const word = cmd.word;

    if (cmd.type !== 'decl') {
      if (word === 'import') { imports.push(...text.replace(/^.*?\bimport\s+/, '').split(/\s+/).filter(w => w !== 'all')); return; }
      if (word === 'mutual') stop(cmd.at, 'mutual blocks are not supported yet');
      if (word === 'deriving') stop(cmd.at, '"deriving instance" is not supported yet');
      if (['macro', 'macro_rules', 'syntax', 'elab', 'elab_rules', 'initialize'].includes(word)) stop(cmd.at, word + ' can change what later code means, and is not supported yet');
      if (NOTATION.has(word) && !cmd.local) stop(cmd.at, 'non-local notation cannot be followed across files');
      if (word === 'namespace') {
        for (const part of text.split(/\s+/)[1].split('.')) frames.push({ type: 'namespace', name: part, scope: [] });
        resetPrefix();
        return;
      }
      if (word === 'section') {
        const name = text.split(/\s+/).at(-1);
        frames.push({ type: 'section', name: name === 'section' ? '' : name, scope: [] });
        resetPrefix();
        return;
      }
      if (word === 'end') {
        const name = text.split(/\s+/)[1];
        const parts = name ? name.split('.').length : 1;
        for (let k = 0; k < parts; k++) {
          if (frames.length === 1) stop(cmd.at, 'end without a matching namespace or section');
          frames.pop();
        }
        resetPrefix();
        return;
      }
      if ((word === 'open' || word === 'set_option') && /\sin$/.test(text)) {
        prefixText += normalizeRange(masked, literals, cmd.at, end) + ' ';
        prefixRaw += rawText.slice(0, maskedText.replace(/\s+$/, '').length) + '\n';
        if (word === 'open') {
          const o = parseOpen(text);
          prefixOpens.push(...o.opens);
          prefixAliases.push(...o.aliases);
        }
        if (prefixStart === null) prefixStart = cmd.at;
        return;
      }
      if ((word === 'open' || word === 'set_option') && /\bin\s+\S/.test(text)) stop(cmd.at, '"' + word + ' … in" on one line with its command is not supported yet');
      resetPrefix();
      if (word === 'attribute') {
        const m = text.match(/\[([^\]]*\binstance\b[^\]]*)\]\s*(.*)$/);
        if (m) instanceNames.push(...m[2].split(/\s+/).filter(Boolean));
      }
      if (word === 'export') exportsOut.push(...parseOpen(text).opens);
      if (SCOPED.has(word) || NOTATION.has(word)) {
        frames[frames.length - 1].scope.push(normalizeRange(masked, literals, cmd.at, end));
      }
      return;
    }

    const usedText = prefixText, usedRaw = prefixRaw, firstAt = prefixStart ?? cmd.at;
    const usedOpens = prefixOpens, usedAliases = prefixAliases;
    resetPrefix();
    if (cmd.kind === 'example') return;

    const after = scanText.slice(cmd.len);
    const short = declName(after, cmd.kind);
    const headerAt = headerEnd(scanText);
    const header = normalize(scanText.slice(cmd.len, headerAt));
    const ns = frames.filter(f => f.type === 'namespace').map(f => f.name);
    let name;
    if (short) {
      name = short.startsWith('_root_.') ? short.slice(7) : [...ns, short].join('.');
    } else {
      const key = sha(header).slice(0, 8);
      const n = (anonSeen.get(key) || 0) + 1;
      anonSeen.set(key, n);
      name = 'instance#' + file + '#' + key + (n > 1 ? '-' + n : '');
    }
    const scope = frames.flatMap(f => f.scope);
    const openStates = scope.filter(s => /^(?:(?:local|scoped)\s+)*open\b/.test(s)).map(parseOpen);
    const isThm = THEOREM_KINDS.has(cmd.kind);
    const formalEnd = cmd.at + (isThm ? headerAt : scanText.length);
    // Stop at the last real token, so the next declaration's docstring stays out.
    const shownLen = masked.slice(cmd.at, formalEnd).replace(/\s+$/, '').length;

    decls.push({
      name, kind: cmd.kind, file,
      line: lineOf(src, firstAt),
      endLine: lineOf(src, cmd.at + shownLen),
      doc: docBefore(src, comments, firstAt),
      code: usedRaw + rawText.slice(0, shownLen),
      scope,
      namespaces: name.split('.').slice(0, -1),
      opens: [...openStates.flatMap(o => o.opens), ...usedOpens],
      aliases: [...openStates.flatMap(o => o.aliases), ...usedAliases],
      formal: (usedText + normalizeRange(masked, literals, cmd.at, cmd.at + shownLen)).trim(),
      formalScan: normalize(scan.slice(firstAt, cmd.at + shownLen)),
      header,
      isInstance: cmd.kind === 'instance' || cmd.attrs.some(a => /\binstance\b/.test(a)),
      ctors: /inductive$/.test(cmd.kind)
        ? [...scanText.slice(cmd.len).matchAll(/\|\s*([^\s:({[]+)/gu)].map(m => m[1]) : [],
      hasSorry: /\b(?:sorry|admit|sorryAx)\b/.test(scanText),
    });
  });
  if (frames.length > 1) stop(src.length, 'unclosed namespace or section "' + frames.at(-1).name + '"');
  const count = re => (scan.match(re) || []).length;
  return {
    decls, imports, instanceNames, exportsOut, refs: fileRefs(comments),
    sorries: count(/\b(?:sorry|admit|sorryAx)\b/g),
    risky: ['native_decide', 'implemented_by', 'extern', 'unsafe'].filter(w => new RegExp('\\b' + w + '\\b').test(scan)),
  };
}

function tokens(text) {
  const named = new Set(), fields = new Set();
  for (const m of text.matchAll(TOKEN_RE)) {
    if (text[m.index - 1] === '.') fields.add(m[0]);  // `.foo`, `(x).foo`, `x |>.foo`
    else named.add(m[0]);
  }
  return { named, fields };
}

/* Every declaration a token could mean, not just the first: a wrong guess only adds
 * something to read, while a missed one hides it. */
function resolver(names, ctors) {
  const byLast = new Map();
  for (const n of names) {
    if (!n.includes('.')) continue;
    const last = n.split('.').pop();
    if (!byLast.has(last)) byLast.set(last, []);
    byLast.get(last).push(n);
  }
  const lookup = q => (names.has(q) ? [q] : ctors.has(q) ? [ctors.get(q)] : []);
  const ending = part => byLast.get(part) || [];
  return {
    named(tok, d, globalOpens) {
      const out = new Set();
      const add = xs => xs.forEach(x => out.add(x));
      for (const [alias, full] of d.aliases) if (tok === alias || tok.startsWith(alias + '.')) add(lookup(full));
      if (tok.startsWith('_root_.')) { add(lookup(tok.slice(7))); return out; }
      const prefixes = [''];
      for (let i = 1; i <= d.namespaces.length; i++) prefixes.push(d.namespaces.slice(0, i).join('.'));
      for (const o of [...d.opens, ...globalOpens]) {
        for (const p of [...prefixes]) prefixes.push(p ? p + '.' + o : o);
      }
      const parts = tok.split('.');
      for (const p of prefixes) {
        for (let n = parts.length; n >= 1; n--) {
          const q = parts.slice(0, n).join('.');
          add(lookup(p ? p + '.' + q : q));
        }
      }
      // `s.g.h` is field notation: without types, take every `X.g` and `X.h`.
      for (const part of parts.slice(1)) add(ending(part));
      return out;
    },
    field: tok => tok.split('.').flatMap(ending),
  };
}

/* Import order, so sorting by (file, line) follows declare-before-use. */
function fileOrder(files) {
  const order = [], seen = new Set();
  const moduleOf = f => f.replace(/\.lean$/, '').replace(/\//g, '.');
  const byModule = new Map(Object.keys(files).map(f => [moduleOf(f), f]));
  const visit = f => {
    if (seen.has(f)) return;
    seen.add(f);
    for (const i of files[f].imports) if (byModule.has(i)) visit(byModule.get(i));
    order.push(f);
  };
  Object.keys(files).sort().forEach(visit);
  return new Map(order.map((f, i) => [f, i]));
}

/* Link declarations across files and compute hashes. `sources` maps relative path
 * to file contents. */
export function buildIndex(sources) {
  const files = {};
  for (const [f, src] of Object.entries(sources)) files[f] = parseFile(f, src);
  const order = fileOrder(files);
  const all = Object.values(files).flatMap(f => f.decls)
    .sort((a, b) => order.get(a.file) - order.get(b.file) || a.line - b.line);

  const byName = new Map();
  for (const d of all) {
    if (byName.has(d.name)) throw new UnsupportedLean(d.name + ' is declared twice (' + byName.get(d.name).file + ', ' + d.file + ')');
    byName.set(d.name, d);
  }
  for (const f of Object.values(files)) {
    for (const n of f.instanceNames) for (const d of all) if (d.name === n || d.name.endsWith('.' + n)) d.isInstance = true;
  }

  const defLike = new Set(all.filter(d => DEF_KINDS.has(d.kind)).map(d => d.name));
  const ctors = new Map();
  for (const d of all) for (const c of d.ctors) ctors.set(d.name + '.' + c, d.name);
  const resolve = resolver(defLike, ctors);
  const globalOpens = Object.values(files).flatMap(f => f.exportsOut);
  const depsIn = (text, d) => {
    const out = new Set();
    const { named, fields } = tokens(text);
    for (const t of named) resolve.named(t, d, globalOpens).forEach(n => out.add(n));
    for (const t of fields) resolve.field(t).forEach(n => out.add(n));
    out.delete(d.name);
    return out;
  };
  for (const d of all) {
    // Variable binders and local notation are part of what the declaration says.
    const assumed = d.scope.filter(s => /^(?:(?:local|scoped)\s+)*(?:variable|notation|infix|prefix|postfix)/.test(s)).join('\n');
    d.deps = [...new Set([...depsIn(d.formalScan, d), ...depsIn(assumed, d)])].sort();
    d.ownHash = sha([d.kind, d.name, d.formal, d.scope.join('\n')].join('\0'));
  }
  // An instance about X can change what code using X means without being named,
  // so it joins any closure containing X.
  const instances = all.filter(d => d.isInstance).map(d => ({ name: d.name, about: depsIn(d.header, d) }));

  const closureOf = d => {
    const seen = new Set();
    const stack = [...d.deps];
    for (;;) {
      while (stack.length) {
        const n = stack.pop();
        if (seen.has(n)) continue;
        seen.add(n);
        stack.push(...byName.get(n).deps);
      }
      const attached = instances.filter(i => !seen.has(i.name) &&
        [...i.about].some(a => a === d.name || seen.has(a)));
      if (!attached.length) break;
      stack.push(...attached.map(i => i.name));
    }
    seen.delete(d.name);
    return [...seen];
  };
  const rank = new Map(all.map((d, i) => [d.name, i]));
  for (const d of all) {
    d.closure = closureOf(d).sort((a, b) => rank.get(a) - rank.get(b));
    d.deepHash = sha([d.name + ':' + d.ownHash, ...d.closure.map(n => n + ':' + byName.get(n).ownHash).sort()].join('\n'));
  }

  const pick = fn => Object.fromEntries(Object.entries(files).map(([k, f]) => [k, fn(f)]).filter(([, v]) => v && (!Array.isArray(v) || v.length)));
  return {
    decls: all, byName,
    sorries: pick(f => f.sorries),
    risky: pick(f => f.risky),
    refs: pick(f => f.refs),
  };
}

/* The reviewable payload: every definition, plus the named targets' statements.
 * Theorems other than targets are the kernel's business, so they are left out. */
export function reviewPayload(index, targets) {
  for (const t of targets) if (!index.byName.has(t)) throw new Error('target not found: ' + t);
  const keep = d => DEF_KINDS.has(d.kind) || targets.includes(d.name);
  const rootSet = new Set(targets.flatMap(t => [t, ...index.byName.get(t).closure]));
  return {
    targets,
    decls: index.decls.filter(keep).map(d => ({
      name: d.name, kind: d.kind, file: d.file, line: d.line, endLine: d.endLine,
      doc: d.doc, code: d.code, scope: d.scope, deps: d.deps, closure: d.closure,
      ownHash: d.ownHash, deepHash: d.deepHash, hasSorry: d.hasSorry,
      root: rootSet.has(d.name),
    })),
    sorries: index.sorries,
    risky: index.risky,
    refs: index.refs,
    axioms: index.decls.filter(d => d.kind === 'axiom').map(d => d.name),
  };
}
