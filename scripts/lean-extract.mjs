/* Text-level extraction of Lean 4 declarations for human review.
 *
 * Deliberately not an elaborator: it reads source, so it needs no Mathlib build,
 * and it errs towards over-approximating dependencies. It cannot see what only
 * elaboration reveals (instances found by unification outside the attachment
 * rule below, macro expansion across files). The UI says so.
 *
 * What the hashes cover:
 *   ownHash  : kind, name, comment-free whitespace-normalised text, active scope.
 *              For a theorem, the statement only: the kernel checks proofs.
 *   deepHash : the own hashes of the declaration's whole dependency closure.
 */
import { createHash } from 'node:crypto';

const MODIFIER = String.raw`(?:@\[[^\]]*\]\s*|(?:private|protected|public|noncomputable|unsafe|partial|nonrec)\s+)*`;
const DECL_RE = new RegExp('^(' + MODIFIER + String.raw`)(class\s+inductive|def|abbrev|theorem|lemma|instance|structure|class|inductive|axiom|opaque|example)(?![\p{L}\p{N}_'.])`, 'u');
const SECTION_RE = /^(?:(?:noncomputable|public)\s+)*section\b[ \t]*([^\s]*)/u;
const CMD_RE = /^(?:local\s+|scoped\s+)?(variable|open|universe|namespace|end|attribute|set_option|omit|include|notation\d*|infixl|infixr|infix|prefix|postfix|macro_rules|macro|syntax|export|mutual|import|initialize|deriving|#\w+)(?![\p{L}\p{N}_'.])/u;
const TOKEN_RE = /[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*/gu;
const IN_SCOPE = new Set(['variable', 'open', 'universe', 'attribute', 'set_option', 'omit', 'include',
  'notation', 'infixl', 'infixr', 'infix', 'prefix', 'postfix', 'macro_rules', 'macro', 'syntax', 'export']);

export const DEF_KINDS = new Set(['def', 'abbrev', 'structure', 'class', 'class inductive', 'inductive', 'axiom', 'opaque', 'instance']);
const THEOREM_KINDS = new Set(['theorem', 'lemma']);

const sha = s => createHash('sha256').update(s).digest('hex').slice(0, 16);
const normalize = s => s.replace(/\s+/g, ' ').trim();

/* Blank out comments, keeping every offset and newline. Strings are skipped so
 * that `--` inside a literal is not a comment. */
export function maskComments(src) {
  const out = src.split('');
  const comments = [];
  const blank = (a, b) => { for (let i = a; i < b; i++) if (out[i] !== '\n') out[i] = ' '; };
  let i = 0;
  while (i < src.length) {
    if (src[i] === '"') {
      i++;
      while (i < src.length && src[i] !== '"') i += src[i] === '\\' ? 2 : 1;
      i++;
    } else if (src.startsWith('--', i)) {
      const nl = src.indexOf('\n', i);
      const end = nl < 0 ? src.length : nl;
      blank(i, end);
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
      if (depth) throw new Error('unterminated block comment at offset ' + start);
      comments.push({ start, end: i, kind, text: src.slice(start, i) });
      blank(start, i);
    } else i++;
  }
  return { masked: out.join(''), comments };
}

const OPEN = new Set(['(', '[', '{', '⟨', '⦃', '⟦']);
const CLOSE = new Set([')', ']', '}', '⟩', '⦄', '⟧']);

/* Offset where the signature stops: the first depth-zero `:=`, `where`, or
 * pattern-match bar. */
export function headerEnd(text) {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (OPEN.has(c)) depth++;
    else if (CLOSE.has(c)) depth--;
    else if (!depth) {
      if (text.startsWith(':=', i)) return i;
      if (c === '|' && /\n\s*$/.test(text.slice(0, i))) return i;
      if (text.startsWith('where', i) && /\s/.test(text[i - 1] || ' ') && !/[\p{L}\p{N}_']/u.test(text[i + 5] || ' ')) return i;
    }
  }
  return text.length;
}

function lineOf(src, offset) {
  let n = 1;
  for (let i = 0; i < offset; i++) if (src[i] === '\n') n++;
  return n;
}

function declName(afterKind, kind) {
  const m = afterKind.match(/^\s*(?:\(priority[^)]*\)\s*)?([^\s:({[⦃]+)?/u);
  const name = m && m[1];
  if (!name || name === 'where') return null;
  if (kind === 'instance' && name === ':') return null;
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

/* Every declaration in one file, with its namespace and active scope. */
export function parseFile(file, src) {
  const { masked, comments } = maskComments(src);
  const starts = [];
  for (let i = 0; i < masked.length;) {
    const nl = masked.indexOf('\n', i);
    const end = nl < 0 ? masked.length : nl;
    if (i < end && !/\s/.test(masked[i])) {
      const rest = masked.slice(i);
      const d = rest.match(DECL_RE);
      const s = rest.match(SECTION_RE);
      const c = rest.match(CMD_RE);
      if (d) starts.push({ at: i, type: 'decl', kind: d[2].replace(/\s+/, ' '), head: d[0].length });
      else if (s) starts.push({ at: i, type: 'section', name: s[1] });
      else if (c) starts.push({ at: i, type: c[1] });
    }
    i = end + 1;
  }

  const decls = [], imports = [], warnings = [];
  const frames = [{ type: 'file', name: '', scope: [] }];
  let prefixText = '', prefixRaw = '', prefixStart = null, anon = 0;

  starts.forEach((cmd, idx) => {
    const end = idx + 1 < starts.length ? starts[idx + 1].at : masked.length;
    const maskedText = masked.slice(cmd.at, end);
    const rawText = src.slice(cmd.at, end);
    const text = normalize(maskedText);

    if (cmd.type === 'import') { imports.push(...text.split(/\s+/).slice(1)); return; }
    if (cmd.type === 'mutual') { warnings.push(file + ': mutual block is not split into declarations'); return; }
    if (cmd.type === 'namespace') { frames.push({ type: 'namespace', name: text.split(/\s+/)[1], scope: [] }); return; }
    if (cmd.type === 'section') { frames.push({ type: 'section', name: cmd.name, scope: [] }); return; }
    if (cmd.type === 'end') { if (frames.length > 1) frames.pop(); return; }

    if (cmd.type !== 'decl') {
      // `open X in` and `set_option x y in` modify only the next command.
      if (/\sin$/.test(text)) {
        prefixText += text + ' ';
        prefixRaw += rawText.replace(/\s+$/, '') + '\n';
        if (prefixStart === null) prefixStart = cmd.at;
      } else if (IN_SCOPE.has(cmd.type)) frames[frames.length - 1].scope.push(text);
      return;
    }

    const usedPrefix = prefixText, usedRaw = prefixRaw, firstAt = prefixStart ?? cmd.at;
    prefixText = ''; prefixRaw = ''; prefixStart = null;
    if (cmd.kind === 'example') return;

    const after = maskedText.slice(cmd.head);
    const short = declName(after, cmd.kind);
    const ns = frames.filter(f => f.type === 'namespace').map(f => f.name).join('.');
    const name = short
      ? (short.startsWith('_root_.') ? short.slice(7) : (ns ? ns + '.' + short : short))
      : 'instance#' + file + '#' + (++anon);
    const scope = frames.flatMap(f => f.scope);
    const opens = scope.filter(s => /^(?:local\s+|scoped\s+)?open\b/.test(s)).flatMap(s => s.replace(/^.*?open\s+/, '').split(/\s+/));
    const headerAt = headerEnd(maskedText);
    const isThm = THEOREM_KINDS.has(cmd.kind);
    const formal = isThm ? maskedText.slice(0, headerAt) : maskedText;
    // Stop at the last real token, so the next declaration's docstring stays out.
    const shownLen = (isThm ? maskedText.slice(0, headerAt) : maskedText).replace(/\s+$/, '').length;
    const trimmedRaw = rawText.slice(0, shownLen);

    decls.push({
      name, kind: cmd.kind, file,
      line: lineOf(src, firstAt),
      endLine: lineOf(src, cmd.at + trimmedRaw.length),
      doc: docBefore(src, comments, firstAt),
      code: usedRaw + trimmedRaw,
      scope, namespaces: ns ? ns.split('.') : [], opens,
      formal: normalize(usedPrefix + formal),
      header: normalize(maskedText.slice(cmd.head, headerAt)),
      hasSorry: /\bsorry\b/.test(maskedText),
    });
  });
  return { decls, imports, warnings, sorries: (masked.match(/\bsorry\b/g) || []).length };
}

function tokens(text) {
  const out = new Set();
  for (const m of text.matchAll(TOKEN_RE)) {
    if (text[m.index - 1] === '.') continue;  // `.foo` and `(x).foo` are fields of something else
    out.add(m[0]);
  }
  return out;
}

function resolver(names) {
  const byLast = new Map();
  for (const n of names) {
    if (!n.includes('.')) continue;
    const last = n.split('.').pop();
    if (!byLast.has(last)) byLast.set(last, []);
    byLast.get(last).push(n);
  }
  return (tok, d) => {
    const prefixes = [];
    for (let i = d.namespaces.length; i >= 0; i--) prefixes.push(d.namespaces.slice(0, i).join('.'));
    prefixes.push(...d.opens);
    for (const p of prefixes) {
      const full = p ? p + '.' + tok : tok;
      if (names.has(full)) return [full];
    }
    if (!tok.includes('.')) return [];
    const head = tok.split('.')[0];
    if (names.has(head)) return [head];
    // `s.at` is field notation: without types, take every `X.at`.
    return byLast.get(tok.split('.').pop()) || [];
  };
}

/* Import order, so sorting by (file, line) is a dependency order: Lean requires
 * declare-before-use. */
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

/* Link declarations across files and compute hashes. `sources` maps relative
 * path to file contents. */
export function buildIndex(sources) {
  const files = {};
  for (const [f, src] of Object.entries(sources)) files[f] = parseFile(f, src);
  const order = fileOrder(files);
  const all = Object.values(files).flatMap(f => f.decls)
    .sort((a, b) => order.get(a.file) - order.get(b.file) || a.line - b.line);

  const defLike = new Set(all.filter(d => DEF_KINDS.has(d.kind)).map(d => d.name));
  const resolve = resolver(defLike);
  const depsIn = (text, d) => {
    const out = new Set();
    for (const t of tokens(text)) for (const n of resolve(t, d)) if (n !== d.name) out.add(n);
    return out;
  };
  const byName = new Map(all.map(d => [d.name, d]));
  for (const d of all) {
    d.deps = [...depsIn(d.formal, d)].sort();
    d.ownHash = sha([d.kind, d.name, d.formal, d.scope.join('\n')].join('\0'));
  }
  // An instance about X can change what code using X means without being named,
  // so it joins any closure containing X.
  const instances = all.filter(d => d.kind === 'instance').map(d => ({ name: d.name, about: depsIn(d.header, d) }));

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

  return {
    decls: all, byName,
    warnings: Object.values(files).flatMap(f => f.warnings),
    sorries: Object.fromEntries(Object.entries(files).filter(([, f]) => f.sorries).map(([k, f]) => [k, f.sorries])),
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
    axioms: index.decls.filter(d => d.kind === 'axiom').map(d => d.name),
    warnings: index.warnings,
  };
}
