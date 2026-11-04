#!/usr/bin/env node
/* Check an exported ledger against the current review-data.js.
 *
 *   node scripts/check-reviews.mjs dojo-reviews.json [--data other-review-data.js]
 *
 * Exit 0: every declaration behind every target has a current approval, and the
 * file and source raised no problem. Exit 1: not fully reviewed. Exit 2: could not
 * check at all. This covers meaning only: run `lake build` for the proofs.
 */
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { describeStale, indexDecls, latestEvents, parseLedger, summarize } from '../review-core.js';

const USAGE = 'usage: check-reviews.mjs <ledger.json> [--data review-data.js]';
function fail(msg) { console.error(msg); process.exit(2); }

const argv = process.argv.slice(2);
let dataPath = fileURLToPath(new URL('../review-data.js', import.meta.url));
const at = argv.indexOf('--data');
if (at >= 0) {
  if (!argv[at + 1]) fail(USAGE);
  dataPath = argv.splice(at, 2)[1];
}
if (argv.length !== 1) fail(USAGE);

let REVIEW, parsed;
try {
  ({ REVIEW } = await import(pathToFileURL(resolve(dataPath)).href));
  parsed = parseLedger(readFileSync(argv[0], 'utf8'));
} catch (e) {
  fail('could not read input: ' + e.message);
}
if (!REVIEW.targets.length) fail('review data names no target');

const { events, skipped, conflicts } = parsed;
let ok = true;
if (skipped) { console.log(skipped + ' malformed event(s) ignored: a dropped event could have been a flag'); ok = false; }
if (conflicts) { console.log(conflicts + ' id(s) with conflicting content ignored'); ok = false; }
if (REVIEW.unchecked) { console.log('review data was built with --unchecked'); ok = false; }

for (const target of REVIEW.targets) {
  const { base, counts, trusted } = summarize(target, events, REVIEW);
  console.log(target + ': ' + counts.approved + '/' + counts.total + ' approved @ ' + REVIEW.rev.slice(0, 7));
  for (const { decl, status } of base) {
    if (decl.hasSorry) console.log('  contains sorry  ' + decl.name);
    if (status.state === 'approved') continue;
    console.log('  ' + status.state.padEnd(11) + decl.name + '  ' + decl.file + ':' + decl.line);
    if (status.event?.note) console.log('             note: ' + status.event.note);
    if (status.stale) describeStale(status.stale).forEach(s => console.log('             ' + s));
  }
  if (counts.imported) console.log('  ' + counts.imported + ' approval(s) came from an imported file');
  ok = ok && trusted;
}
const known = indexDecls(REVIEW);
for (const [name, e] of latestEvents(events, REVIEW.repo)) {
  if (!known.has(name)) console.log('verdict for a declaration that no longer exists: ' + name + ' (' + e.verdict + (e.note ? ': ' + e.note : '') + ')');
}
const others = [...new Set(events.filter(e => e.repo !== REVIEW.repo).map(e => e.repo))];
if (others.length) console.log('verdicts for other repos ignored: ' + others.join(', '));
if (Object.keys(REVIEW.sorries).length) console.log('sorry in source: ' + JSON.stringify(REVIEW.sorries));
if (Object.keys(REVIEW.risky || {}).length) { console.log('needs attention in source: ' + JSON.stringify(REVIEW.risky)); ok = false; }
console.log(ok ? 'All approved and current. Proofs are separate: run lake build.' : 'Not fully reviewed.');
process.exit(ok ? 0 : 1);
