#!/usr/bin/env node
/* Check an exported ledger against the current review-data.js.
 *
 *   node scripts/check-reviews.mjs dojo-reviews.json [--data other-review-data.js]
 *
 * Exits 0 only if every declaration behind every target has a current approval.
 * That covers meaning only: run `lake build` for the proofs.
 */
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { describeStale, indexDecls, latestEvents, parseLedger, summarize } from '../review-core.js';

const argv = process.argv.slice(2);
const dataAt = argv.indexOf('--data');
const dataPath = dataAt >= 0 ? argv.splice(dataAt, 2)[1] : new URL('../review-data.js', import.meta.url).pathname;
if (argv.length !== 1) { console.error('usage: check-reviews.mjs <ledger.json> [--data review-data.js]'); process.exit(2); }

const { REVIEW } = await import(pathToFileURL(resolve(dataPath)).href);
const { events, skipped } = parseLedger(readFileSync(argv[0], 'utf8'));
if (skipped) console.log(skipped + ' malformed event(s) ignored');

let ok = true;
for (const target of REVIEW.targets) {
  const { base, counts, trusted } = summarize(target, events, REVIEW);
  console.log(target + ': ' + counts.approved + '/' + counts.total + ' approved @ ' + REVIEW.rev.slice(0, 7));
  for (const { decl, status } of base) {
    if (status.state === 'approved') continue;
    console.log('  ' + status.state.padEnd(11) + decl.name + '  ' + decl.file + ':' + decl.line);
    if (status.event?.note) console.log('             note: ' + status.event.note);
    if (status.stale) describeStale(status.stale).forEach(s => console.log('             ' + s));
  }
  ok = ok && trusted;
}
const known = indexDecls(REVIEW);
for (const name of latestEvents(events, REVIEW.repo).keys()) {
  if (!known.has(name)) console.log('verdict for a declaration that no longer exists: ' + name);
}
if (Object.keys(REVIEW.sorries).length) console.log('sorry in source: ' + JSON.stringify(REVIEW.sorries));
console.log(ok ? 'All approved and current. Proofs are separate: run lake build.' : 'Not fully reviewed.');
process.exit(ok ? 0 : 1);
