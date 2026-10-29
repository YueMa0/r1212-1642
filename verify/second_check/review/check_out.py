import sys, json, collections
import numpy as np
A = np.load(sys.argv[1]); n = A.shape[0]
raw = open(sys.argv[2], 'rb').read()
print("ends with newline:", raw.endswith(b'\n'), " CR present:", b'\r' in raw)
lines = raw.decode().split('\n')
assert lines[-1] == ''
lines = lines[:-1]
print("lines:", len(lines))
recs = []
keysets = collections.Counter()
for i, l in enumerate(lines):
    r = json.loads(l)      # raises on any truncated / malformed line
    keysets[tuple(r.keys())] += 1
    recs.append(r)
print("key sets:", dict(keysets))
print("results:", collections.Counter(r['result'] for r in recs))
pairs = collections.Counter((r['v'], r['c']) for r in recs)
expected = {(v, c) for v in range(n) for c in (0, 1)}
print("distinct (v,c):", len(pairs), " duplicates:", sum(1 for k, x in pairs.items() if x > 1),
      " missing:", len(expected - set(pairs)), " extra:", len(set(pairs) - expected))
# independent |P(v,c)|
bad_m = 0
for r in recs:
    v, c = r['v'], r['c']
    m = int(np.count_nonzero(A[v, v+1:] == c))
    if m != r['m']: bad_m += 1
print("m mismatches vs graph:", bad_m, " max m:", max(r['m'] for r in recs))
# nodes >= 1 iff m >= 11
print("m>=11 with nodes<1:", sum(1 for r in recs if r['m'] >= 11 and r['nodes'] < 1),
      " m<11 with nodes!=0:", sum(1 for r in recs if r['m'] < 11 and r['nodes'] != 0),
      " count m<11:", sum(1 for r in recs if r['m'] < 11))
print("total nodes %.4g  total sec %.1f" % (sum(r['nodes'] for r in recs), sum(r['sec'] for r in recs)))
# queue order consistency: sorted by (m desc, v asc, c asc)
order = sorted(recs, key=lambda r: (-r['m'], r['v'], r['c']))
qpos = {(r['v'], r['c']): q for q, r in enumerate(order)}
viol = [(i, qpos[(r['v'], r['c'])]) for i, r in enumerate(recs) if qpos[(r['v'], r['c'])] > i + 7]
print("lines whose queue position > line index + 7 (would indicate resumed/merged runs):", len(viol), viol[:5])
# a few of the most expensive tasks
top = sorted(recs, key=lambda r: -r['nodes'])[:6]
for r in top: print("  top:", r)
cheap = sorted([r for r in recs if r['m'] >= 11], key=lambda r: r['nodes'])
print("cheapest searched tasks:", [(r['v'], r['c'], r['m'], r['nodes']) for r in cheap[:5]])
