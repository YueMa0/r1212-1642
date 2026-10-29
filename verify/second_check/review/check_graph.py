import sys, hashlib
import numpy as np
p = sys.argv[1]
raw = open(p, 'rb').read()
print("bytes", len(raw), "sha256", hashlib.sha256(raw).hexdigest())
print("distinct byte values:", sorted(set(raw)))
print("has CR:", b'\r' in raw, " ends with LF:", raw.endswith(b'\n'), " starts with BOM:", raw.startswith(b'\xef\xbb\xbf'))
lines = raw.split(b'\n')
if lines[-1] == b'': lines = lines[:-1]
print("lines", len(lines), "lengths", sorted(set(len(l) for l in lines)))
n = len(lines)
A = np.array([[c - 48 for c in l] for l in lines], dtype=np.int8)
print("shape", A.shape, "values", np.unique(A))
print("diag nonzero:", int(np.count_nonzero(np.diag(A))), " symmetric:", bool((A == A.T).all()))
deg_red = A.sum(1)
print("red degree range", deg_red.min(), deg_red.max(), " blue degree range", (n-1-deg_red).min(), (n-1-deg_red).max())
np.save(sys.argv[2], A)
