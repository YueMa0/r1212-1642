"""Run maxclique and require an exact result, including a valid clique witness.

usage: python3 -I check_maxclique.py BINARY GRAPH EXPECTED_OMEGA
GRAPH has the vertex count on its first line (the maxclique.c input format).
"""
import re
import subprocess
import sys


def read_graph(path):
    with open(path, encoding="ascii") as fh:
        lines = fh.read().splitlines()
    n = int(lines[0])
    rows = lines[1:]
    if n < 1 or len(rows) != n or any(len(row) != n or set(row) - {"0", "1"} for row in rows):
        raise ValueError("invalid maxclique input dimensions or entries")
    if any(rows[i][i] != "0" or any(rows[i][j] != rows[j][i] for j in range(i)) for i in range(n)):
        raise ValueError("maxclique input is not a simple undirected graph")
    return [[int(x) for x in row] for row in rows]


def parse_result(output, adj, target=None):
    """Reject missing/ambiguous output and independently check any claimed witness."""
    lines = output.splitlines()
    result = [line for line in lines if line.startswith("omega")]
    targets = [line for line in lines if line.startswith("target")]
    nodes = [line for line in lines if re.fullmatch(r"nodes [0-9]+", line)]
    expected_lines = 3 if target is not None else 2
    if len(result) != 1 or len(nodes) != 1 or len(lines) != expected_lines:
        raise ValueError(f"incomplete or unexpected maxclique output: {output!r}")
    match = re.fullmatch(r"omega ([0-9]+) witness((?: [0-9]+)*)", result[0])
    if match:
        omega = int(match[1])
        witness = [int(v) for v in match[2].split()]
        if (not 1 <= omega <= len(adj) or len(witness) != omega or len(set(witness)) != omega
                or any(not 0 <= v < len(adj) for v in witness)
                or any(not adj[u][v] for i, u in enumerate(witness) for v in witness[i + 1:])):
            raise ValueError("invalid maxclique witness")
        exact = True
    else:
        match = re.fullmatch(r"omega <= ([0-9]+)", result[0])
        if match is None or target is None or int(match[1]) != target - 1:
            raise ValueError(f"expected an exact clique number: {result[0]!r}")
        omega, exact = int(match[1]), False
    expected_target = [] if target is None else [f"target {target}: {'FOUND' if exact else 'none'}"]
    if targets != expected_target or (target is not None and exact and omega < target):
        raise ValueError("inconsistent maxclique target result")
    return omega, exact


def run_solver(binary, path, adj, target=None):
    result = subprocess.run([binary, str(path)] + ([] if target is None else [str(target)]),
                            capture_output=True, text=True, check=True, timeout=60)
    return parse_result(result.stdout, adj, target)


def main():
    binary, path, expected = sys.argv[1:]
    expected = int(expected)
    omega, exact = run_solver(binary, path, read_graph(path))
    if not exact or omega != expected:
        raise SystemExit(f"CHECK FAILED: expected omega {expected}, got {omega}")
    print(f"RESULT: PASS: omega {omega} (witness checked)")


if __name__ == "__main__":
    main()
