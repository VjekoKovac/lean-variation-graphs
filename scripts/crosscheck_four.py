"""Independent regression check of the definitions on small integer inputs.

Uses integer arithmetic throughout. This finite sample supplies no proof for
arbitrary reals; the Lean certificates establish that quantifier.
"""
from itertools import combinations, product

vertices = range(4)
pairs = list(combinations(vertices, 2))
functions = list(product((-1, 0, 1, 2), repeat=4))
graph_count = 0
for mask in range(64):
    edges = [(u, v) for k, (u, v) in enumerate(pairs) if mask >> k & 1]
    distance = [[0 if u == v else 1 if (min(u, v), max(u, v)) in edges else 10
                 for v in vertices] for u in vertices]
    for k, u, v in product(vertices, repeat=3):
        distance[u][v] = min(distance[u][v], distance[u][k] + distance[k][v])
    if max(distance[0]) > 3:
        continue
    graph_count += 1
    balls = [[[j for j in vertices if distance[i][j] <= r]
              for r in vertices] for i in vertices]
    sharp = False
    for f in functions:
        # 12 is divisible by each ball size, so these are exactly 12*M(f).
        scaled = [max((12 // len(ball)) * sum(abs(f[j]) for j in ball)
                      for ball in family) for family in balls]
        original = sum(abs(f[u] - f[v]) for u, v in edges)
        image = sum(abs(scaled[u] - scaled[v]) for u, v in edges)
        if image > 9 * original:
            raise ValueError((mask, f, image, original))
        sharp |= original > 0 and image == 9 * original
    if not sharp:
        raise ValueError(f"No nonconstant equality witness for mask {mask}")
assert graph_count == 38
print(f"{graph_count} connected labeled graphs, {len(functions)} real-valued integer inputs per graph")
print(f"{graph_count * len(functions)} exact upper-bound checks; equality witnessed on every graph")
