"""P2 残りの定理の全数照合（小さい幅）。

1. multiply-shift: w ビット → 上位 l ビット。x ≠ y ごとに衝突する奇数 a の数の最大値 ≤ 2^(w-l)
2. Toeplitz NH 2 本: 語 b ビット（W = 2^b）、レーン n 個、鍵レーン n+1 個。
   最後に違うレーンが両方にあるメッセージ対で、2 本とも衝突する鍵の数の最大値 ≤ W^(2(n+1)) / W^2
   （レーンの有無つき：None は和に何も足さない）

使い方: python3 -I bench/exhaustive/p2_rest_check.py
"""
import itertools


def ms_check(w, l):
    M = 1 << w
    best = 0
    for x in range(M):
        for y in range(x + 1, M):
            c = sum(1 for a in range(1, M, 2)
                    if ((a * x) % M) >> (w - l) == ((a * y) % M) >> (w - l))
            best = max(best, c)
    return best


def toeplitz_check(b, n):
    W = 1 << b
    lanes = [None] + [(p, q) for p in range(W) for q in range(W)]
    keys = list(itertools.product(range(W), repeat=2))
    allK = list(itertools.product(keys, repeat=n + 1))

    def nh(K, M, off):
        s = 0
        for i, m in enumerate(M):
            if m is not None:
                k = K[i + off]
                s += ((m[0] + k[0]) % W) * ((m[1] + k[1]) % W)
        return s % (W * W)

    best = 0
    msgs = list(itertools.product(lanes, repeat=n))
    for a, M in enumerate(msgs):
        for M2 in msgs[a + 1:]:
            diff = [i for i in range(n) if M[i] != M2[i]]
            j = max(diff)
            if M[j] is None or M2[j] is None:
                continue  # 定理の仮定（最後に違う位置が両方にある）を満たさない
            c = sum(1 for K in allK
                    if nh(K, M, 0) == nh(K, M2, 0) and nh(K, M, 1) == nh(K, M2, 1))
            best = max(best, c)
    return best, W ** (2 * (n + 1)) // (W * W)


if __name__ == "__main__":
    for w, l in [(4, 1), (4, 2), (4, 3), (6, 2), (6, 3), (8, 4)]:
        c = ms_check(w, l)
        print(f"ms w={w} l={l}: max collisions={c}, bound 2^(w-l)={1 << (w - l)}",
              "OK" if c <= 1 << (w - l) else "NG")
    for b, n in [(1, 1), (1, 2), (2, 1), (1, 3)]:
        c, bound = toeplitz_check(b, n)
        print(f"toeplitz b={b} n={n}: max collisions={c}, bound={bound}",
              "OK" if c <= bound else "NG")
