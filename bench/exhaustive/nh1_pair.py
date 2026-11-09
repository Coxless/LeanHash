# NH の 1 組: f(k1,k2) = ((m1+k1)%W) * ((m2+k2)%W) mod W^2
# 差 D = f(m) - f(m') ≡ c となる (k1,k2) の数の最大値と、k1 固定時の k2 解の数の最大値
import sys, itertools
from collections import Counter
for w in range(1, int(sys.argv[1])+1):
    W=1<<w; W2=W*W
    worst=0; per_k1_both=0; per_k1_single=0
    for m1,m2,n1,n2 in itertools.product(range(W),repeat=4):
        if (m1,m2)==(n1,n2): continue
        cnt=Counter(); 
        for k1 in range(W):
            a=(m1+k1)%W; b=(n1+k1)%W
            row=Counter((a*((m2+k2)%W) - b*((n2+k2)%W))%W2 for k2 in range(W))
            cnt.update(row)
            mx=max(row.values())
            if m1!=n1 and m2!=n2: per_k1_both=max(per_k1_both,mx)
            if m1!=n1 and m2==n2: per_k1_single=max(per_k1_single,mx)
        worst=max(worst,max(cnt.values()))
    print(f"w={w}: max collisions={worst} (W={W}), per-k1 max: both differ={per_k1_both}, only m1 differs={per_k1_single}")
