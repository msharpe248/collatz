"""
Geometric-ideal tracking (lean/Collatz/Ideal.lean), numerically.

For an itinerary w with c_inf(w) = sum_{w_i=1} 2^i / 3^{#ones <= i}  (real),
Ideal.lean proves for the orbit of any integer n with itinerary w:

    n_T = (n + c_inf(w)) * 3^{j_T} / 2^T  -  c_inf(shift^T w)         (*)

Experiments:
 1. exact check of tracking_finite on real orbits (fractions);
 2. c_inf of the rung-1 word w = fix(1->110, 0->011) and its tails:
    size, spread, 3-kernel clustering;
 3. the mod-1 obstruction: for candidate n, first T at which
    frac((n + c_inf(w)) 3^j/2^T) != frac(c_inf(tail_T)) — i.e. how fast
    (*) excludes each n, versus the parity-bijection bound log2 n.
"""
from fractions import Fraction
import math

def terras(n): return n//2 if n%2==0 else (3*n+1)//2

def itinerary(n, T):
    w=[]
    for _ in range(T):
        w.append(n%2); n=terras(n)
    return w

def c_partial(w):
    s=Fraction(0); ones=0
    for i,b in enumerate(w):
        if b: ones+=1; s+=Fraction(2**i, 3**ones)
    return s

def c_inf(w, tol=1e-30):
    s=0.0; ones=0
    for i,b in enumerate(w):
        if b:
            ones+=1
            term=math.exp(i*math.log(2)-ones*math.log(3))
            s+=term
            if term<tol and i>50: break
    return s

def sub_fixed(sigma, n):
    w=[1]
    while len(w)<n:
        w=[c for b in w for c in sigma[b]]
    return w[:n]

def exp1():
    print("== exp1: tracking_finite exact on real orbits ==")
    bad=0
    for n in range(1,400):
        for T in (5,17,40):
            S=30
            w=itinerary(n,T+S); j=sum(w[:T])
            nT=n
            for _ in range(T): nT=terras(nT)
            rhs=(n+c_partial(w))*Fraction(3**j,2**T)-c_partial(w[T:])
            if Fraction(nT)!=rhs: bad+=1
    print("  mismatches:",bad,"(expect 0)")

SIG={1:[1,1,0],0:[0,1,1]}
def exp2():
    print("== exp2: rung-1 word tails ==")
    w=sub_fixed(SIG,6000)
    c=c_inf(w)
    print(f"  c_inf(w) = {c:.12f}")
    tails=[c_inf(w[T:]) for T in range(0,3000)]
    print(f"  tails T<3000: min {min(tails):.6f} max {max(tails):.6f}  (uniform bound B)")
    for k in (3,9,27):
        spreads=[]
        for r in range(k):
            vals=[tails[T] for T in range(r,3000,k)]
            spreads.append(max(vals)-min(vals))
        print(f"  T mod {k}: mean spread of tail values within class = {sum(spreads)/k:.4f}")
    return w,c,tails

def exp3(w,c,tails):
    print("== exp3: mod-1 exclusion speed ==")
    res=[]
    for n in range(1,2001):
        theta=n+c
        j=0; first=None
        for T in range(0,200):
            lhs=(theta*3**j/2**T)%1.0
            rhs=tails[T]%1.0
            d=abs(lhs-rhs); d=min(d,1-d)
            if d>1e-6: first=T; break
            j+=w[T]
        wn=itinerary(n,200)
        firstdiff=next((T for T in range(200) if wn[T]!=w[T]),None)
        res.append((n,first,firstdiff))
    worst=max(res,key=lambda r:(r[1] if r[1] is not None else 999))
    print("  (n, first mod-1 failure T, first itinerary mismatch T):")
    for r in res[:6]+[worst]: print("   ",r)
    # (*) at time T uses only w_{<T}, so failure lands exactly one step
    # after the first itinerary mismatch: no information gained, none lost.
    print("  mod-1 failure == itinerary mismatch + 1 for all n:",
          all(f is not None and fd is not None and f==fd+1 for _,f,fd in res))
    print("  max first-failure T over n<=2000:",worst[1]," log2(2000)=",round(math.log2(2000),1))

if __name__=="__main__":
    exp1(); w,c,t=exp2(); exp3(w,c,t)
