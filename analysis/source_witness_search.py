#!/usr/bin/env python3
"""Test terminal obligations and a candidate rank for affine transfer.

Exact rational intertwining only; finite success is not a coverage theorem.
"""
import argparse
from fractions import Fraction
import json


def trajectory(n, depth):
    # T^t(n) = (3^j*n+d)/2^t on the realized parity cylinder.
    rows = [(n, 0, 0)]
    j = d = 0
    for t in range(depth):
        if n % 2:
            n, j, d = (3*n+1)//2, j+1, 3*d+2**t
        else:
            n //= 2
        rows.append((n,j,d))
    return rows


def transition(u, s, t, source, target):
    x, j, d = source[s]
    y, k, e = target[t]
    # Original y0=9*x0+2. Eliminate x0 from the two exact orbit formulas.
    a = Fraction(3**(k+2)*2**s, 3**j*2**t)
    b = Fraction(2*3**k+e, 2**t)-a*Fraction(d, 2**s)
    assert a*x+b == y
    rank = (abs(s-t)+abs(k+2-j), abs(y-x))
    return dict(source_steps=s, target_steps=t, source=x, target=y,
                slope=str(a), offset=str(b), rank=rank)


def inspect_seed(u, depth=12):
    source = trajectory(3*u+2, depth)
    target = trajectory(27*u+20, depth)
    initial_rank = (2, 24*u+18)
    successes = []
    for s in range(depth+1):
        for t in range(depth+1):
            if s+t == 0:
                continue
            row = transition(u,s,t,source,target)
            terminal = row['source']==row['target'] or row['target']==1
            if terminal or row['rank'] < initial_rank:
                row['kind'] = 'terminal' if terminal else 'rank_decrease'
                successes.append(row)
    if successes:
        best = min(successes, key=lambda r: (r['kind']!='terminal',
                                            r['source_steps']+r['target_steps']))
        return dict(parameter=u, status='candidate', transition=best)
    return dict(parameter=u, status='no_transition', depth=depth,
                source=source, target=target)


def power_two_terminal(m):
    """First source hit: x0=2^(2m+1), y0=9*x0+2; admissible x0=2 mod 3."""
    t = 2*m+1
    x0 = 2**t
    y0 = 9*x0+2
    source = trajectory(x0,t)
    target = trajectory(y0,t)
    assert x0 % 3 == 2
    assert source[-1][0] == 1 and all(x>1 for x,_,_ in source[:-1])
    assert target[-1][0] == 3**(m+2)+1
    row = transition((x0-2)//3,t,t,source,target)
    assert row['slope']==str(3**(m+2)) and row['offset']=='1'
    return dict(m=m, source_steps=t, terminal_target=target[-1][0],
                slope=row['slope'], offset=row['offset'])


def report(limit=4096, depth=12, terminal_examples=201):
    candidates = 0
    failure = None
    for u in range(limit):
        result = inspect_seed(u,depth)
        if result['status']=='no_transition':
            failure = result
            break
        candidates += 1
    return dict(scope='bounded rank test and exact terminal-family examples; no global proof',
                limit=limit, depth=depth, candidate_prefix=candidates,
                first_failure=failure,
                terminal_family=[power_two_terminal(m) for m in range(terminal_examples)])




def follow_rank(u, depth=12, macro_cap=200):
    """Follow the candidate rank into successor states, retaining failures.

    Choosing one best descent path is not complete: a failure rejects this
    greedy strategy, not every path admitted by this rank.
    """
    x, y, a, b, i, j = 3*u+2, 27*u+20, Fraction(9), Fraction(2), 0, 2
    history = []
    for macro in range(macro_cap):
        source, target = trajectory(x,depth), trajectory(y,depth)
        rank = (abs(i)+abs(j),abs(y-x))
        options = []
        for s,(xx,jj,dd) in enumerate(source):
            for t,(yy,kk,ee) in enumerate(target):
                if s+t==0:
                    continue
                ii, jnew = i+s-t, j+kk-jj
                anew = a*Fraction(3**kk*2**s,3**jj*2**t)
                bnew = Fraction(3**kk*b+ee,2**t)-anew*Fraction(dd,2**s)
                assert anew*xx+bnew==yy
                newrank = (abs(ii)+abs(jnew),abs(yy-xx))
                terminal = xx==yy or yy==1
                if terminal or newrank<rank:
                    options.append((not terminal,newrank,s+t,s,t,xx,yy,anew,bnew,ii,jnew))
        if not options:
            return dict(parameter=u,status='greedy_dead_end',macro=macro,
                        source=x,target=y,slope=str(a),offset=str(b),rank=rank,
                        history=history)
        terminal_not,nr,_,s,t,xx,yy,anew,bnew,ii,jnew=min(options)
        history.append(dict(source_steps=s,target_steps=t,source=xx,target=yy,
                            slope=str(anew),offset=str(bnew),rank=nr))
        if not terminal_not:
            return dict(parameter=u,status='terminal',macros=macro+1)
        x,y,a,b,i,j=xx,yy,anew,bnew,ii,jnew
    return dict(parameter=u,status='macro_cap',history=history)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=4096)
    parser.add_argument('--depth', type=int, default=12)
    args = parser.parse_args()
    result = report(args.limit, args.depth)
    for u in range(args.limit):
        successor = follow_rank(u,args.depth)
        if successor['status'] != 'terminal':
            result['successor_probe'] = successor
            break
    print(json.dumps(result,indent=2))
