"""
audit_frontier_15_leaves.py
Exhaustive, zero-truncation mathematical audit of ALL 15 branches of the
Laczkovich / Beeson / Bonfioli classification of congruent triangle dissections
for N = 280 (and other small frontier open N <= 650).

Includes exact squarefree-part handling for S2, S3, F1, Iso120, F2, F3, F4,
E120, E60 (via Theorem A), G (via Theorem D'), S1 (T_M), S4 (W_M), S5 (theta_t).
"""
import math

def is_sq(n):
    if n < 0: return False
    r = math.isqrt(n)
    return r * r == n

def factorize(n):
    res = {}
    d = 2
    x = n
    while d * d <= x:
        while x % d == 0:
            res[d] = res.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        res[x] = res.get(x, 0) + 1
    return res

def squarefree_part(n):
    sf = 1
    for p, e in factorize(n).items():
        if e % 2 == 1:
            sf *= p
    return sf

def has_word(L, a, b, c, z_min=0):
    for z in range(z_min, L // c + 1):
        rem = L - z * c
        for y in range(0, rem // b + 1):
            if (rem - y * b) % a == 0:
                return True
    return False

def verify_15_leaves(N):
    pf = factorize(N)
    sf = squarefree_part(N)
    print(f"\n======================================================================")
    print(f"EXHAUSTIVE 15-LEAF AUDIT FOR N = {N} = {' * '.join(f'{p}^{e}' if e>1 else str(p) for p,e in sorted(pf.items()))} (sf={sf})")
    print(f"======================================================================")
    surviving = []

    # 1. NSq: N = x^2 + y^2
    odd_3mod4 = [p for p, e in pf.items() if p % 4 == 3 and e % 2 == 1]
    if odd_3mod4:
        print(f"  [1] NSq (N = x^2+y^2):            CLOSED (prime {odd_3mod4[0]} == 3 mod 4 has odd exponent)")
    else:
        print(f"  [1] NSq:                          TILED (sum of 2 squares!)")
        surviving.append("NSq")

    # 2. R: N = 2(x^2 + y^2)
    if N % 2 == 1:
        print(f"  [2] R   (N = 2(x^2+y^2)):         CLOSED (N is odd)")
    else:
        pf2 = factorize(N // 2)
        odd3 = [p for p, e in pf2.items() if p % 4 == 3 and e % 2 == 1]
        if odd3:
            print(f"  [2] R   (N = 2(x^2+y^2)):         CLOSED (N/2={N//2} has prime {odd3[0]} == 3 mod 4 to odd exponent)")
        else:
            print(f"  [2] R:                            TILED!")
            surviving.append("R")

    # 3. HAr: 2, 3, 6, 10 * r^2
    if sf in (1, 2, 3, 6, 10):
        print(f"  [3] HAr:                          TILED (sf={sf})")
        surviving.append("HAr")
    else:
        print(f"  [3] HAr (2,3,6,10 * r^2):         CLOSED (sf={sf} not in {{1,2,3,6,10}})")

    # 4-5. A & B: commensurable / right-angled
    odd_ge7 = [p for p, e in pf.items() if p >= 7 and e % 2 == 1]
    if odd_ge7:
        print(f"  [4-5] A, B (commensurable/right): CLOSED (prime {odd_ge7[0]} >= 7 has odd exponent)")
    else:
        print(f"  [4-5] A, B:                       CHECK (no odd prime >= 7)")
        surviving.append("A/B")

    sq_divs = [M for M in range(1, math.isqrt(N) + 1) if N % (M * M) == 0]

    # 6. E (Eq120 & Eq60) via Theorem A (ab | X => N = m^2 * ab)
    e_hits = []
    for M in sq_divs:
        ab = N // (M * M)
        for a in range(1, math.isqrt(ab) + 1):
            if ab % a != 0: continue
            b = ab // a
            if a == b or math.gcd(a, b) != 1: continue
            if is_sq(a*a + a*b + b*b):
                c = math.isqrt(a*a + a*b + b*b)
                X = M * ab
                p1, p2 = c + a - b, c + b - a
                if (3*X) % p1 == 0 and (3*X) % p2 == 0 and (3*X//p1)%2 == N%2 and (3*X//p2)%2 == N%2:
                    e_hits.append(f"Eq120({a},{b},{c},m={M},X={X})")
                else:
                    print(f"      (Eq120({a},{b},{c},m={M}) EXCLUDED by Prop 5.1)")
            if is_sq(a*a - a*b + b*b):
                c = math.isqrt(a*a - a*b + b*b)
                X = M * ab
                p1, p2 = a + b - c, a + b + c
                if (3*X) % p1 == 0 and (3*X) % p2 == 0 and (3*X//p1)%2 == N%2 and (3*X//p2)%2 == N%2:
                    e_hits.append(f"Eq60({a},{b},{c},m={M},X={X})")
                else:
                    print(f"      (Eq60({a},{b},{c},m={M}) EXCLUDED by Prop 5.1)")
    print(f"  [6] E   (Eq120 & Eq60, via ThmA): {'CLOSED' if not e_hits else 'OPEN -> ' + str(e_hits)}")
    surviving.extend(e_hits)

    # 7-9. F1, Iso120, R8 (F2, F3, F4) — zero truncation!
    # Also check both orientations for F1, Iso120 (a,b) and (b,a) since we loop over all a != b!
    f1_open, iso_open, r8_open = [], [], []
    divs_N = [d for d in range(2, N + 1) if N % d == 0]
    for d in divs_N:
        # F1: N = lam^2 * (a+b)/b => (a+b) | N, (N/d)*b = lam^2
        for a in range(1, d):
            b = d - a
            if a == b or math.gcd(a, b) != 1: continue
            if is_sq(a*a + a*b + b*b):
                c = math.isqrt(a*a + a*b + b*b)
                if is_sq((N // d) * b):
                    lam = math.isqrt((N // d) * b)
                    # Check signed-direction functional on F1:
                    # F1 sides: (lam*a, lam*c, lam*(a+b)) scaled so area = N * area(tile)
                    # Wait: area of F1 with sides (s*a, s*c, s*(a+b))? No, angle pi/3 is between a and a+b:
                    # Area = 1/2 * (lam*a) * (lam*(a+b)) * sin(pi/3) = lam^2 * a(a+b)/ (ab) * Area(tile) = lam^2*(a+b)/b!
                    # Signed direction weights: check s1, s2!
                    # For F1: angles (alpha, pi/3, alpha+2beta), sides opp (alpha, pi/3, alpha+2beta) = (lam*a, lam*c, lam*(a+b))
                    # Actually check both parity & divisibility:
                    # Wait: Theorem A / Bonfioli Prop: does b | lam always hold? Let's report exact lam, b!
                    f1_open.append(f"F1({a},{b},{c},lam={lam},b|lam={lam%b==0})")
        # Iso120: N = lam^2 * (a+2b)/b => (a+2b) | N
        for b in range(1, d // 2 + 1):
            a = d - 2 * b
            if a <= 0 or a == b or math.gcd(a, b) != 1: continue
            if is_sq(a*a + a*b + b*b):
                c = math.isqrt(a*a + a*b + b*b)
                if is_sq((N // d) * b):
                    lam = math.isqrt((N // d) * b)
                    p1, p2 = c + a - b, c + b - a
                    r1, r2 = lam * (2*c - a - 2*b), lam * (a + 2*b + 2*c)
                    if r1 % p1 == 0 and r2 % p2 == 0 and (r1//p1)%2 == N%2 and (r2//p2)%2 == N%2:
                        iso_open.append(f"Iso120({a},{b},{c},lam={lam})")
                    else:
                        print(f"      (Iso120({a},{b},{c},lam={lam}) EXCLUDED by signed-direction parity)")
    for a in range(1, N):
        for b in range(1, N):
            if (a + b) * (2*a + b) > N and (a + 2*b) * (2*a + b) > N:
                break
            if a == b or math.gcd(a, b) != 1: continue
            if not is_sq(a*a + a*b + b*b): continue
            c = math.isqrt(a*a + a*b + b*b)
            if a < b and N % ((a+2*b)*(2*a+b)) == 0 and is_sq(N // ((a+2*b)*(2*a+b))):
                r8_open.append(f"F2({a},{b},{c},k={math.isqrt(N//((a+2*b)*(2*a+b)))})")
            if N % (3*(a+2*b)*(a+b)) == 0 and is_sq(N // (3*(a+2*b)*(a+b))):
                r8_open.append(f"F3({a},{b},{c},k={math.isqrt(N//(3*(a+2*b)*(a+b)))})")
            if N % ((2*a+b)*(a+b)) == 0 and is_sq(N // ((2*a+b)*(a+b))):
                r8_open.append(f"F4({a},{b},{c},k={math.isqrt(N//((2*a+b)*(a+b)))})")
    print(f"  [7] F1  (2pi/3 F1):               {'CLOSED' if not f1_open else 'OPEN -> ' + str(f1_open)}")
    print(f"  [8] Iso (2pi/3 Iso120):           {'CLOSED' if not iso_open else 'OPEN -> ' + str(iso_open)}")
    print(f"  [9] R8  (2pi/3 F2/F3/F4):         {'CLOSED' if not r8_open else 'OPEN -> ' + str(r8_open)}")
    surviving.extend(f1_open + iso_open + r8_open)

    # 10-11. Leaves S2 & S3 (EXHAUSTIVE, including non-squarefree b = f^2-e^2!)
    # S2: angles (2alpha, alpha, 2beta). Sides prop to (2cos(alpha)*ef, ef, 2cos(beta)*b) -> let's check!
    # Wait: sin(2a) : sin(a) : sin(2b) = (2f^2-e^2)e : ef^2 : ...
    # Actually Area ratio for S2 is N = s^2 * (2f^2-e^2)*(3f^2-e^2) / ?
    # Wait: sin(2a) = sin(a)*(2f^2-e^2)/f^2, sin(2b) = sin(3a) = sin(a)*(3f^2-e^2)/f^2? Wait:
    # sin(3a)/sin(a) = 3 - 4sin^2(a) = 2cos(2a)+1. Since 2cos(a) = (2f^2-e^2)/f^2,
    # cos(2a) = 2cos^2(a)-1, wait: Area(S2)/Area(tau) = L^2 * sin(2a)*sin(a)/(sin(2b) * ef * f^2 * sin(beta)?)
    # Better: S2 has N * k^2 = (2f^2-e^2)(3f^2-e^2) * m^2 => sf(N) == sf((2f^2-e^2)(3f^2-e^2))!
    # Even simpler: check BOTH exact area formulas!
    # For S2: sides of (2a, a, 2b) are proportional to (e(2f^2-e^2), e*f^2, e*(3f^2-e^2))? Wait:
    # sin(2a)/sin(a) = (2f^2-e^2)/f^2.
    # sin(2b) = sin(pi - 3a) = sin(3a), and sin(3a)/sin(a) = (2f^2-e^2)^2/f^4 - 1 = (3f^4 - 4e^2 f^2 + e^4)/f^4 = (f^2-e^2)(3f^2-e^2)/f^4!
    # OH! So Area(S2) = 1/2 * (s*f^2) * (s*(2f^2-e^2)) * sin(3a)
    #                 = 1/2 * s^2 * (2f^2-e^2) * (f^2-e^2)(3f^2-e^2) / f^2 * sin(a)
    # Wait: Area(tau) = 1/2 * (f^2-e^2) * f^2 * sin(a)!
    # Divide: Area(S2) / Area(tau) = s^2 * (2f^2-e^2)*(3f^2-e^2) / f^4!
    # Since gcd(f, 2f^2-e^2) = gcd(f, 3f^2-e^2) = 1, f^2 | s, so N = M^2 * (2f^2-e^2)*(3f^2-e^2) ALWAYS!
    # And for S3: sides of (a, a, a+2b) are (s*f^2, s*f^2, s*(2f^2-e^2)):
    # Area(S3) / Area(tau) = s^2 * (2f^2-e^2) / (f^2 - e^2)!
    # Since gcd(f^2-e^2, 2f^2-e^2) = 1, (f^2-e^2) | s^2, so N = g^2 * sf(f^2-e^2) * (2f^2-e^2) ALWAYS!
    # Note: 2f^2 - e^2 > f^2, so f < sqrt(N) is 100% EXHAUSTIVE for BOTH S2 and S3!
    s2_open, s3_open = [], []
    for f in range(2, math.isqrt(N) + 2):
        for e in range(1, f):
            if math.gcd(e, f) != 1: continue
            q2 = (2*f*f - e*e) * (3*f*f - e*e)
            if N % q2 == 0 and is_sq(N // q2):
                s2_open.append(f"S2_{math.isqrt(N//q2)}({e},{f})")
            b = f*f - e*e
            b_sf = squarefree_part(b)
            q3 = b_sf * (2*f*f - e*e)
            if N % q3 == 0 and is_sq(N // q3):
                g_eff = math.isqrt(N // q3)
                # scale s = g_eff * sqrt(b * b_sf) = g_eff * b_sf * r
                s_val = math.isqrt(N * b // (2*f*f - e*e))
                s3_open.append(f"alpha_s={s_val}({e},{f})[g={g_eff},b={b},b_sf={b_sf}]")
    print(f"  [10] S2 ((2a,a,2b)):              {'CLOSED' if not s2_open else 'OPEN -> ' + str(s2_open)}")
    print(f"  [11] S3 (alpha_g(e,f)):           {'CLOSED' if not s3_open else 'OPEN -> ' + str(s3_open)}")
    surviving.extend(s2_open + s3_open)

    # 12. Leaf G (gamma = 2*alpha): N = g^2 * (v^2 - u^2), 1 <= u < v < 2u, gcd(u,v)=1
    g_open = []
    for g in sq_divs:
        q = N // (g * g)
        for d1 in range(1, math.isqrt(q) + 1):
            if q % d1 != 0: continue
            d2 = q // d1
            if (d1 + d2) % 2 != 0 or d1 >= d2: continue
            v, u = (d1 + d2) // 2, (d2 - d1) // 2
            if 1 <= u < v < 2 * u and math.gcd(u, v) == 1:
                gD = (u - 1) // (v - u) + 1
                if g <= gD:
                    print(f"      (G({u},{v},g={g}) EXCLUDED by Theorem D': g={g} <= gD={gD})")
                else:
                    g_open.append(f"G({u},{v},g={g})")
    print(f"  [12] G  (gamma = 2*alpha):        {'CLOSED' if not g_open else 'OPEN -> ' + str(g_open)}")
    surviving.extend(g_open)

    # 13. Leaf S4 (W_M(e,f)): N = M^2 * (2f^2 - e^2)
    s4_open = []
    for M in sq_divs:
        q = N // (M * M)
        for f in range(max(2, math.isqrt(q // 2)), math.isqrt(q) + 2):
            e2 = 2 * f * f - q
            if e2 > 0 and is_sq(e2):
                e = math.isqrt(e2)
                if 1 <= e < f and math.gcd(e, f) == 1:
                    if M == 1 or M*e < f or (e == 1 and M < f) or (e >= 2 and f <= M*e and M*(f-e) < f):
                        print(f"      (W_{M}({e},{f}) EXCLUDED by M=1 / Me<f / W-gap)")
                    else:
                        s4_open.append(f"W_{M}({e},{f})")
    print(f"  [13] S4 (W_M(e,f)):               {'CLOSED' if not s4_open else 'OPEN -> ' + str(s4_open)}")
    surviving.extend(s4_open)

    # 14. Leaf S5 (theta_t(e,f)): N = t^2 * (f^2 - e^2)
    s5_open = []
    for t in sq_divs:
        q = N // (t * t)
        for d1 in range(1, math.isqrt(q) + 1):
            if q % d1 != 0: continue
            d2 = q // d1
            if (d1 + d2) % 2 != 0 or d1 >= d2: continue
            f, e = (d1 + d2) // 2, (d2 - d1) // 2
            if 1 <= e < f and math.gcd(e, f) == 1:
                a, b, c = e * f, f * f - e * e, f * f
                base = t * e * b
                if t == 1 or f > t*e or base < f**3 or not has_word(base, a, b, c, z_min=f):
                    print(f"      (theta_{t}({e},{f}) EXCLUDED by Prop theta S5wChk: teb={base} vs f^3={f**3})")
                else:
                    s5_open.append(f"theta_{t}({e},{f})")
    print(f"  [14] S5 (theta_t(e,f)):           {'CLOSED' if not s5_open else 'OPEN -> ' + str(s5_open)}")
    surviving.extend(s5_open)

    # 15. Leaf S1 (T_M(e,f)): N = M^2 * (3f^2 - e^2)
    s1_open = []
    for M in sq_divs:
        q = N // (M * M)
        for f in range(max(2, math.isqrt(q // 3)), math.isqrt(q // 2) + 2):
            e2 = 3 * f * f - q
            if e2 > 0 and is_sq(e2):
                e = math.isqrt(e2)
                if 1 <= e < f and math.gcd(e, f) == 1:
                    if M == 1 or 2*M*e < f or (e == 1 and 2*M <= f) or (e >= 2 and M >= 2 and f <= 2*M*e < f + e):
                        print(f"      (T_{M}({e},{f}) EXCLUDED by M=1 / 2Me<f / BandThm)")
                    else:
                        s1_open.append(f"T_{M}({e},{f})")
    print(f"  [15] S1 (T_M(e,f)):               {'CLOSED' if not s1_open else 'OPEN -> ' + str(s1_open)}")
    surviving.extend(s1_open)

    print(f"  >>> TOTAL SURVIVING BRANCHES FOR N={N}: {surviving}")
    return surviving

for N in [280, 284, 332, 351, 423, 444, 524, 531, 552, 594, 644]:
    verify_15_leaves(N)
