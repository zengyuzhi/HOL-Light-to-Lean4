# primerecip.ml

## Overview

Number of statements: 7

This file proves the divergence of the sum of reciprocals of prime numbers (∑ 1/p). It builds upon Bertrand's postulate and results about harmonic series, extending the library's number-theoretic results. The proof likely follows the classical approach of comparing the prime reciprocal series with the harmonic series, establishing that since harmonic series diverges, so must the sum of prime reciprocals.

## INDUCTION_FROM_1

### INDUCTION_FROM_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDUCTION_FROM_1 = prove
 (`!P. P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P(SUC n)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[num_CONV `1`; ARITH_RULE `n = 0 \/ 1 <= n`]);;
```

### Informal statement
For any predicate $P$ on the natural numbers, if:
1. $P(0)$ holds, and
2. $P(1)$ holds, and
3. For all $n \geq 1$, if $P(n)$ holds, then $P(n+1)$ holds

Then $P(n)$ holds for all natural numbers $n$.

### Informal proof
The proof proceeds by standard induction on $n$:

* Base case: We need to prove $P(0)$, which is directly given by our first assumption.

* Inductive step: Assume $P(n)$ holds for some $n$. We need to show $P(n+1)$ holds.
  - If $n = 0$, then $P(1)$ is directly given by our second assumption.
  - If $n \geq 1$, then by our third assumption, since $1 \leq n$ and $P(n)$ holds, we can conclude $P(n+1)$ holds.

This completes the induction, showing that $P(n)$ holds for all natural numbers $n$.

### Mathematical insight
This is a variant of the standard mathematical induction principle, structured to handle both $P(0)$ and $P(1)$ as base cases. This form is particularly useful when:

1. The proof naturally requires verifying the first two cases separately
2. The inductive step requires $n \geq 1$ to work properly

The theorem provides a clean way to express this common induction pattern without having to repeatedly handle the special case of $n=0$ in the inductive step. This pattern appears frequently in proofs about sequences where the behavior at $n=0$ or $n=1$ may be exceptional.

### Dependencies
- Standard HOL Light induction principle (`INDUCT_TAC`)
- Basic arithmetic reasoning (`ARITH_RULE`)

### Porting notes
This theorem should be straightforward to port to other systems. Most proof assistants have similar induction principles or the ability to define custom induction schemes. When porting:

1. Make sure the target system handles the base case and inductive step in the same way
2. Verify how the system treats natural number constants and inequalities
3. Consider whether the target system might already have an equivalent principle built-in

In systems like Lean or Coq, this could be implemented as a derived induction principle, while in others it might be proven as a standard theorem.

---

## SUM_CONV

### SUM_CONV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Conversion function

### Formal Content
```ocaml
let SUM_CONV =
  let pth = prove
   (`sum(1..1) f = f 1 /\ sum(1..SUC n) f = sum(1..n) f + f(SUC n)`,
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0;
             ARITH_RULE `1 <= SUC n`; SUM_SING_NUMSEG]) in
  let econv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and econv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec sconv tm =
    (econv_0 ORELSEC
     (LAND_CONV(RAND_CONV num_CONV) THENC econv_1 THENC
      COMB2_CONV (RAND_CONV sconv) (RAND_CONV NUM_SUC_CONV))) tm in
  sconv;;
```

### Informal statement
`SUM_CONV` is a conversion function that evaluates summations over explicit numerical intervals of the form `sum(1..n) f`, where:
- `sum(1..n) f` represents the sum $\sum_{i=1}^{n} f(i)$
- The function works by repeatedly applying the recursive definition of sums

### Informal proof
The conversion is built using the theorem:
```
sum(1..1) f = f 1 ∧ sum(1..SUC n) f = sum(1..n) f + f(SUC n)
```

The proof of this theorem uses several existing results:
- `SUM_CLAUSES_NUMSEG` which provides basic properties of sums over numerical segments
- `LE_0` for basic inequality reasoning
- `ARITH_RULE` to establish that `1 <= SUC n`
- `SUM_SING_NUMSEG` for handling single-element sums

The implementation creates a conversion that:
1. For the base case `sum(1..1) f`, directly applies the first conjunct of the theorem
2. For other cases `sum(1..n) f` where `n > 1`:
   - Converts `n` to successor form (`SUC m`)
   - Applies the second conjunct of the theorem
   - Recursively processes the smaller sum `sum(1..m) f`
   - Handles the successor notation in `f(SUC n)`

### Mathematical insight
`SUM_CONV` is a computational conversion that evaluates explicit finite sums by repeatedly applying the inductive definition of summation. This conversion is particularly useful for:

1. Simplifying expressions containing explicit numerical sums
2. Performing symbolic computation of sums where both the interval and function are explicitly given
3. Supporting automation in proofs involving summations

The conversion follows a common pattern in HOL Light where complex expressions are evaluated by recursively applying simpler rules.

### Dependencies
- `SUM_CLAUSES_NUMSEG` - Basic properties of sums over numerical segments
- `SUM_SING_NUMSEG` - Property of sums over single-element segments
- `LE_0` - Basic inequality reasoning
- `ARITH_RULE` - Arithmetic reasoning
- `GEN_REWRITE_CONV` - General rewriting conversion
- `LAND_CONV`, `RAND_CONV` - Conversions applied to specific parts of terms
- `COMB2_CONV` - Combining conversions
- `NUM_SUC_CONV` - Conversion for successor notation

### Porting notes
When porting this to other systems:
1. Ensure the target system has equivalent operations for numerical summations
2. Implement the recursive evaluation strategy, which may require different tactics in other systems
3. Be aware that conversion-style rewriting might be handled differently in other proof assistants
4. The implementation uses HOL Light's combinatorial approach to conversions, which might need adaptation

---

## PRIMERECIP_HARMONIC_LBOUND

### PRIMERECIP_HARMONIC_LBOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRIMERECIP_HARMONIC_LBOUND = prove
 (`!n. (&3 / (&16 * ln(&32))) * sum(1..n) (\i. &1 / &i) <=
       sum(1..32 EXP n) (\i. if prime(i) then &1 / &i else &0)`,
  MATCH_MP_TAC INDUCTION_FROM_1 THEN CONJ_TAC THENL
   [SIMP_TAC[SUM_TRIV_NUMSEG; ARITH; SUM_SING_NUMSEG; REAL_MUL_RZERO] THEN
    REWRITE_TAC[PRIME_1; REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH; SUM_SING_NUMSEG] THEN
    CONV_TAC(RAND_CONV SUM_CONV) THEN REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SYM(REAL_RAT_REDUCE_CONV `&2 pow 5`)] THEN
    SIMP_TAC[LN_POW; REAL_OF_NUM_LT; ARITH; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LN_2_COMPOSITION; real_div; real_sub] THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `b - a <= s2 - s1 ==> a <= s1 ==> b <= s2`) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; REAL_ADD_SUB; ARITH_RULE `1 <= SUC n`] THEN
  MP_TAC(SPEC `32 EXP n` PII_UBOUND_5) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `32 EXP 1` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(SPEC `32 EXP (SUC n)` PII_LBOUND) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `32 EXP 1` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN REWRITE_TAC[ARITH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP(REAL_ARITH
   `a <= s1 /\ s2 <= b ==> a - b <= s1 - s2`)) THEN
  SIMP_TAC[pii; PSUM_SUM_NUMSEG; EXP_EQ_0; ARITH; ADD_SUB2] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[EXP; ARITH_RULE `32 * n = n + 31 * n`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; REAL_ADD_SUB] THEN
  REWRITE_TAC[ARITH_RULE `n + 31 * n = 32 * n`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv(&32 pow (SUC n)) *
    sum(32 EXP n + 1 .. 32 EXP SUC n) (\i. if prime i then &1 else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `32 EXP n + 1 <= i` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[ARITH_RULE `~(0 < i) <=> i = 0`] THEN
    REWRITE_TAC[LE; ARITH; ADD_EQ_0]] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM real_div; REAL_POW_LT; REAL_LE_RDIV_EQ;
           REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `a <= x ==> b <= a ==> b <= x`)) THEN
  SIMP_TAC[LN_POW; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  REWRITE_TAC[REAL_FIELD
   `&1 / &2 * (&32 * n32) / (n1 * l) - &5 * n32 / (n * l) =
    (n32 / l) * (&16 / n1 - &5 / n)`] THEN
  REWRITE_TAC[REAL_FIELD
   `(&3 / (&16 * l) * i) * &32 * n32 = (n32 / l) * (&6 * i)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; LN_POS; REAL_OF_NUM_LE; ARITH] THEN
  REWRITE_TAC[real_div; REAL_ARITH
   `&6 * &1 * n1 <= &16 * n1 - &5 * n <=> n <= inv(inv(&2)) * n1`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, we have:
$$\frac{3}{16 \ln(32)} \sum_{i=1}^{n} \frac{1}{i} \leq \sum_{i=1}^{32^n} \begin{cases} \frac{1}{i} & \text{if $i$ is prime} \\ 0 & \text{otherwise} \end{cases}$$

This theorem provides a lower bound for the sum of reciprocals of primes up to $32^n$ in terms of the harmonic series up to $n$.

### Informal proof
The proof proceeds by induction on $n$ starting from 1.

**Base cases:**
- For $n = 0$: Both sides evaluate to zero since the sums are over empty ranges.
- For $n = 1$: We compute the sum of reciprocals of primes up to $32 = 2^5$, which easily satisfies the inequality after simplification.

**Inductive step:** Assume the inequality holds for some $n$. We need to show it holds for $n+1$.

We approach this by analyzing the difference between the values at $n+1$ and $n$:
- Let $S_1$ be the left side at $n$ and $S_2$ be the left side at $n+1$
- Let $T_1$ be the right side at $n$ and $T_2$ be the right side at $n+1$

If we can show that $S_2 - S_1 \leq T_2 - T_1$, then the inductive step follows.

We use the bounds on the prime-counting function:
- From `PII_UBOUND_5`: $\pi(32^n) \leq 5 \cdot \frac{32^n}{\ln(32^n)}$
- From `PII_LBOUND`: $\frac{1}{2} \cdot \frac{32^{n+1}}{\ln(32^{n+1})} \leq \pi(32^{n+1})$

The difference $T_2 - T_1$ is the sum of reciprocals of primes between $32^n + 1$ and $32^{n+1}$. By comparing this with the appropriate bounds and using the fact that $\frac{1}{i} \geq \frac{1}{32^{n+1}}$ for all $i$ in the range, we can establish the required inequality.

The proof concludes with algebraic manipulations to show that the resulting expression satisfies the original inequality.

### Mathematical insight
This theorem establishes a relationship between the harmonic series and the sum of reciprocals of primes. It shows that the sum of reciprocals of primes up to a given bound is at least a constant multiple of a partial sum of the harmonic series, where the index of the harmonic sum is logarithmic in the bound for the primes.

This is significant because it provides a lower bound on the growth rate of the sum of reciprocals of primes, connecting it to the well-understood behavior of the harmonic series. The result contributes to our understanding of the distribution of prime numbers and is relevant to analytic number theory.

The constant factor $\frac{3}{16\ln(32)}$ is carefully chosen to make the induction work, and the specific use of powers of 32 as bounds simplifies the calculations.

### Dependencies
- **Theorems**:
  - `LN_2_COMPOSITION`: A specific identity for $\ln(2)$ in terms of other logarithms
  - `PII_LBOUND`: Lower bound for the prime-counting function: $\frac{1}{2} \cdot \frac{n}{\ln(n)} \leq \pi(n)$ for $n \geq 3$
  - `PII_UBOUND_5`: Upper bound for the prime-counting function: $\pi(n) \leq 5 \cdot \frac{n}{\ln(n)}$ for $n \geq 3$
- **Definitions**:
  - `pii`: The prime-counting function $\pi(n) = \sum_{i=1}^{n} [i \text{ is prime}]$

### Porting notes
When porting this theorem:
1. The proof relies heavily on bounds for the prime-counting function, so those theorems should be ported first.
2. The proof uses induction starting from 1, which is common in number theory but might require adaptation in some systems.
3. The specific value of the constant $\frac{3}{16\ln(32)}$ was carefully chosen to make the induction work. In another system, you might need to verify that the numeric calculations in the proof still hold.
4. The proof uses a mixture of algebraic manipulation and established results about prime distribution, so the general structure should transfer well to other systems.

---

## PRIMERECIP_LBOUND

### PRIMERECIP_LBOUND
- prove

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PRIMERECIP_LBOUND = prove
 (`!n. &3 / (&32 * ln(&32)) * &n
       <= sum (1 .. 32 EXP (2 EXP n)) (\i. if prime i then &1 / &i else &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 / (&16 * ln(&32)) * sum (1 .. 2 EXP n) (\i. &1 / &i)` THEN
  REWRITE_TAC[PRIMERECIP_HARMONIC_LBOUND] THEN
  REWRITE_TAC[REAL_FIELD
   `&3 / (&32 * ln(&32)) * &n = &3 / (&16 * ln(&32)) * (&n / &2)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REWRITE_RULE[real_ge] HARMONIC_LEMMA] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; LN_POS; REAL_OF_NUM_LE; ARITH]);;
```

### Informal statement
For all natural numbers $n$, we have:
$$\frac{3}{32 \ln(32)} \cdot n \leq \sum_{i=1}^{32^{2^n}} \begin{cases} \frac{1}{i} & \text{if $i$ is prime} \\ 0 & \text{otherwise} \end{cases}$$

In other words, the sum of reciprocals of prime numbers up to $32^{2^n}$ has a lower bound of $\frac{3}{32 \ln(32)} \cdot n$.

### Informal proof
To prove this, we use a transitive inequality argument:

1. First, we establish that:
   $$\frac{3}{32 \ln(32)} \cdot n \leq \frac{3}{16 \ln(32)} \cdot \sum_{i=1}^{2^n} \frac{1}{i}$$

2. This relies on the intermediate result `PRIMERECIP_HARMONIC_LBOUND` (not provided in dependencies).

3. We algebraically rewrite the left side as:
   $$\frac{3}{32 \ln(32)} \cdot n = \frac{3}{16 \ln(32)} \cdot \frac{n}{2}$$
   using field arithmetic.

4. Then we apply left multiplication to both sides of the inequality.

5. We apply `HARMONIC_LEMMA` which states that $\sum_{i=1}^{2^m} \frac{1}{i} \geq \frac{m}{2}$, which gives us:
   $$\sum_{i=1}^{2^n} \frac{1}{i} \geq \frac{n}{2}$$

6. Finally, we verify that $\frac{3}{16 \ln(32)}$ is positive because $\ln(32)$ is positive, completing the proof.

### Mathematical insight
This theorem provides a concrete lower bound for the sum of reciprocals of primes up to a large number ($32^{2^n}$). 

It connects to the well-known result that the sum of reciprocals of all primes diverges, but at a much slower rate than the harmonic series. This theorem quantifies that relationship for a specific range of values.

The proof leverages the relationship between the harmonic sum and the sum of prime reciprocals, establishing a proportional lower bound that grows with $n$, showing that the sum of prime reciprocals, while growing slowly, does grow without bound as the upper limit increases.

### Dependencies
#### Theorems
- `HARMONIC_LEMMA`: For all $m$, $\sum_{n=1}^{2^m} \frac{1}{n} \geq \frac{m}{2}$
- `PRIMERECIP_HARMONIC_LBOUND` (not provided in dependencies)

### Porting notes
When porting this theorem:
- Ensure the definition of primality matches between systems
- Check how the target system handles conditionals in sums
- The proof relies on algebraic manipulation of real numbers and logarithms, so ensure the target system has good support for real arithmetic

---

## UNBOUNDED_DIVERGENT

### Name of formal statement
UNBOUNDED_DIVERGENT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNBOUNDED_DIVERGENT = prove
 (`!s. (!k. ?N. !n. n >= N ==> sum(1..n) s >= k)
       ==> ~(convergent(\n. sum(1..n) s))`,
  REWRITE_TAC[convergent; SEQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l + &1`) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `M:num` THEN
  DISCH_THEN(MP_TAC o SPEC `M + N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M + N:num`) THEN
  REWRITE_TAC[LE_ADD; ONCE_REWRITE_RULE[ADD_SYM] LE_ADD; GE] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
Let $s$ be a sequence. If for all $k$, there exists $N$ such that for all $n \geq N$, the partial sum $\sum_{i=1}^{n} s_i \geq k$, then the sequence of partial sums $(\sum_{i=1}^{n} s_i)_{n=1}^{\infty}$ diverges.

### Informal proof
We prove the contrapositive by showing that if the sequence of partial sums converges, then it cannot satisfy the unboundedness property stated in the hypothesis.

1. We start with the definition of convergence: assume there exists a limit $l$ such that for all $\varepsilon > 0$, there exists $M$ such that for all $n \geq M$, $|\sum_{i=1}^{n} s_i - l| < \varepsilon$.

2. Choose $\varepsilon = 1$, which gives us that for some $M$, whenever $n \geq M$, we have $|\sum_{i=1}^{n} s_i - l| < 1$.

3. From the hypothesis, with $k = l + 1$, there exists $N$ such that for all $n \geq N$, $\sum_{i=1}^{n} s_i \geq l + 1$.

4. Consider $n = M + N$. Then $n \geq M$ implies $|\sum_{i=1}^{n} s_i - l| < 1$, which means $\sum_{i=1}^{n} s_i < l + 1$.

5. But also $n \geq N$ implies $\sum_{i=1}^{n} s_i \geq l + 1$, creating a contradiction.

6. This contradiction proves that the sequence of partial sums cannot converge.

### Mathematical insight
This theorem establishes a basic and important result about the relationship between unboundedness and divergence. Specifically, it shows that if the partial sums of a sequence grow arbitrarily large, then the sequence of partial sums must diverge. This is a standard result in analysis and forms part of the foundation for understanding series convergence.

The result is intuitive: if the partial sums can exceed any arbitrary bound $k$, then they cannot settle down to a finite limit, which is precisely what divergence means. This theorem is particularly useful in proving the divergence of series where terms do not approach zero.

### Dependencies
No specific theorems or definitions were listed in the dependencies, but the proof uses:
- `convergent` - Definition of a convergent sequence
- `SEQ` - Likely a definition related to sequences
- Real arithmetic tactics and properties

### Porting notes
When porting this theorem:
1. Ensure that the target system has a suitable definition of convergent sequences and partial sums.
2. The proof relies on contradiction and the properties of real numbers, which should be available in most proof assistants.
3. The arithmetic reasoning at the end of the proof is handled by `REAL_ARITH_TAC` in HOL Light; the target system should have a similar arithmetic solver or you may need to expand this into more explicit steps.

---

## PRIMERECIP_DIVERGES_NUMSEG

### Name of formal statement
PRIMERECIP_DIVERGES_NUMSEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMERECIP_DIVERGES_NUMSEG = prove
 (`~(convergent (\n. sum (1..n) (\i. if prime i then &1 / &i else &0)))`,
  MATCH_MP_TAC UNBOUNDED_DIVERGENT THEN X_GEN_TAC `k:real` THEN
  MP_TAC(SPEC `&3 / (&32 * ln(&32))` REAL_ARCH) THEN
  SIMP_TAC[REAL_LT_DIV; LN_POS_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(MP_TAC o SPEC `k:real`) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `32 EXP (2 EXP N)` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[GE; real_ge] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&N * &3 / (&32 * ln (&32))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(1 .. 32 EXP (2 EXP N)) (\i. if prime i then &1 / &i else &0)` THEN
  REWRITE_TAC[PRIMERECIP_LBOUND] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS]);;
```

### Informal statement
The theorem states that the series $\sum_{i=1}^{n} \frac{1}{i}$ where $i$ is restricted to prime numbers is divergent. Formally:

$$\text{The sequence } \left(\sum_{i=1}^{n} \left(\frac{1}{i} \text{ if } i \text{ is prime, otherwise } 0\right)\right)_{n=1}^{\infty} \text{ is not convergent.}$$

### Informal proof
The proof shows that the series of reciprocals of prime numbers diverges by demonstrating that the sequence of partial sums is unbounded:

* Apply the theorem `UNBOUNDED_DIVERGENT` which states that if a sequence is unbounded, then it diverges.
* For any real value $k$, we need to find a sufficiently large index $n$ where the partial sum exceeds $k$.
* Use the Archimedean property of real numbers applied to $\frac{3}{32\ln(32)}$, which gives us some $N$ such that $N \cdot \frac{3}{32\ln(32)} > k$.
* Set $n = 32^{2^N}$.
* For any $n' \geq n$, the partial sum $\sum_{i=1}^{n'} \left(\frac{1}{i} \text{ if } i \text{ is prime, otherwise } 0\right)$ exceeds $N \cdot \frac{3}{32\ln(32)} > k$.
* This leverages the theorem `PRIMERECIP_LBOUND` which provides a lower bound on the sum of reciprocals of prime numbers.
* For the remaining terms in the sum, we observe that each term is non-negative (when $i$ is prime, $\frac{1}{i} > 0$, and otherwise the term is 0).

Since we can make the partial sum exceed any arbitrary $k$ by choosing a sufficiently large $n$, the sequence is unbounded and thus diverges.

### Mathematical insight
This theorem establishes the divergence of the sum of reciprocals of prime numbers, which is a classical result in number theory. The result is interesting because while the density of primes decreases (as established by the Prime Number Theorem), the reciprocals of primes still sum to infinity.

This contrasts with the fact that the sum of reciprocals of perfect squares converges. The divergence of the sum of reciprocals of primes indicates the "density" of prime numbers is sufficient to prevent convergence, despite their growing sparsity.

The proof technique uses a lower bound on the partial sums related to the distribution of prime numbers, showing that no matter how large a value we choose, we can find a partial sum exceeding that value.

### Dependencies
- `UNBOUNDED_DIVERGENT` - Theorem stating that unbounded sequences diverge
- `REAL_ARCH` - Archimedean property of real numbers
- `PRIMERECIP_LBOUND` - Lower bound for sum of reciprocals of prime numbers
- Various arithmetic and real number theorems for manipulating inequalities

### Porting notes
When porting this theorem:
1. Ensure the target system has a suitable definition of convergence for sequences
2. Verify that the necessary number theory results about prime numbers are available, particularly bounds on the sum of reciprocals of primes
3. The proof relies heavily on real analysis results for handling inequalities and convergence, so these foundations must be in place

---

## PRIMERECIP_DIVERGES

### Name of formal statement
PRIMERECIP_DIVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMERECIP_DIVERGES = prove
 (`~(convergent (\n. sum {p | prime p /\ p <= n} (\p. &1 / &p)))`,
  MP_TAC PRIMERECIP_DIVERGES_NUMSEG THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> ~a ==> ~b`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [SUBGOAL_THEN `{p | prime p /\ p <= 0} = {}`
     (fun th -> SIMP_TAC[SUM_CLAUSES; SUM_TRIV_NUMSEG; th; ARITH]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LE] THEN
    MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= SUC n} =
        if prime(SUC n) then (SUC n) INSERT {p | prime p /\ p <= n}
        else {p | prime p /\ p <= n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p <= n}`
   (fun th -> SIMP_TAC[SUM_CLAUSES; th])
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n` THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[PRIME_0; ARITH_RULE `1 <= i <=> ~(i = 0)`];
    REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `~(SUC n <= n)`; REAL_ADD_AC]]);;
```

### Informal statement
The sum of reciprocals of prime numbers up to $n$ diverges as $n$ tends to infinity. Formally:
$$\neg\text{convergent}\left(n \mapsto \sum_{p \in \{p \mid \text{prime}(p) \wedge p \leq n\}} \frac{1}{p}\right)$$

This states that the sequence of partial sums $\sum_{p \leq n, p \text{ prime}} \frac{1}{p}$ does not converge to any finite limit.

### Informal proof
The proof builds on the theorem `PRIMERECIP_DIVERGES_NUMSEG`, which establishes the divergence of prime reciprocals when indexed by position rather than by value.

The proof proceeds as follows:

* First, apply `PRIMERECIP_DIVERGES_NUMSEG` which states that the sum of reciprocals of prime numbers indexed by position diverges.
* The goal is to show that this divergence implies the divergence of the sum indexed by value.
* To establish this implication, we need to show that the two sequences are identical.

We prove that for all $n$:
$$\sum_{p \in \{p \mid \text{prime}(p) \wedge p \leq n\}} \frac{1}{p} = \sum_{i=1}^n \begin{cases} \frac{1}{i} & \text{if $i$ is prime} \\ 0 & \text{otherwise} \end{cases}$$

This is shown by induction on $n$:

* Base case ($n = 0$): 
  * We show that $\{p \mid \text{prime}(p) \wedge p \leq 0\} = \emptyset$ since 0 is not prime.
  * Thus the sum equals 0, which matches the right-hand side.

* Inductive step:
  * We prove that $\{p \mid \text{prime}(p) \wedge p \leq \text{SUC}(n)\}$ equals either:
    * $\{\text{SUC}(n)\} \cup \{p \mid \text{prime}(p) \wedge p \leq n\}$ if $\text{SUC}(n)$ is prime, or
    * $\{p \mid \text{prime}(p) \wedge p \leq n\}$ if $\text{SUC}(n)$ is not prime
  * This allows us to express the sum at $\text{SUC}(n)$ in terms of the sum at $n$, establishing the inductive step.

Given that both sequences are identical and one diverges, the other must also diverge.

### Mathematical insight
This theorem is a classical result in number theory, establishing an important property of the distribution of prime numbers. The divergence of the sum of reciprocals of primes contrasts with the convergence of the sum of reciprocals of perfect squares, highlighting the relative "density" of prime numbers among natural numbers.

The result was first proved by Leonhard Euler in 1737 and is related to the prime number theorem. While the reciprocal sum of all natural numbers (the harmonic series) also diverges, it does so very slowly - the partial sum exceeds any given value eventually but grows at a logarithmic rate. The divergence of the prime reciprocal sum is even slower, reflecting the sparsity of primes compared to natural numbers.

This formulation uses sets and explicit bounds, which is perhaps more intuitive to mathematicians than the version indexed by position in the sequence of primes.

### Dependencies
- `PRIMERECIP_DIVERGES_NUMSEG`: The theorem that establishes the divergence of prime reciprocals when indexed by position.
- Various basic arithmetic, set theory, and summation theorems.

### Porting notes
When porting this proof:
- Ensure your system has a good library of theorems about summation over sets and finite sequences.
- The proof relies on set-theoretic manipulations and case analysis on whether a number is prime.
- A key aspect is the connection between two different ways of formulating the sum of prime reciprocals.
- In some systems, you might need to explicitly state the finiteness of the set of primes less than n.

---

