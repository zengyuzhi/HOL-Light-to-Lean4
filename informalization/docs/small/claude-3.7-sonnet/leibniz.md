# leibniz.ml

## Overview

Number of statements: 10

This file formalizes Leibniz's series for π, which states that π/4 = 1 - 1/3 + 1/5 - 1/7 + ... The implementation likely includes the formal statement of this infinite alternating series, a proof of its convergence to π/4, and related properties. It builds upon transcendental functions from the transc.ml library, using them to establish the connection between the infinite series and the value of π.

## ALTERNATING_SUM_BOUNDS

### ALTERNATING_SUM_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALTERNATING_SUM_BOUNDS = prove
 (`!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. (EVEN m ==> &0 <= sum(m,n) a /\ sum(m,n) a <= a(m)) /\
                 (ODD m ==> a(m) <= sum(m,n) a /\ sum(m,n) a <= &0)`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[ODD; EVEN] THENL
   [SIMP_TAC[sum; ODD_EXISTS; EVEN_EXISTS; LEFT_IMP_EXISTS_THM; ADD1] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; GSYM SUM_SPLIT] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl) o SPEC `SUC m`) THEN
  REWRITE_TAC[ODD; EVEN; SUM_1] THEN REWRITE_TAC[ADD1; GSYM NOT_EVEN] THEN
  UNDISCH_THEN `!n. abs(a(n + 1)) <= abs(a n)` (MP_TAC o SPEC `m:num`) THEN
  ASM_CASES_TAC `EVEN m` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
    REWRITE_TAC[ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[ADD1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC]);;
```

### Informal statement
Let $a$ be a sequence of real numbers satisfying:
1. For all natural numbers $n$, $a(2n+1) \leq 0$ and $0 \leq a(2n)$
2. For all natural numbers $n$, $|a(n+1)| \leq |a(n)|$

Then for all natural numbers $m$ and $n$:
- If $m$ is even, then $0 \leq \sum_{i=m}^{m+n} a(i) \leq a(m)$
- If $m$ is odd, then $a(m) \leq \sum_{i=m}^{m+n} a(i) \leq 0$

### Informal proof
This proof establishes bounds for partial sums of alternating sequences with decreasing absolute values - a key property for convergence of alternating series.

The proof proceeds by induction on $n$:

- **Base case** ($n = 0$):
  For $n = 0$, we have $\sum_{i=m}^{m+0} a(i) = a(m)$. The inequality becomes:
  - For even $m$: $0 \leq a(m) \leq a(m)$, which holds by our assumptions
  - For odd $m$: $a(m) \leq a(m) \leq 0$, which also holds by our assumptions

- **Inductive step**:
  Assume the result holds for $n$, then we need to prove it for $n+1$.
  
  We use the fact that $\sum_{i=m}^{m+(n+1)} a(i) = \sum_{i=m}^{m+n} a(i) + a(m+n+1)$
  
  Consider two cases:
  
  1. When $m$ is even:
     From the induction hypothesis, we have $0 \leq \sum_{i=m}^{m+n} a(i) \leq a(m)$.
     If $m+n+1$ is odd, then $a(m+n+1) \leq 0$. 
     If $m+n+1$ is even, then $a(m+n+1) \geq 0$.
     
     Using $|a(n+1)| \leq |a(n)|$ and the parity of $m+n+1$, we can show that the bounds hold.
     
  2. When $m$ is odd:
     From the induction hypothesis, we have $a(m) \leq \sum_{i=m}^{m+n} a(i) \leq 0$.
     Similar to the previous case, we use the decreasing absolute values property and 
     the parity of $m+n+1$ to show the bounds hold.

In both cases, real arithmetic completes the proof.

### Mathematical insight
This theorem provides bounds for partial sums of alternating sequences where absolute values are non-increasing. It's a fundamental result for analyzing alternating series, showing that:

1. For series starting with a positive term (even index), the partial sums are bounded between 0 and the first term
2. For series starting with a negative term (odd index), the partial sums are bounded between the first term and 0

This is critical for proving convergence of alternating series like Leibniz's series for π and establishing error bounds for partial sums of such series. The result is the foundation of the alternating series test (Leibniz criterion) in analysis, which states that alternating series whose terms decrease in absolute value converge.

### Dependencies
None explicitly listed in the provided dependency information.

### Porting notes
When porting this theorem:
1. Ensure the definition of `sum(m,n)` in the target system matches HOL Light's - it represents the sum of terms from index m to m+n inclusive.
2. The proof relies on case analysis based on parity of indices, so ensure the target system has good support for handling even/odd properties.
3. The real arithmetic automation in the target system may require different tactics than HOL Light's `REAL_ARITH_TAC`.

---

## ALTERNATING_SUM_BOUND

### Name of formal statement
ALTERNATING_SUM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALTERNATING_SUM_BOUND = prove
 (`!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. abs(sum(m,n) a) <= abs(a m)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALTERNATING_SUM_BOUNDS) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN m` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any sequence $a$, if:
- For all $n$, $a(2n+1) \leq 0$ and $0 \leq a(2n)$ (alternating sign pattern with even terms non-negative and odd terms non-positive)
- For all $n$, $|a(n+1)| \leq |a(n)|$ (absolute values form a non-increasing sequence)

Then for all $m$ and $n$, the absolute value of the sum $\left|\sum_{i=m}^{m+n-1} a(i)\right|$ is bounded by the absolute value of the first term $|a(m)|$.

### Informal proof
This theorem is a direct consequence of the more general `ALTERNATING_SUM_BOUNDS` theorem, which is applied by matching the patterns and constraints.

The proof proceeds as follows:
- Start with the sequence $a$ satisfying the given conditions.
- Apply the `ALTERNATING_SUM_BOUNDS` theorem, which provides bounds for alternating sums.
- For all $m$ and $n$, consider two cases based on the parity of $m$:
  - When $m$ is even, the result follows directly from `ALTERNATING_SUM_BOUNDS`.
  - When $m$ is odd (i.e., not even), the result still holds.
- The final step uses real arithmetic reasoning to establish the bound.

### Mathematical insight
This theorem provides a tight upper bound for the absolute value of partial sums of alternating sequences with decreasing magnitudes. It captures the intuition that in an alternating sequence with decreasing magnitudes, the first term dominates the behavior of any partial sum.

The result is particularly useful in analysis for estimating the size of alternating series and establishing convergence properties. It's closely related to the alternating series test (Leibniz's criterion) in calculus, which states that if a sequence $a_n$ has decreasing absolute values and alternating signs, then $\sum_{n=1}^{\infty} a_n$ converges.

This theorem gives us a precise quantitative bound on the partial sums, showing that not only do they converge, but their magnitude never exceeds that of the first term.

### Dependencies
- Theorems:
  - `ALTERNATING_SUM_BOUNDS`: Provides the core result about bounds for alternating sums
  - `GSYM NOT_EVEN`: Relates the "not even" predicate to oddness
  - `EVEN`: Predicate for even numbers
  
- Tactics and conversions:
  - `REAL_ARITH_TAC`: Automated reasoning about real arithmetic

### Porting notes
When porting this theorem:
1. Ensure that the dependent theorem `ALTERNATING_SUM_BOUNDS` is ported first
2. The target system should have a good way to handle parity (even/odd) of naturals
3. The automation for real arithmetic (`REAL_ARITH_TAC`) may need to be replaced with explicit reasoning or a similar tactic in the target system
4. The sum notation in the target system might differ from HOL Light's `sum(m,n)` which represents $\sum_{i=m}^{m+n-1} a(i)$

---

## SUMMABLE_ALTERNATING

### Name of formal statement
SUMMABLE_ALTERNATING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_ALTERNATING = prove
 (`!v. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n))) /\ a tends_num_real &0
       ==> summable a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SER_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o GEN_REWRITE_RULE I [SEQ]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_MESON_TAC[ALTERNATING_SUM_BOUND; REAL_LET_TRANS]);;
```

### Informal statement
For any sequence $a : \mathbb{N} \to \mathbb{R}$, if:
1. For all $n$, $a(2n+1) \leq 0$ and $0 \leq a(2n)$ (alternating sign condition)
2. For all $n$, $|a(n+1)| \leq |a(n)|$ (decreasing absolute value)
3. $a$ tends to $0$ (i.e., $\lim_{n \to \infty} a(n) = 0$)

Then the series $\sum_{n=0}^{\infty} a(n)$ is summable (i.e., converges).

### Informal proof
This proof establishes the convergence of an alternating series with decreasing terms that approach zero, which is a generalized form of the alternating series test.

The proof proceeds as follows:

- We rewrite the goal using `SER_CAUCHY`, which represents the Cauchy criterion for series convergence: a series is summable if for every $\varepsilon > 0$, there exists $N$ such that for all $m \geq n \geq N$, $|\sum_{i=n}^{m} a(i)| < \varepsilon$.

- We apply the definition of a sequence tending to zero (using `SEQ`), which gives us that for any $\varepsilon > 0$, there exists $N$ such that for all $n \geq N$, $|a(n) - 0| = |a(n)| < \varepsilon$.

- The key insight is to use the `ALTERNATING_SUM_BOUND` theorem, which states that for an alternating sequence with decreasing magnitudes, the absolute value of any partial sum starting at position $n$ is bounded by the absolute value of the first term $|a(n)|$.

- Since $a(n)$ approaches zero, we can make $|a(n)| < \varepsilon$ for sufficiently large $n$, and by the alternating sum bound, all partial sums starting at such $n$ will also be less than $\varepsilon$ in magnitude.

- We combine these facts using transitivity of the less-than-or-equal relation to conclude that the series satisfies the Cauchy criterion and is therefore summable.

### Mathematical insight
This theorem formalizes a generalization of the alternating series test (also known as the Leibniz test) in calculus. The classical alternating series test requires strictly decreasing absolute values, while this version only requires non-increasing absolute values.

The alternating series test is a powerful tool for determining convergence of series where the terms alternate in sign and decrease in magnitude. Examples include important series like $\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n}$ (the alternating harmonic series).

The key insight is that for alternating series with decreasing magnitudes, the partial sums oscillate around the limit with decreasing amplitude, making the series convergent as long as the terms approach zero.

### Dependencies
- `SER_CAUCHY`: Characterization of summable series using the Cauchy criterion
- `SEQ`: Definition of a sequence converging to a limit
- `ALTERNATING_SUM_BOUND`: Theorem stating that for an alternating sequence with decreasing magnitudes, the remainder sum is bounded by the first term
- `REAL_LET_TRANS`: Transitivity of less-than-or-equal relation for reals
- `REAL_SUB_RZERO`: Simplification rule for subtracting zero from a real number

### Porting notes
When porting this theorem:
- Ensure your target system has appropriate library theorems for the Cauchy criterion for series and for bounding alternating sums.
- The proof relies on the `ALTERNATING_SUM_BOUND` theorem, which may need to be ported first if not available in the target library.
- The statement uses a sequence `a` indexed from 0, which might need adjustment if your target system prefers sequences indexed from 1.
- Note that HOL Light represents "tends to" with `tends_num_real`, which corresponds to the limit of a sequence approaching a real number.

---

## REAL_ATN_POWSER_ALT

### Name of formal statement
REAL_ATN_POWSER_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_ATN_POWSER_ALT = prove
 (`!x. abs(x) < &1
       ==> (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1))
           sums (atn x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_ATN_POWSER) THEN
  FIRST_ASSUM(MP_TAC o C CONJ (ARITH_RULE `0 < 2`) o
              MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_GROUP) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[SUM_2; EVEN_MULT; EVEN_ADD; ARITH_EVEN; ADD_SUB] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `n * 2 = 2 * n`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_LID]);;
```

### Informal statement
For any real number $x$ such that $|x| < 1$, the power series
$$\sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1} \cdot x^{2n+1}$$
converges to $\arctan(x)$.

### Informal proof
This theorem provides an alternative formulation of the power series for arctangent. The proof leverages the existing theorem `REAL_ATN_POWSER` and demonstrates the equivalence of the two series expressions:

* Start with the assumption that $|x| < 1$.
* Apply the existing theorem `REAL_ATN_POWSER` to establish that the power series for $\arctan(x)$ converges.
* Use the fact that the series is summable (via `SUM_SUMMABLE`), and apply `SER_GROUP` with the grouping factor of 2.
* The grouping of terms transforms the original series into the form stated in this theorem.
* Simplify arithmetic expressions involving even/odd terms.
* Use properties of multiplication and division to complete the equivalence.

The key step is regrouping the terms of the original arctangent power series to obtain this alternative formulation.

### Mathematical insight
This theorem provides an alternative representation of the power series for arctangent function. While the standard power series for arctangent is often expressed as $\sum_{n=0}^{\infty} \frac{(-1)^n x^{2n+1}}{2n+1}$, this alternate form makes explicit the pattern of terms with alternating signs. The series converges for all $x$ in the interval $(-1,1)$.

This representation is particularly useful in numerical computations and for establishing properties of the arctangent function. The simple pattern of coefficients makes it easier to analyze and work with the arctangent series in various theoretical contexts.

### Dependencies
- Theorems:
  - `REAL_ATN_POWSER`: The original arctangent power series theorem
  - `SUM_SUMMABLE`: Theorem about summability of series
  - `SER_GROUP`: Theorem about regrouping series terms
  - `SUM_UNIQ`: Uniqueness of series sums
  - `SUM_2`: Theorem about grouping series terms by 2
  - `EVEN_MULT`, `EVEN_ADD`, `ARITH_EVEN`: Theorems about even numbers
  - Arithmetic rules and simplifications

### Porting notes
When porting this theorem:
1. Ensure the target system has an equivalent arctangent power series theorem to build upon
2. Verify that the system has theorems for regrouping and manipulating series
3. The proof relies heavily on series manipulation theorems, so make sure these are available or can be developed
4. The arithmetic simplifications may need to be adapted based on the target system's handling of even/odd numbers and numeric operations

---

## SUMMABLE_LEIBNIZ

### Name of formal statement
SUMMABLE_LEIBNIZ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_LEIBNIZ = prove
 (`summable (\n. (-- &1) pow n / &(2 * n + 1))`,
  MATCH_MP_TAC SUMMABLE_ALTERNATING THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ONE; real_div; REAL_MUL_LID; REAL_MUL_LNEG] THEN
    REWRITE_TAC[REAL_LE_LNEG; REAL_ADD_RID; REAL_LE_INV_EQ; REAL_POS];
    GEN_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
    REWRITE_TAC[SEQ; REAL_SUB_RZERO; REAL_ABS_DIV; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&1` o MATCH_MP REAL_ARCH) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&1 < x * e ==> e * x <= y ==> &1 < y`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;
```

### Informal statement
The series $\sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1}$ is summable.

### Informal proof
The proof applies the theorem for alternating series (`SUMMABLE_ALTERNATING`), which requires checking three conditions:

1. First, we verify that $\frac{(-1)^n}{2n+1} = \frac{(-1)^n \cdot 1}{2n+1}$, and that the sign alternates as required.

2. Second, we show that the absolute values of the terms form a decreasing sequence. We need to prove $\left|\frac{1}{2n+1}\right| \geq \left|\frac{1}{2(n+1)+1}\right|$, which simplifies to $\frac{1}{2n+1} \geq \frac{1}{2n+3}$. This follows from the fact that $2n+1 \leq 2n+3$ for all $n$, which implies $\frac{1}{2n+1} \geq \frac{1}{2n+3}$.

3. Finally, we prove that the sequence of terms converges to 0. For any $\varepsilon > 0$, we need to find $N$ such that $\left|\frac{1}{2n+1}\right| < \varepsilon$ for all $n \geq N$. 

   Using the Archimedean property (`REAL_ARCH`), we can find an $N$ such that $N > \frac{1}{\varepsilon}$. Then for any $n \geq N$, we have $n \geq N > \frac{1}{\varepsilon}$, which implies $2n+1 > n > \frac{1}{\varepsilon}$. Thus, $\frac{1}{2n+1} < \varepsilon$, completing the proof.

### Mathematical insight
This theorem proves the summability of the Leibniz series when $x = 1$, which gives the value $\frac{\pi}{4}$. This is a special case of the arctangent series expansion.

The Leibniz formula for $\pi$ states that $\frac{\pi}{4} = 1 - \frac{1}{3} + \frac{1}{5} - \frac{1}{7} + \cdots$, which is precisely the sum of the series in this theorem.

The alternating series test is a powerful tool for establishing convergence of series where the signs alternate, and the absolute values of the terms decrease monotonically to zero.

### Dependencies
#### Theorems
- `SUMMABLE_ALTERNATING`: A theorem for proving summability of alternating series
- `REAL_POW_ADD`: Properties of powers with addition in the exponent
- `REAL_POW_MUL`: Properties of powers with multiplication in the exponent
- `REAL_POW_POW`: Properties of iterated powers
- `REAL_POW_ONE`: Properties of powers of 1
- `REAL_LE_LNEG`: Properties of inequalities with negation
- `REAL_LE_INV_EQ`: Properties of inequalities with reciprocals
- `REAL_POS`: Positivity of real numbers
- `REAL_ABS_DIV`: Absolute value of a division
- `REAL_ABS_POW`: Absolute value of a power
- `REAL_ABS_NEG`: Absolute value of a negation
- `REAL_ABS_NUM`: Absolute value of a number
- `REAL_OF_NUM_LT`: Conversion of numerical inequality to real inequality
- `REAL_OF_NUM_LE`: Conversion of numerical inequality to real inequality
- `REAL_LT_LDIV_EQ`: Properties of inequalities with division
- `REAL_ARCH`: The Archimedean property of real numbers

### Porting notes
When porting this theorem, note that:
1. The handling of alternating series might differ between proof assistants
2. The specific formulation of the Archimedean property might vary
3. Some proof assistants might have more specialized tactics for handling series, which could simplify the proof

---

## SUM_DIFFERENCES

### Name of formal statement
SUM_DIFFERENCES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_DIFFERENCES = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i) - a(i+1)) = a(m) - a(n + 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH; REAL_SUB_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `n < n + 1`; REAL_SUB_REFL] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG;
    ARITH_RULE `m <= n + 1 ==> m <= SUC n /\ m <= SUC n + 1`] THEN
  REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any sequence $a$ and natural numbers $m$ and $n$ such that $m \leq n + 1$, the sum of differences $\sum_{i=m}^{n} (a(i) - a(i+1))$ equals $a(m) - a(n + 1)$.

### Informal proof
The proof proceeds by induction on $n$.

**Base case:** When $n = 0$:
- We need $m \leq 0 + 1$, which means $m = 0$ or $m = 1$ (by arithmetic).
- If $m = 0$, we have a single term sum $\sum_{i=0}^{0} (a(i) - a(i+1)) = a(0) - a(1)$, which matches the required result.
- If $m = 1$, we have $\sum_{i=1}^{0} (a(i) - a(i+1))$. Since this is an empty sum (as the lower bound exceeds the upper bound), it equals $0$. Also, $a(m) - a(n+1) = a(1) - a(1) = 0$, so the result holds.

**Inductive case:** Assume the result holds for some $n$, and consider $n+1$:
- We need $m \leq (n+1) + 1$, which is equivalent to $m \leq n + 1$ or $m = (n+1) + 1$ (by arithmetic).
- If $m = (n+1) + 1$, then $\sum_{i=m}^{n+1} (a(i) - a(i+1))$ is an empty sum and equals $0$. Also, $a(m) - a((n+1)+1) = a(m) - a(m) = 0$, so the result holds.
- Otherwise, $m \leq n + 1$, so we can use the induction hypothesis.
- Using the recursive definition of sum: 
  $\sum_{i=m}^{n+1} (a(i) - a(i+1)) = \sum_{i=m}^{n} (a(i) - a(i+1)) + (a(n+1) - a(n+2))$
- By the induction hypothesis, $\sum_{i=m}^{n} (a(i) - a(i+1)) = a(m) - a(n+1)$
- Thus, $\sum_{i=m}^{n+1} (a(i) - a(i+1)) = a(m) - a(n+1) + (a(n+1) - a(n+2)) = a(m) - a(n+2)$
- This equals $a(m) - a((n+1)+1)$, which is our desired result.

### Mathematical insight
This theorem provides a simple closed form for telescoping sums where each term consists of the difference between adjacent elements of a sequence. The key insight is the telescoping nature of such sums, where intermediate terms cancel out, leaving only the difference between the first and last (plus one) terms.

This is a fundamental result used in many mathematical contexts, particularly in discrete calculus where differences play the role analogous to derivatives in continuous calculus. The theorem is especially useful when working with series, sequences, and discrete approximations.

### Dependencies
No specific dependencies are listed, but the proof uses:
- `SUM_SING_NUMSEG` (for handling single-term sums)
- `SUM_TRIV_NUMSEG` (for handling empty sums)
- `SUM_CLAUSES_NUMSEG` (for recursive definition of sums)
- Various arithmetic rules and real number properties

### Porting notes
When porting this theorem:
- Ensure your system has a good way to handle telescoping sums
- Make sure the empty sum is properly defined to be 0
- Verify that the indexing conventions match between systems (particularly for empty sums where the lower bound exceeds the upper bound)
- The proof structure should transfer well to most systems, as it follows standard induction on natural numbers

---

## SUM_REARRANGE_LEMMA

### Name of formal statement
SUM_REARRANGE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_REARRANGE_LEMMA = prove
 (`!a v m n.
        m <= n + 1
        ==> sum(m..n+1) (\i. a i * v i) =
            sum(m..n) (\k. sum(m..k) a * (v(k) - v(k+1))) +
            sum(m..n+1) a * v(n+1)`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; num_CONV `1`; ADD_CLAUSES] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_CASES_TAC `m = SUC(n + 1)` THENL
   [ASM_REWRITE_TAC[LE_SUC; ARITH_RULE `~(n + 1 <= n)`] THEN
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE
     `n < SUC n /\ n < SUC(n + 1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `m <= SUC n <=> m <= SUC(n + 1) /\ ~(m = SUC(n + 1))`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_RDISTRIB; REAL_EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `m <= SUC(n + 1) /\ ~(m = SUC(n + 1)) ==> m <= SUC n`] THEN
  REWRITE_TAC[REAL_ARITH
   `(s1 * (v - w) + x) + (s2 + y) * w =
    (x + y * w) + (v - w) * s1 + w * s2`] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[REAL_ADD_LDISTRIB; GSYM SUM_CMUL; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any sequences $a$ and $v$, and natural numbers $m$ and $n$ where $m \leq n + 1$, the following equality holds:

$$\sum_{i=m}^{n+1} a(i) \cdot v(i) = \sum_{k=m}^{n} \left(\sum_{i=m}^{k} a(i)\right) \cdot (v(k) - v(k+1)) + \left(\sum_{i=m}^{n+1} a(i)\right) \cdot v(n+1)$$

This is a summation rearrangement formula that expresses a weighted sum in terms of partial sums of weights and differences of values.

### Informal proof
The proof proceeds by induction on $n$.

**Base case**: When $n = 0$:
- We need to show that for $m \leq 1$:
  $$\sum_{i=m}^{1} a(i) \cdot v(i) = \sum_{k=m}^{0} \left(\sum_{i=m}^{k} a(i)\right) \cdot (v(k) - v(k+1)) + \left(\sum_{i=m}^{1} a(i)\right) \cdot v(1)$$
- Consider the cases $m = 0$ and $m = 1$:
  - If $m = 0$, we apply summation rules and algebraically verify the equality
  - If $m = 1$, we simplify the expressions and show they are equal using real arithmetic

**Inductive step**: Assume the formula holds for $n$, and prove for $n+1$:
- We need to establish the formula for $m \leq (n+1) + 1 = n+2$
- First, handle the case where $m = n+2$, which simplifies both sides to $a(n+2) \cdot v(n+2)$
- For $m < n+2$, apply the induction hypothesis for $n$
- Rewrite the formula using summation properties:
  - Split the summation from $m$ to $n+2$ at $n+1$
  - Distribute terms and rearrange using algebraic manipulations
  - Use the distributive property of multiplication over addition
  - Apply summation rules to combine terms
- After algebraic simplification, we obtain the required equality

The proof relies heavily on algebraic manipulation of summations and the properties of real arithmetic.

### Mathematical insight
This lemma provides a way to rewrite a weighted sum in terms of partial sums of weights and differences of consecutive values. It's a form of "summation by parts," which is analogous to integration by parts in calculus. 

The formula is particularly useful when analyzing sequences where the differences $v(k) - v(k+1)$ have a meaningful interpretation or are easier to work with than the original values. This transformation is valuable in various areas of mathematics including numerical analysis, probability theory, and combinatorics.

The result can be seen as a discrete analog of the formula for integration by parts, where partial sums play the role of antiderivatives and differences correspond to derivatives.

### Dependencies
No explicit dependencies were listed in the input, but the proof uses:
- `SUM_CLAUSES_NUMSEG`: Rules for breaking down summations over numeric segments
- `SUM_TRIV_NUMSEG`: Rules for handling trivial summation cases
- `SUM_CMUL`: Rule for constant multiplication in summations
- `SUM_ADD_NUMSEG`: Rule for addition of summations
- Various arithmetic and real arithmetic rules

### Porting notes
When porting this theorem:
- Ensure your target system has a well-defined notion of summation over integer ranges
- The proof heavily relies on real arithmetic simplifications, so a good automation for algebraic manipulation is required
- Pay attention to boundary cases, especially when $m = n+1$ or $m = n+2$
- Different proof assistants may require more explicit handling of the summation ranges and indices

---

## SUM_BOUNDS_LEMMA

### Name of formal statement
SUM_BOUNDS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_BOUNDS_LEMMA = prove
 (`!a v l u m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> l <= sum(m..k) a /\ sum(m..k) a <= u)
        ==> l * v(m) <= sum(m..n) (\i. a(i) * v(i)) /\
            sum(m..n) (\i. a(i) * v(i)) <= u * v(m)`,
  REPLICATE_TAC 5 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE; SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `m <= i /\ i = 0 <=> m = 0 /\ i = 0`] THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    SIMP_TAC[REAL_LE_RMUL];
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[ADD1]] THEN
  SIMP_TAC[SUM_REARRANGE_LEMMA] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..n) (\k. l * (v(k) - v(k + 1))) + l * v(n+1)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LMUL; SUM_DIFFERENCES] THEN REAL_ARITH_TAC;
      ALL_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..n) (\k. u * (v(k) - v(k + 1))) + u * v(n+1)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[SUM_LMUL; SUM_DIFFERENCES] THEN REAL_ARITH_TAC]] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[REAL_LE_RMUL; LE_REFL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_SUB_LE; ARITH_RULE `k <= n ==> k <= n + 1`]);;
```

### Informal statement
Let $a$ and $v$ be sequences, and let $l,u,m,n$ be such that $m \leq n$. If:

1. For all $i$ such that $m \leq i \leq n$, we have $0 \leq v(i)$ and $v(i+1) \leq v(i)$
2. For all $k$ such that $m \leq k \leq n$, we have $l \leq \sum_{i=m}^{k} a(i) \leq u$

Then:
$$l \cdot v(m) \leq \sum_{i=m}^{n} a(i) \cdot v(i) \leq u \cdot v(m)$$

### Informal proof
We prove this by induction on $n$, with the base case being $n = m$.

**Base case ($n = m$):**
- When $n = m$, we have $\sum_{i=m}^{n} a(i) \cdot v(i) = a(m) \cdot v(m)$
- By the assumption, $l \leq \sum_{i=m}^{m} a(i) = a(m) \leq u$
- Multiplying these inequalities by $v(m)$, which is non-negative by assumption, we get $l \cdot v(m) \leq a(m) \cdot v(m) \leq u \cdot v(m)$

**Inductive case ($n = n'+1$):**
- We need to show that $l \cdot v(m) \leq \sum_{i=m}^{n'+1} a(i) \cdot v(i) \leq u \cdot v(m)$

For the lower bound:
- We use the sum rearrangement lemma to express $\sum_{i=m}^{n} a(i) \cdot v(i) = \sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) + \sum_{i=m}^{n} a(i) \cdot v(i+1)$
- This can be rewritten as $\sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) + v(n+1) \cdot \sum_{i=m}^{n} a(i)$
- Since $l \leq \sum_{i=m}^{n} a(i)$ and $v(i) - v(i+1) \geq 0$ (as $v$ is non-increasing), we have $\sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) \geq l \cdot \sum_{i=m}^{n} (v(i) - v(i+1))$
- The sum $\sum_{i=m}^{n} (v(i) - v(i+1))$ telescopes to $v(m) - v(n+1)$
- Therefore, $\sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) \geq l \cdot (v(m) - v(n+1))$
- Adding $l \cdot v(n+1)$ to both sides, we get $\sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) + l \cdot v(n+1) \geq l \cdot v(m)$
- Since $\sum_{i=m}^{n} a(i) \geq l$, we have $v(n+1) \cdot \sum_{i=m}^{n} a(i) \geq l \cdot v(n+1)$
- Combining these inequalities gives the lower bound

For the upper bound:
- We use a similar approach, but with $\sum_{i=m}^{n} a(i) \leq u$
- This leads to $\sum_{i=m}^{n} a(i) \cdot (v(i) - v(i+1)) \leq u \cdot \sum_{i=m}^{n} (v(i) - v(i+1)) = u \cdot (v(m) - v(n+1))$
- Similarly, we get $v(n+1) \cdot \sum_{i=m}^{n} a(i) \leq u \cdot v(n+1)$
- Combining these inequalities gives the upper bound

### Mathematical insight
This theorem provides bounds for weighted sums when we have a non-increasing weight sequence and bounds on the partial sums of the original sequence. The result is particularly useful in analysis when studying weighted averages or integrals with monotone weight functions.

The key insight is that when a sequence of partial sums is bounded, and we weight those terms by a non-increasing sequence, the resulting weighted sum is bounded by the extremal values of the original sum multiplied by the largest weight.

This lemma can be viewed as a discrete analog of integration by parts, where the monotonicity of the weight function allows us to establish tight bounds on the weighted sum.

### Dependencies
#### Theorems
- `ARITH_RULE`
- `LE`
- `LE_REFL`
- `LEFT_FORALL_IMP_THM`
- `REAL_LE_ADD2`
- `REAL_LE_RMUL`
- `REAL_LE_TRANS`
- `REAL_SUB_LE`
- `RIGHT_EXISTS_AND_THM`
- `SUM_CLAUSES_NUMSEG`
- `SUM_DIFFERENCES`
- `SUM_LE_NUMSEG`
- `SUM_LMUL`
- `SUM_REARRANGE_LEMMA`
- `SUM_SING_NUMSEG`

### Porting notes
When porting this theorem:
1. Ensure that the target system has support for finite sums over ranges of integers.
2. The proof relies on sum rearrangement (telescoping sums) which should be available or may need to be proven in the target system.
3. The induction is on the upper bound of the sum, which is a common pattern, but the handling of the base case may differ between systems.
4. Pay attention to the assumptions about the decreasing sequence v(i) - these are critical to the proof and may need explicit handling in systems with different automation capabilities.

---

## SUM_BOUND_LEMMA

### SUM_BOUND_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_BOUND_LEMMA = prove
 (`!a v b m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> abs(sum(m..k) a) <= b)
        ==> abs(sum(m..n) (\i. a(i) * v(i))) <= b * abs(v m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `--b * k <= a /\ a <= b * k ==> abs(a) <= b * k`) THEN
  ASM_SIMP_TAC[LE_REFL; real_abs] THEN
  MATCH_MP_TAC SUM_BOUNDS_LEMMA THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE]);;
```

### Informal statement
For any sequences $a$, $v$, and real number $b$, if:
- $m \leq n$ (integers)
- For all $i$ such that $m \leq i \leq n$, we have $0 \leq v(i)$ and $v(i+1) \leq v(i)$ (i.e., $v$ is non-negative and non-increasing)
- For all $k$ such that $m \leq k \leq n$, we have $\left|\sum_{i=m}^{k} a(i)\right| \leq b$

Then:
$$\left|\sum_{i=m}^{n} a(i) \cdot v(i)\right| \leq b \cdot |v(m)|$$

### Informal proof
The proof proceeds by establishing upper and lower bounds, then applying properties of absolute values:

1. First, we apply the fact that if $-b \cdot k \leq a \leq b \cdot k$, then $|a| \leq b \cdot k$. 
   - This is done using `REAL_ARITH` to handle the real arithmetic.
   
2. We simplify using `ASM_SIMP_TAC[LE_REFL; real_abs]` which applies reflexivity of less-than-or-equal and properties of absolute value.

3. The main step involves applying the theorem `SUM_BOUNDS_LEMMA` which provides bounds for sums of products.

4. Finally, we use `REAL_BOUNDS_LE` to handle the bounds on real numbers, completing the proof.

### Mathematical insight
This lemma provides a bound on the absolute value of a weighted sum. Specifically, it shows that if a sequence $a$ has bounded partial sums (bounded by $b$), and if $v$ is a non-negative, non-increasing sequence, then the absolute value of the weighted sum $\sum a(i)v(i)$ is bounded by $b$ times the initial value of $v$.

This is a useful result in analysis, particularly for dealing with summation by parts or for establishing convergence criteria for certain types of series. The non-increasing property of $v$ is crucial here, as it allows us to control how the weights affect the partial sums of $a$.

### Dependencies
- `REAL_ARITH` - For real number arithmetic simplification
- `SUM_BOUNDS_LEMMA` - For establishing bounds on sums of products
- `REAL_BOUNDS_LE` - For handling bounds on real numbers
- `real_abs` - Definition or property of absolute value for real numbers

### Porting notes
When porting this theorem:
- Ensure that your target system has a well-developed real number theory with properties of absolute values.
- The theorem `SUM_BOUNDS_LEMMA` is likely a key dependency that should be ported first.
- The proof is relatively straightforward and should port easily to systems with good automation for real arithmetic.

---

## LEIBNIZ_PI

### Name of formal statement
LEIBNIZ_PI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEIBNIZ_PI = prove
 (`(\n. (-- &1) pow n / &(2 * n + 1)) sums (pi / &4)`,
  REWRITE_TAC[GSYM ATN_1] THEN
  ASSUME_TAC(MATCH_MP SUMMABLE_SUM SUMMABLE_LEIBNIZ) THEN
  ABBREV_TAC `s = suminf(\n. (-- &1) pow n / &(2 * n + 1))` THEN
  SUBGOAL_THEN `s = atn(&1)` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(x - y)) ==> x = y`) THEN
  ABBREV_TAC `e = abs(s - atn(&1))` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  REWRITE_TAC[SER_CAUCHY] THEN DISCH_THEN(MP_TAC o SPEC `e / &7`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\x. sum(0,N) (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1)))
    contl (&1)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC
     `sum(0,N) (\n. (-- &1) pow n * &1 pow (2 * n))` THEN
    MATCH_MP_TAC DIFF_SUM THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC DIFF_CMUL THEN
    MP_TAC(SPECL [`2 * k + 1`; `&1`] DIFF_POW) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&(2 * k + 1))` o MATCH_MP DIFF_CMUL) THEN
    MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN
    REWRITE_TAC[ADD_SUB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_POW_ONE] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `atn contl (&1)` MP_TAC THENL
   [MESON_TAC[DIFF_CONT; DIFF_ATN]; ALL_TAC] THEN
  REWRITE_TAC[CONTL_LIM; LIM] THEN
  REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; GSYM SUM_SUB] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NEG] THEN
  REWRITE_TAC[GSYM SUM_NEG; REAL_NEG_SUB; GSYM REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_POW_ONE; GSYM REAL_SUB_LDISTRIB] THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
                    (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `x = &1 - min (min (d1 / &2) (d2 / &2)) (&1 / &2)` THEN
  REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
          [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN `&0 < x /\ x < &1 /\ abs x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_ALT) THEN
  REWRITE_TAC[sums; SEQ] THEN DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sums]) THEN
  REWRITE_TAC[SEQ] THEN DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `N + N1 + N2:num`) THEN
         ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(sum(N,N1+N2) (\n. -- &1 pow n / &(2 * n + 1) * x pow (2 * n + 1)))
     < e / &6`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `N1 + N2 = 0` THENL
     [ASM_SIMP_TAC[sum; REAL_LT_DIV; REAL_OF_NUM_LT; REAL_ABS_NUM; ARITH];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= e / &7 /\ &0 < e ==> x < e / &6`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `e / &7 * abs(x pow (2 * N + 1))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      MAP_EVERY UNDISCH_TAC [`&0 < x`; `x < &1`] THEN REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN MATCH_MP_TAC SUM_BOUND_LEMMA THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(N1 + N2 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LT];
      REWRITE_TAC[ARITH_RULE `2 * (m + 1) + 1 = (2 * m + 1) + 2`] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_POW_ADD] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_1_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `(k - N:num) + 1`]) THEN
      SIMP_TAC[PSUM_SUM_NUMSEG; ADD_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[ARITH_RULE `N <= k ==> (N + (k - N) + 1) - 1 = k`] THEN
      REWRITE_TAC[GE; LE_REFL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `N1 + N2:num`]) THEN
  REWRITE_TAC[GE; LE_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs((slo + shi) - s) < e / &6
    ==> ~(abs(slo - s) < e / &3) ==> ~(abs(shi) < e / &7)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_LDISTRIB; SUM_SUB; REAL_MUL_RID]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(s1 - sx) < e / &6
    ==> ~(abs(sx - s) < e / &2) ==> ~(abs(s1 - s) < e / &3)`)) THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
The theorem states that the infinite series $\sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1}$ converges to $\frac{\pi}{4}$.

In mathematical notation:
$$\sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1} = \frac{\pi}{4}$$

This is known as the Leibniz series for $\pi$.

### Informal proof
The proof proceeds as follows:

- First, we rewrite $\frac{\pi}{4}$ as $\arctan(1)$ using `ATN_1`.
- We establish that the Leibniz series is summable (converges) by applying `SUMMABLE_LEIBNIZ`.
- Let $s$ be the sum of the Leibniz series: $s = \sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1}$.
- We set up a proof by contradiction, assuming that $s \neq \arctan(1)$.
- Let $e = |s - \arctan(1)|$, and we assume $e > 0$.

The core strategy involves:
1. Using the Cauchy criterion for series to establish bounds on partial sums
2. Exploiting the continuity of both the arctangent function and a truncated power series at $x = 1$
3. Considering a point $x$ slightly less than 1 where the power series converges more rapidly

For this value $x$ (chosen carefully with $0 < x < 1$), we show:
- The truncated power series approximates $\arctan(x)$ with error less than $\frac{e}{6}$
- The Leibniz series sum approximates $s$ with error less than $\frac{e}{6}$
- The contribution of the remaining terms is bounded by $\frac{e}{6}$

By combining these error bounds and applying the triangle inequality, we reach a contradiction with our initial assumption that $s \neq \arctan(1)$. Therefore, we must have $s = \arctan(1) = \frac{\pi}{4}$.

### Mathematical insight
This theorem establishes the famous Leibniz formula for π, which is one of the simplest infinite series representations for π. Though it converges very slowly (requiring about 10,000 terms to get 4 decimal places), it's historically significant and mathematically elegant.

The proof elegantly connects the arctangent function and the Leibniz series through power series expansions. It shows that the Leibniz series is exactly the power series for arctangent evaluated at x=1, which gives π/4.

This result is part of a broader family of arctangent-based series for calculating π, and it demonstrates how infinite series can be used to compute transcendental numbers.

### Dependencies
- Theorems:
  - `DIFF_ATN`: The derivative of arctangent at point x is $\frac{1}{1+x^2}$
  - `SUMMABLE_LEIBNIZ`: The alternating harmonic series is summable
  - `REAL_ATN_POWSER_ALT`: Power series expansion of arctangent
  - Various theorems about continuity, limits, and series convergence

### Porting notes
When porting this proof to other systems:
- The proof relies heavily on manipulation of real number inequalities and power series.
- The continuity and differentiation properties of arctangent are essential.
- The alternating series test (Leibniz's test) is used to establish convergence.
- Special care may be needed when dealing with the approximation arguments for continuity and power series convergence at the boundary of the convergence region.

---

