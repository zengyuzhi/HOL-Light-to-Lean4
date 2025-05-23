# divharmonic.ml

## Overview

Number of statements: 2

The file `divharmonic.ml` formalizes the divergence of the harmonic series. It imports `analysis.ml` and `transc.ml`, suggesting it relies on real analysis and transcendental function theory. The file likely contains definitions and theorems related to the harmonic series and its divergent behavior.


## HARMONIC_LEMMA

### Name of formal statement
HARMONIC_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HARMONIC_LEMMA = prove
 (`!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2`,
  REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; MULT_2; SUM_SING_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= 2 EXP m + 1`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a <= x ==> b - a <= y ==> b <= x + y`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM (CONJUNCT2 EXP); GSYM MULT_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; EXP; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN
    REWRITE_TAC[ARITH] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```
### Informal statement
For all natural numbers `m`, the sum from `1` to `2` to the power of `m` of the sequence where the `n`th term is `1/n` is greater than or equal to `m/2`.

### Informal sketch
The theorem is proved by induction on `m`.
- Base case: show that the sum from `1` to `2^0 = 1` of `1/n` is greater than or equal to `0/2 = 0`, which is trivially true since the sum is just `1`.
- Inductive step: Assume the statement holds for `m`, i.e., `sum(1..2^m) (\n. 1/n) >= m/2`. We need to show that `sum(1..2^(m+1)) (\n. 1/n) >= (m+1)/2`.
   - The left-hand side can be split into `sum(1..2^m) (\n. 1/n) + sum(2^m + 1..2^(m+1)) (\n. 1/n)`.
   - By the induction hypothesis, `sum(1..2^m) (\n. 1/n) >= m/2`.
   - We show that `sum(2^m + 1..2^(m+1)) (\n. 1/n) >= 1/2`. The tactic `EXISTS_TAC` introduces the term `sum(2 ^ m + 1 .. 2 EXP (SUC m)) (\n. &1 / &(2 EXP (SUC m)))`.
   - Since `n <= 2^(m+1)` for all `n` in the range `2^m + 1` to `2^(m+1)`, we have `1/n >= 1/(2^(m+1))`. Thus, `sum(2^m + 1..2^(m+1)) (\n. 1/n) >= sum(2^m + 1..2^(m+1)) (\n. 1/(2^(m+1))) = (2^(m+1) - (2^m + 1) + 1) * (1/(2^(m+1))) = (2^m) * (1/(2^(m+1))) = 1/2`.
   - Combining the two inequalities, we have `sum(1..2^(m+1)) (\n. 1/n) >= m/2 + 1/2 = (m+1)/2`, completing the inductive step.

### Mathematical insight
This lemma provides a lower bound for the partial sums of the harmonic series. It demonstrates that the partial sums grow at least linearly with respect to the logarithm (base 2) of the upper limit of the summation. This hints at the divergence of the harmonic series, as it grows without bound.

### Dependencies
- `real_ge`
- `EXP`
- `MULT_2`
- `SUM_SING_NUMSEG`
- `SUM_ADD_SPLIT`
- `REAL_OF_NUM_SUC`
- `EXP`
- `REAL_LE_TRANS`
- `SUM_CONST_NUMSEG`
- `REAL_OF_NUM_MUL`
- `EXP_EQ_0`
- `REAL_FIELD`
- `SUM_LE_NUMSEG`
- `real_div`
- `REAL_MUL_LID`
- `REAL_LE_INV2`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`

### Porting notes (optional)
The proof relies on induction and inequalities involving sums and real numbers. Care should be taken to ensure that the target proof assistant has comparable theorems and tactics for manipulating sums and inequalities. The use of `REAL_RAT_REDUCE_CONV` suggests that a facility for simplifying rational expressions over the reals is necessary.
---
### Name of formal statement
HARMONIC_DIVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HARMONIC_LEMMA = prove
 (`!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2`,
  REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; MULT_2; SUM_SING_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= 2 EXP m + 1`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a <= x ==> b - a <= y ==> b <= x + y`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM (CONJUNCT2 EXP); GSYM MULT_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; EXP; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN
    REWRITE_TAC[ARITH] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```
### Informal statement
It is not the case that there exists a real number `s` such that for all positive real numbers `e`, there exists a natural number `N` such that for all natural numbers `n`, if `N <= n`, then the absolute value of the difference between the sum from `1` to `n` of the sequence where the `i`th term is `1/i` and `s` is less than `e`.
In other words, the harmonic series does not converge.

### Informal sketch
The proof proceeds by contradiction.
- We assume the harmonic series converges to some limit `s`.
- We choose a specific `e = 1/4`. Then, by the assumed convergence, there exists an `N` such that for all `n >= N`, `|sum(1..n) (1/i) - s| < 1/4`.
- In particular, `|sum(1..(N+1)) (1/i) - s| < 1/4` and `|sum(1..(2*(N+1))) (1/i) - s| < 1/4`.
- We split the sum `sum(1..(2*(N+1))) (1/i)` into `sum(1..(N+1)) (1/i) + sum((N+1)+1..(2*(N+1))) (1/i)`.
- We then have `|(sum(1..(N+1)) (1/i) - s) + sum((N+1)+1..(2*(N+1))) (1/i)| < 1/4`. Thus, `|sum((N+1)+1..(2*(N+1))) (1/i)| >= 1/4`. `EXISTS_TAC` introduces the term  `sum((N + 1) + 1 .. 2 * (N + 1)) (\i. &1 / &(2 * (N + 1)))`.
- The sum `sum((N+1)+1..(2*(N+1))) (1/i)` contains `(2*(N+1)) - ((N+1)+1) + 1 = N+1` terms. Since `i <= 2*(N+1)` in the range of summation, `1/i >= 1/(2*(N+1))`.  Therefore, `sum((N+1)+1..(2*(N+1))) (1/i) >= (N+1)*(1/(2*(N+1))) = 1/2`.
- Therefore, `1/2 <= sum((N+1)+1..(2*(N+1))) (1/i) = (sum(1..(2*(N+1)))(1/i)) - (sum(1..(N+1))(1/i))`. Rearranging and taking absolute value, it implies `|sum(1..(2*(N+1)))(1/i) - s| >= |1/2 -|sum(1..(N+1))(1/i) - s||`. The assumption `|sum(1..(N+1))(1/i) - s|<1/4` makes this term greater than `(1/2)-(1/4)=1/4`
- This contradicts the assumption that `|sum(1..(2*(N+1))) (1/i) - s| < 1/4`.

### Mathematical insight
This theorem demonstrates a fundamental property of the harmonic series: it diverges. It refutes the notion that the sum of reciprocals of natural numbers converges to a finite limit. The proof exploits the fact that even though the individual terms `1/n` tend to zero, they do so slowly enough that their sum grows without bound.

### Dependencies
- `LE_ADD`
- `REAL_ARITH`
- `MULT_2`
- `SUM_CONST_NUMSEG`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_ADD`
- `REAL_POS`
- `REAL_FIELD`
- `SUM_LE_NUMSEG`
- `real_div`
- `REAL_MUL_LID`
- `REAL_LE_INV2`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`

### Porting notes (optional)
This proof relies heavily on the manipulation of inequalities and sums, as well as the properties of absolute values. The `REAL_ARITH` tactic is used to perform arithmetic reasoning on real numbers. The porting effort should focus on replicating these capabilities in the target proof assistant.

---
### Name of formal statement
HARMONIC_DIVERGES'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HARMONIC_LEMMA = prove
 (`!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2`,
  REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; MULT_2; SUM_SING_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= 2 EXP m + 1`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a <= x ==> b - a <= y ==> b <= x + y`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM (CONJUNCT2 EXP); GSYM MULT_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; EXP; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN
    REWRITE_TAC[ARITH] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```
### Informal statement
It is not the case that the sequence defined by the partial sums of the harmonic series (i.e., the sequence whose `n`th term is the sum from `1` to `n` of `1/i`) is convergent.

### Informal sketch
The proof is a direct consequence of the theorem `HARMONIC_DIVERGES`. It uses the definition of convergence which is present in `convergent` and the definition of sequence `SEQ`. Rewrite the theorem, using `convergent`, `SEQ`, `GE` and `HARMONIC_DIVERGES` performs the proof automatically.

### Mathematical insight
This theorem rephrases the divergence of the harmonic series in terms of the convergence of the sequence of its partial sums. It states that this sequence does not approach a finite limit as `n` tends to infinity. It is simply a restatement of `HARMONIC_DIVERGES` using definitions from the `analysis.ml` library.

### Dependencies
- `convergent`
- `SEQ`
- `GE`
- `HARMONIC_DIVERGES`
- requires `"Library/analysis.ml"`


---

## LOG_BOUND

### Name of formal statement
LOG_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LOG_BOUND = prove
 (`&0 < x /\ x < &1 ==> ln(&1 + x) >= x / &2`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LN_EXP] THEN
  ASM_SIMP_TAC[LN_MONO_LE; REAL_EXP_POS_LT; REAL_LT_ADD; REAL_LT_01] THEN
  MP_TAC(SPEC `x / &2` REAL_EXP_BOUND_LEMMA) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
If `0 < x` and `x < 1`, then `ln(1 + x) >= x / 2`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the goal using the definition of the real "greater than or equal to" relation (`real_ge`).
- Strip the implication and separate the assumptions.
- Rewrite using the property that `ln(exp(x)) = x`.
- Simplify using assumptions such as the monotonicity of `ln` (`LN_MONO_LE`), the positivity of the exponential function (`REAL_EXP_POS_LT`), the transitivity of `<` (`REAL_LT_ADD`) and `0 < 1` (`REAL_LT_01`).
- Apply a specialization of `REAL_EXP_BOUND_LEMMA` i.e. `exp(x) <= 1 + x + x^2`, to `x / 2`.
- Combine assumptions using conjunction (`CONJ`).
- Use arithmetic to conclude.

### Mathematical insight
This theorem provides a lower bound for the natural logarithm of `1 + x` when `x` is between 0 and 1. Specifically, it states that `ln(1 + x)` is greater than or equal to `x / 2` in this interval. This inequality is useful in analysis for estimating the behavior of the logarithm function and can be used in convergence proofs or when bounding other expressions.

### Dependencies
- Theorems:
  - `real_ge`
  - `LN_EXP`
  - `LN_MONO_LE`
  - `REAL_EXP_POS_LT`
  - `REAL_LT_ADD`
  - `REAL_LT_01`
  - `REAL_EXP_BOUND_LEMMA`

### Porting notes (optional)
The main challenge in porting this theorem would be ensuring that the real number library in the target proof assistant has similar lemmas about the exponential and logarithmic functions like `LN_MONO_LE`, `REAL_EXP_POS_LT`, and `REAL_EXP_BOUND_LEMMA`. The automatic arithmetic tactic `ARITH_TAC` might need to be replaced with a comparable tactic or a manual proof using basic arithmetic lemmas.


---

