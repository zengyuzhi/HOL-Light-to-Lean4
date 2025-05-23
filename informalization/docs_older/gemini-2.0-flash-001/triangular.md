# triangular.ml

## Overview

Number of statements: 5

`triangular.ml` formalizes properties related to triangular numbers, specifically focusing on the summation of their reciprocals. It imports results from multivariate analysis and general analysis to support these developments. The file likely contains definitions related to triangular numbers and theorems about the convergence or closed-form expression for the sum of their reciprocals.


## triangle

### Name of formal statement
- triangle

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let triangle = new_definition
 `triangle n = (n * (n + 1)) DIV 2`;;
```
### Informal statement
- Define `triangle n` to be the integer division of `n * (n + 1)` by 2.

### Informal sketch
- The definition directly computes the nth triangular number, which is the sum of the first n natural numbers.
- No proof is needed, since this is definitional.

### Mathematical insight
- Triangular numbers represent the number of objects that can form an equilateral triangle.  The nth triangular number is the sum of the first n positive integers.  This definition provides a direct computational method based on the standard formula `n * (n + 1) / 2`.  Integer division (`DIV`) is used since the formula always results in an integer.

### Dependencies
- `REAL_ARCH_INV` (mentioned in the comment, indicating usage in related code, but not directly required for the definition itself)

### Porting notes (optional)
- Ensure that the target proof assistant supports integer division and that it behaves as expected (rounding down for positive numbers).
- The definition can be directly translated into most proof assistants. For example, in Lean it would be `def triangle (n : ℕ) : ℕ := (n * (n + 1)) / 2`.


---

## REAL_TRIANGLE

### Name of formal statement
REAL_TRIANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_TRIANGLE = prove
 (`&(triangle n) = (&n * (&n + &1)) / &2`,
  MATCH_MP_TAC(REAL_ARITH `&2 * x = y ==> x = y / &2`) THEN
  REWRITE_TAC[triangle; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
   [REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH] THEN CONV_TAC TAUT;
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC[ARITH]]);;
```
### Informal statement
For any natural number `n`, the real representation of the `triangle` of `n` is equal to the real representation of `n` times the real representation of `n` plus 1, divided by the real representation of 2.

### Informal sketch
The proof proceeds as follows:
-  First, rewrite using the definitions of `triangle`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_ADD`, and `REAL_OF_NUM_EQ`, to obtain the goal `&(triangle n) = (&(n * (n + 1))) / &2`. Then apply the theorem stating that if `2 * x = y` then `x = y / 2` within real arithmetic reasoning to achieve the intermediate goal of showing that `EVEN(n * (n + 1))`.
- This intermediate goal is then tackled by rewriting using the definitions of `EVEN_MULT`, `EVEN_ADD`, and applying arithmetic reasoning and tautology checking.
- Finally, the goal `EXISTS k. n * (n + 1) = 2 * k` is tackled by stripping the existential quantifier, using assumption rewriting, applying a term, and applying `DIV_MULT` along with arithmetic rewriting.

### Mathematical insight
The `REAL_TRIANGLE` theorem establishes the relationship between the natural-number definition of the triangle function i.e. the sum of numbers from 1 to `n` and a formula for directly calculating the sum, when viewed within the real numbers. It shows that exact division is possible when mapping the triangle number formula to the reals; this fact relies on `n * (n + 1)` being even, so `&(n * (n + 1)) / &2` represents the same natural number, just in the reals.

### Dependencies
- `triangle`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_EQ`
- `EVEN_MULT`
- `EVEN_ADD`
- `ARITH`
- `EVEN_EXISTS`
- `DIV_MULT`


---

## TRIANGLE_FINITE_SUM

### Name of formal statement
TRIANGLE_FINITE_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_FINITE_SUM = prove
 (`!n. sum(1..n) (\k. &1 / &(triangle k)) = &2 - &2 / (&n + &1)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_TRIANGLE; GSYM REAL_OF_NUM_SUC] THEN CONV_TAC REAL_FIELD);;
```
### Informal statement
For all natural numbers `n`, the sum from `k = 1` to `n` of `1` divided by the `k`-th triangle number is equal to `2` minus `2` divided by `n + 1`.

### Informal sketch
The theorem is proved by induction on `n`.
- The base case (`n = 0`) is handled by simplification using arithmetic.
- In the inductive step (assuming the theorem holds for `n`), we rewrite using the inductive hypothesis, the definition of `sum` (`SUM_CLAUSES_NUMSEG`) and arithmetic facts such as `1 <= SUC n`.
- The conclusion is then simplified by evaluating the expression involving real numbers and rational arithmetic (`REAL_RAT_REDUCE_CONV`), the definition of the triangle number (`REAL_TRIANGLE`) and `REAL_OF_NUM_SUC`. The remaining step consists of applying field tactics `REAL_FIELD`.

### Mathematical insight
The theorem provides a closed-form expression for the sum of the reciprocals of the first `n` triangle numbers. Triangle numbers are numbers of the form `k*(k+1)/2`. This result is a specific instance of more a general kind of summation formula for series.

### Dependencies
- Arithmetic: `ARITH_EQ`, `ARITH_RULE`
- Real Analysis: `REAL_RAT_REDUCE_CONV`, `REAL_TRIANGLE`, `REAL_OF_NUM_SUC`, `REAL_FIELD`
- Summation: `SUM_CLAUSES_NUMSEG`

### Porting notes (optional)
The proof relies on a specific set of tactics to simplify arithmetic and algebraic expressions. In other proof assistants, similar simplification tactics or decision procedures might be needed. The rewriting steps might need to be adapted based on how the definitions for sum and triangle numbers are formalized. The most difficult part could be finding an equivalent to the `REAL_FIELD` tactic.


---

## TRIANGLE_CONVERGES

### Name of formal statement
TRIANGLE_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_CONVERGES = prove
 (`!e. &0 < e
       ==> ?N. !n. n >= N
                   ==> abs(sum(1..n) (\k. &1 / &(triangle k)) - &2) < e`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N + 1` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TRIANGLE_FINITE_SUM; REAL_ARITH `abs(x - y - x) = abs y`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```
### Informal statement
For any real number `e` greater than 0, there exists a natural number `N` such that for all natural numbers `n`, if `n` is greater than or equal to `N`, then the absolute value of the difference between the sum from 1 to `n` of `1` divided by the `triangle` of `k` and `2` is less than `e`.

### Informal sketch
The proof demonstrates that the infinite sum of `1 / triangle k` (where `triangle k = k * (k + 1) / 2`) converges to `2`.

- Begin by assuming `e > 0`.
- Introduce `N` as the chosen variable (existential instantiation/introduction)
- Instantiate the goal using `2 * N + 1`.
- Simplify the goal using `TRIANGLE_FINITE_SUM` which states that the sum from 1 to `n` of `1 / triangle k` is `2n / (n + 1)`. This reduces to showing `|2n / (n + 1) - 2| < e`.
- Transform `|2n / (n + 1) - 2|` to `|2 / (n + 1)|`.
- Show that `|2 / (n + 1)| < e` by showing that `2 / (n + 1) < 1 / N`.
- Since `n >= N` it suffices to show that `2 / (N + 1) < 1 / N`.
- Rewrite `abs(&n + &1) = &n + &1` to eliminate the absolute value, since `n` is a natural number.
- Simplify further using arithmetic and the assumption `n >= N`.
- Reduce the goal to `2N <= N + 1`.
- Use arithmetic to verify this inequality.

### Mathematical insight
The theorem proves the convergence of the infinite sum of reciprocals of triangle numbers. Specifically, it demonstrates that the sum converges to 2. This is a classic result in calculus and real analysis. The proof relies on finding a suitable `N` for a given `e` to satisfy the definition of convergence. The `TRIANGLE_FINITE_SUM` theorem provides a crucial closed-form expression for the partial sums.

### Dependencies
- `REAL_ARCH_INV`
- `TRIANGLE_FINITE_SUM`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_INV_DIV`
- `REAL_LE_INV2`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`


---

## TRIANGLE_CONVERGES'

### Name of formal statement
TRIANGLE_CONVERGES'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_CONVERGES' = prove
 (`(\n. sum(1..n) (\k. &1 / &(triangle k))) --> &2`,
  REWRITE_TAC[SEQ; TRIANGLE_CONVERGES]);;
```
### Informal statement
The infinite sum of the reciprocals of the triangular numbers converges to 2. Specifically, for any natural number `n`, the sum from `k = 1` to `n` of `1` divided by the `triangle k` function, converges to 2 as `n` tends to infinity.

### Informal sketch
The proof shows that the infinite sum of the reciprocals of the triangular numbers converges to 2. The proof relies on a pre-existing theorem, `TRIANGLE_CONVERGES`, and uses rewriting with the `SEQ` tactic.

*   The theorem `TRIANGLE_CONVERGES` is assumed to provide the crux of the argument, likely giving a closed form or partial sum representation that allows the limit to be easily evaluated.
*   The `REWRITE_TAC` tactic, equipped with the `SEQ` combinator and `TRIANGLE_CONVERGES`, replaces the sum with its closed form, which presumably simplifies to the limit `2`.

### Mathematical insight
This theorem demonstrates that the apparently simple sum of reciprocals of triangular numbers converges to a particularly simple integer. It showcases a relationship between discrete mathematics (triangular numbers) and analysis (convergence of series). The result is interesting because it is not immediately obvious what the sum converges to.

### Dependencies
- Theorems: `TRIANGLE_CONVERGES`,
- Tactics: `REWRITE_TAC`, `SEQ`


---

