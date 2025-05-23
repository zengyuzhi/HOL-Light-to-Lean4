# stirling.ml

## Overview

Number of statements: 32

`stirling.ml` formalizes Stirling's approximation, a fundamental result in mathematical analysis. The file, importing `analysis.ml` and `transc.ml`, likely contains the definition of relevant functions and proves theorems related to the asymptotic behavior of the factorial function. This likely culminates in a formal statement and proof of Stirling's formula.


## ODDEVEN_INDUCT

### Name of formal statement
ODDEVEN_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODDEVEN_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;
```

### Informal statement
For any predicate `P` over natural numbers, if `P` holds for 0, `P` holds for 1, and for all natural numbers `n`, if `P` holds for `n`, then `P` holds for `n + 2`, then `P` holds for all natural numbers `n`.

### Informal sketch
The proof proceeds by induction.
- First, the goal `!n. P n` is strengthened to `!n. P n /\ P(n+1)`. `MESON_TAC` will prove the original goal from the strengthened one.
- Then, induction is performed on the strengthened goal i.e. `!n. P n /\ P(n+1)`.
    - Base case: Prove `P 0 /\ P 1`, which is given in the assumptions.
    - Inductive step: Assume `P n /\ P (n+1)` and show `P (n+1) /\ P (n+2)`. This is shown by using the assumption `!n. P n ==> P (n+2)` using `ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC]` to rewrite `P (n+1)` to `P (n+1)` and `P (n+2)` to `P (n+2)` and using `ARITH` to discharge the arithmetic assumptions.

### Mathematical insight
This theorem provides an alternative induction principle for the natural numbers. Instead of the usual induction that proceeds from `n` to `n+1`, it inducts from `n` to `n+2`. This is useful when the property `P` relates values that are two apart. The base case requires proving `P` for both 0 and 1.
This is a convenient induction scheme for proofs by induction involving odd and even numbers.

### Dependencies
- `ADD1`
- `ADD_ASSOC` (used in its symmetric form via `GSYM`)
- `ARITH`


---

## LN_LIM_BOUND

### Name of formal statement
LN_LIM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_LIM_BOUND = prove
 (`!n. ~(n = 0) ==> abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&1 / &n`; `2`] MCLAURIN_LN_POS) THEN
  ASM_SIMP_TAC[SUM_2; REAL_LT_DIV; REAL_OF_NUM_LT; LT_NZ; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_POW_1; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
              REAL_NEG_NEG; REAL_MUL_LID; REAL_INV_1; REAL_POW_NEG;
              REAL_POW_ONE; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(x = &0) ==> x * (inv(x) + a) - &1 = x * a`] THEN
  REWRITE_TAC[REAL_ARITH `n * --((i * i) * a) = --((n * i) * a * i)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL] THEN
  ONCE_REWRITE_TAC[REAL_INV_MUL] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then the absolute value of (`n` times the natural logarithm of (`1` plus `1` divided by `n`)) minus `1` is less than or equal to `1` divided by (`2` times `n`).

### Informal sketch
The proof demonstrates the inequality `abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)` for nonzero natural numbers `n`.

- First, the proof uses the McLaurin series expansion of `ln(1+x)` for a positive real number `x`.
- Then, the absolute value inequality is simplified using several real arithmetic rules (`SUM_2`, `REAL_LT_DIV`, `REAL_OF_NUM_LT`, `LT_NZ`, `ARITH`).
- An assumption is discharged and rewritten.
- Several rewriting steps occur to eliminate terms and reduce the expression including: `real_div`, `REAL_INV_0`, `REAL_MUL_RZERO`, `REAL_ADD_LID`, `REAL_POW_1`, `REAL_POW_2`, `REAL_MUL_LNEG`, `REAL_MUL_RNEG`, `REAL_NEG_NEG`, `REAL_MUL_LID`, `REAL_INV_1`, `REAL_POW_NEG`, `REAL_POW_ONE`, `ARITH`, `REAL_MUL_RID`.
- The goal is further simplified by using field arithmetic (`REAL_FIELD`) and other real arithmetic rules.
- Absolute values are handled by first rewriting under negation and multiplication.
- The expression is reduced using `REAL_RAT_REDUCE_CONV` and the associativity of multiplication.
- Finally inequalities are built up using transitivity and positivity until the desired result is achieved.

### Mathematical insight
This theorem establishes a bound on the rate at which `n * ln(1 + 1/n)` converges to 1 as `n` tends to infinity. It provides a quantitative estimate of the difference between `n * ln(1 + 1/n)` and its limit, 1. This result is useful in various contexts, such as numerical analysis or when reasoning about the asymptotic behavior of functions involving logarithms.

### Dependencies
Real Analysis:
- `MCLAURIN_LN_POS`
- `SUM_2`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `LT_NZ`
- `ARITH`
- `real_div`
- `REAL_INV_0`
- `REAL_MUL_RZERO`
- `REAL_ADD_LID`
- `REAL_POW_1`
- `REAL_POW_2`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_MUL_LID`
- `REAL_INV_1`
- `REAL_POW_NEG`
- `REAL_POW_ONE`
- `REAL_ARITH`
- `REAL_FIELD`
- `REAL_MUL_RINV`
- `REAL_ABS_NEG`
- `REAL_ABS_MUL`
- `REAL_INV_MUL`
- `REAL_RAT_REDUCE_CONV`
- `REAL_MUL_ASSOC`
- `REAL_LE_LMUL`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `REAL_ABS_INV`
- `REAL_INV_LE_1`
- `REAL_LE_MUL2`
- `REAL_OF_NUM_EQ`


---

## LN_LIM_LEMMA

### Name of formal statement
LN_LIM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_LIM_LEMMA = prove
 (`(\n. &n * ln(&1 + &1 / &n)) --> &1`,
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [REAL_ARITH `a = (a - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[ARITH_RULE `n >= 1 <=> ~(n = 0)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 / (&2 * &n)` THEN ASM_SIMP_TAC[LN_LIM_BOUND] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC);;
```

### Informal statement
The limit, as `n` tends to infinity, of the sequence whose `n`-th term is `&n * ln(&1 + &1 / &n)` is `&1`.

### Informal sketch
*   The proof shows that `lim_{n -> infinity} &n * ln(&1 + &1 / &n) = 1`.
*   The proof starts with rewriting `&1` to `(a - &1) + &1`.
*   Then it uses `REAL_ADD_LID` to transform the goal so we can use the sequence lemma `SEQ_ADD`.
*   Apply `SEQ_ADD` and `SEQ_CONST` to split limit into `(&n * ln(&1 + &1 / &n)) - &1` and `&1` respectively.
*   Apply `SEQ_LE_0`.
*   Existentially quantify `\n. &1 / &n` and apply `SEQ_HARMONIC`.
*    Existentially quantify `1`.
*   Rewrite `n >= 1 <=> ~(n = 0)`.
*   Then universally quantify an epsilon `e` and assume `e > 0`.
*   Apply the transitivity of `<=` given by `REAL_LE_TRANS`.
*   Existentially quantify `&1 / (&2 * &n)`.
*   Apply `LN_LIM_BOUND` and rewrite rules `real_div`, `REAL_MUL_LID`, `REAL_ABS_INV`, `REAL_LE_INV2`.
*   Discharge `~(n = 0)`.
*   Rewrite using `REAL_OF_NUM_EQ` and apply real arithmetics.

### Mathematical insight
This theorem establishes a fundamental limit involving the natural logarithm and real numbers. It connects the discrete world of natural numbers (`n`) to the continuous world of real numbers, demonstrating how the expression `&n * ln(&1 + &1 / &n)` approaches 1 as `n` becomes infinitely large. This result can be used in various contexts, such as approximating the natural logarithm and analyzing the asymptotic behavior of functions.

### Dependencies
**Theorems/Lemmas:**

*   `REAL_ARITH`
*   `SEQ_ADD`
*   `SEQ_CONST`
*   `SEQ_LE_0`
*   `SEQ_HARMONIC`
*   `ARITH_RULE`
*   `REAL_LE_TRANS`
*   `LN_LIM_BOUND`
*   `real_div`
*   `REAL_MUL_LID`
*   `REAL_ABS_INV`
*   `REAL_LE_INV2`
*   `REAL_OF_NUM_EQ`

**Tactics:**

*   `GEN_REWRITE_TAC`
*   `LAND_CONV`
*   `BINDER_CONV`
*   `GSYM`
*   `RAND_CONV`
*   `MATCH_MP_TAC`
*   `REWRITE_TAC`
*   `EXISTS_TAC`
*   `REPEAT`
*   `STRIP_TAC`
*   `ASM_SIMP_TAC`
*   `UNDISCH_TAC`
*   `REAL_ARITH_TAC`

### Porting notes (optional)
*   The proof relies heavily on rewriting and arithmetic simplification, so a proof assistant with strong automation in these areas will be beneficial.
*   The `LN_LIM_BOUND` lemma is critical. Make sure a similar bound is either available or can be proven.
*   The tactic `UNDISCH_TAC` relates to discharging assumptions which may require careful consideration regarding the handling of assumptions in other proof assistants.


---

## POSITIVE_DIFF_LEMMA

### Name of formal statement
POSITIVE_DIFF_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POSITIVE_DIFF_LEMMA = prove
 (`!f f'. (!x. &0 < x ==> (f diffl f'(x)) x /\ f'(x) < &0) /\
          (\n. f(&n)) --> &0
          ==> !n. ~(n = 0) ==> &0 < f(&n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m p. n <= m /\ m < p ==> (f:real->real)(&p) < f(&m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `&m`; `&p`] MVT_ALT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LTE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < z * --y ==> z * y + a < a`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `f(&(n + 1)) < &0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + 1`]) THEN ANTS_TAC THENL
     [ARITH_TAC; UNDISCH_TAC `f(&n) <= &0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SEQ]) THEN
  DISCH_THEN(MP_TAC o SPEC `--f(&(n + 1))`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `&0 < --x <=> x < &0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (MP_TAC o SPEC `n + p + 2`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < &0 /\ z < y ==> abs(z) < --y ==> F`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;
```

### Informal statement
If for all `x`, if `0 < x` implies `f` is differentiable at `x` with derivative `f'(x)` and `f'(x) < 0`, and the limit of `f(n)` as `n` goes to infinity is `0`, then for all `n`, if `n` is not equal to `0`, then `0 < f(n)`.

### Informal sketch
The proof proceeds as follows:
- Assume that for all `x`, if `0 < x` then `f` is differentiable at `x` with derivative `f'(x)` and `f'(x) < 0`. Also, assume that the limit of `f(n)` as `n` tends to infinity is `0`.
- We aim to show that for all `n`, if `n` is not equal to `0`, then `0 < f(n)`.
- We introduce the subgoal `!m p. n <= m /\ m < p ==> f(p) < f(m)` and prove it.
  - Applying Mean Value Theorem (`MVT_ALT`) on the interval `[m, p]` gives `f(p) - f(m) = f'(c) * (p - m)` for some `c` in `(m, p)`.
  - Since `f'(c) < 0` and `p > m`, `f'(c) * (p - m) < 0`.
  - Thus, `f(p) - f(m) < 0`, which means `f(p) < f(m)`.
- We introduce the subgoal `f(n + 1) < 0` and prove it.
  - We have `f(n) <= 0` (since the limit of `f(n)` is `0`).
  - Then by contradiction, we can show that `f(n+1) < 0`
- Having `f(n + 1) < 0`, choose `p` such that `f(n + p + 2) < f(n + 1)`.
- We arrive at a contradiction by showing `abs(f(n + p + 2)) < -f(n + 1)` and also `!(abs(f(n + p + 2)) < -f(n + 1))`.

### Mathematical insight
The theorem states that if a function `f` has a negative derivative for positive `x`, and if the limit of `f(n)` goes to zero as `n` goes to infinity, then `f(n)` must be positive for all non-zero `n`. The idea is to leverage the decreasing nature of `f` (due to the negative derivative) along with the limit behavior to establish a lower bound for `f(n)`.

### Dependencies
- `MVT_ALT`
- `LT_NZ`
- `LTE_TRANS`
- `REAL_OF_NUM_LT`
- `REAL_LTE_TRANS`
- `REAL_EQ_SUB_RADD`
- `REAL_ARITH`
- `REAL_LT_MUL`
- `REAL_SUB_LT`
- `REAL_SUB_RZERO`

### Porting notes (optional)
The proof utilizes `ARITH_TAC` and `REAL_ARITH_TAC` heavily, requiring corresponding arithmetic decision procedures in other proof assistants. The use of `MVT_ALT` (Mean Value Theorem) will also require a port of real analysis theorems. Ensure the target system has similar mechanisms for handling real number arithmetic, limits, and differentiation. Specifically, ensure that the Mean Value Theorem is adapted to the right types and definitions in your target proof assistant.


---

## stirling

### Name of formal statement
- stirling

### Type of the formal statement
- new_definition

### Formal Content
- ```ocaml
let stirling = new_definition
 `stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)`;;
```
### Informal statement
- The function `stirling` applied to `n` is defined to be the natural logarithm of the factorial of `n` minus (`n` plus one-half) times the natural logarithm of `n` minus `n`.

### Informal sketch
- The definition introduces the function `stirling`, which approximates the natural logarithm of the factorial function. The definition directly expresses the formula: `stirling n = ln(FACT n) - ((n + 1/2) * ln(n) - n)`.

### Mathematical insight
- The `stirling` definition represents an approximation of `ln(n!)` which is closely related to Stirling's approximation.  The approximation is given by `ln(n!) ≈ (n + 1/2)ln(n) - n`. This definition isolates the difference between the exact value and the approximation, which can be useful in subsequent analysis of the Stirling formula's accuracy.

### Dependencies
- `FACT` (factorial function)
- `ln` (natural logarithm)


---

## STIRLING_DIFF

### Name of formal statement
STIRLING_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DIFF = prove
 (`!n. ~(n = 0)
       ==> stirling(n) - stirling(n + 1) =
           (&n + &1 / &2) * ln((&n + &1) / &n) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stirling] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(f' - f) + x = (nl' - nl) /\ n' = n + &1
    ==> (f - (nl - n)) - (f' - (nl' - n')) = x - &1`) THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REWRITE_RULE[ADD1] FACT; GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[LN_MUL; FACT_LT; ADD_EQ_0; ARITH; LT_NZ; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[LN_DIV; REAL_OF_NUM_LT; ADD_EQ_0; ARITH; LT_NZ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then `stirling(n) - stirling(n + 1)` is equal to `(&n + &1 / &2) * ln((&n + &1) / &n) - &1`.

### Informal sketch
The proof proceeds as follows:
- First, strip the goal.
- Then, rewrite with the definition of `stirling`.
- Next, apply an arithmetic fact: `(f' - f) + x = (nl' - nl) /\ n' = n + &1 ==> (f - (nl - n)) - (f' - (nl' - n')) = x - &1`.
- Rewrite using `REAL_OF_NUM_ADD`.
- Rewrite using `REWRITE_RULE[ADD1] FACT` and `GSYM REAL_OF_NUM_MUL`.
- Simplify using `LN_MUL`, `FACT_LT`, `ADD_EQ_0`, `ARITH`, `LT_NZ`, `REAL_OF_NUM_LT`.
- Perform assumption simplification using `LN_DIV`, `REAL_OF_NUM_LT`, `ADD_EQ_0`, `ARITH`, `LT_NZ`.
- Rewrite using `GSYM REAL_OF_NUM_ADD`.
- Finally, use real arithmetic to complete the proof.

### Mathematical insight
This theorem expresses the difference between consecutive values of the `stirling` function. The right-hand side provides a closed-form expression for this difference, involving the natural logarithm. This is significant because it allows calculating the rate of decay of the Stirling approximation.

### Dependencies
- Definitions: `stirling`
- Theorems: `LN_MUL`, `FACT_LT`, `ADD_EQ_0`, `ARITH`, `LT_NZ`, `REAL_OF_NUM_LT`, `LN_DIV`, `REAL_OF_NUM_ADD`, `ADD1`, `FACT`


---

## STIRLING_DELTA_DERIV

### Name of formal statement
STIRLING_DELTA_DERIV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DELTA_DERIV = prove
 (`!x. &0 < x
       ==> ((\x. ln ((x + &1) / x) - &1 / (x + &1 / &2)) diffl
            (-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2))) x`,
  GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all real numbers `x`, if `0 < x`, then the derivative of the function `λx. ln((x + 1) / x) - 1 / (x + 1/2)` at `x` is equal to `-1 / (x * (x + 1) * (2 * x + 1)^2)`.

### Informal sketch
The proof proceeds as follows:
- Assume `0 < x`.
- Apply the differentiation conversion `DIFF_CONV` to the left-hand side of the derivative (i.e., `ln((x + 1) / x) - 1 / (x + 1/2)`), and use it to rewrite the goal.
- Rewrite using the implication `A ==> A`.
- Split the antecedent (`0 < x`) into smaller parts, and use `REAL_LT_DIV` where applicable to prove the real field side conditions
- Apply the equality implication.
- Apply theorems to arguments and terms
- Rewrite using `REAL_POW_2` to expand `pow 2`.
- Use real field tactics to simplify and finish the proof.

### Mathematical insight
This theorem provides an explicit formula for the derivative of a specific function, which is related to approximations of the Stirling formula. The function `λx. ln((x + 1) / x) - 1 / (x + 1/2)` is related to error bounds in approximations of the log-gamma function or related expressions used within Stirling's approximation.

### Dependencies
None

### Porting notes (optional)
The main challenge in porting this theorem lies in the differentiation tactic. Ensure that differentiation rules for real numbers and logarithms are correctly defined and applied. The `REAL_FIELD` tactic in HOL Light handles algebraic simplification in the real field. If the target proof assistant lacks such a tactic, the simplification steps must be performed manually.


---

## STIRLING_DELTA_LIMIT

### Name of formal statement
STIRLING_DELTA_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DELTA_LIMIT = prove
 (`(\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)) --> &0`,
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SEQ_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SEQ_LE_0 THEN
  EXISTS_TAC `\n. &1 / &n` THEN REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE; GSYM REAL_OF_NUM_LE] THEN
  DISCH_TAC THEN MATCH_MP_TAC
   (REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`)
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC LN_POS THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_FIELD `&1 <= x ==> (x + &1) / x = &1 + &1 / x`] THEN
    MATCH_MP_TAC LN_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
    MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;
```

### Informal statement
For the sequence defined by `\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)`, this sequence converges to `&0` as `n` tends to infinity.

### Informal sketch
The proof demonstrates that the limit of the given sequence as `n` approaches infinity is 0.

*   First, the goal is rewritten to show convergence to `&0` based on the absolute value of the difference being less than epsilon.
*   The proof proceeds by showing that for an arbitrary `n`, the absolute value of `ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)` is bounded by `&1/n`.
*   It is shown that `ln((&n + &1)/&n)` is positive using `LN_POS` and that `n >= 1`, together with other real arithmetic facts.
*   The proof continues by bounding `ln((&n + &1)/&n)` by `&1/n` by applying `LN_LE` and some real arithmetic.
*   Finally, it's shown that `&1 / (&n + &1/&2)` is positive and less than or equal to `&1/n` using `REAL_LE_DIV` and some arithmetic.
*   Finally, the convergence to `&0` can be concluded.

### Mathematical insight
This theorem establishes a limit result that can be used to approximate harmonic numbers and analyze the error terms in Stirling's approximation. Specifically, it relates the difference between `ln((n+1)/n)` and `1/(n + 1/2)` to `1/n` as n grows large. This is a core result for refining estimates of `ln(n!)` and other related quantities.

### Dependencies
*   `GSYM`
*   `REAL_SUB_RZERO`
*   `SEQ_SUB`
*   `SEQ_LE_0`
*   `SEQ_HARMONIC`
*   `GE`
*   `REAL_OF_NUM_LE`
*    `REAL_ARITH` with `&0 <= x /\ x <= y ==> abs x <= abs y`
*   `LN_POS`
*   `REAL_LE_RDIV_EQ`
*   `REAL_ARITH` with `&1 <= x ==> &0 < x`
*   `REAL_FIELD` with `&1 <= x ==> (x + &1) / x = &1 + &1 / x`
*   `LN_LE`
*   `REAL_LE_DIV`
*   `REAL_POS`
*   `real_div`
*   `REAL_MUL_LID`
*   `REAL_LE_INV2`


---

## STIRLING_DECREASES

### Name of formal statement
STIRLING_DECREASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DECREASES = prove
 (`!n. ~(n = 0) ==> stirling(n + 1) < stirling(n)`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN SIMP_TAC[STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. -- &1 / (x * (x + &1) * (&2 * x + &1) pow 2)` THEN
  SIMP_TAC[STIRLING_DELTA_DERIV; STIRLING_DELTA_LIMIT] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then `stirling(n + 1)` is less than `stirling(n)`, where `stirling` is the real-valued function that extends the factorial function.

### Informal sketch
The proof establishes that the continuous extension of the factorial function, `stirling`, decreases for `n > 0`.
- The proof begins by rewriting the inequality `stirling(n + 1) < stirling(n)` using the difference `stirling(n + 1) - stirling(n) < 0`.
- The core of the proof involves simplifying the difference `stirling(n + 1) - stirling(n)` using `STIRLING_DIFF`. This reduces the problem to showing that `real_of_num n < sqrt(2 * pi * real_of_num n) * ((real_of_num n + 1) / real_of_num n) pow (n + 1 / 2) * exp(-1)`.
- Further simplification using real arithmetic transforms the goal and divides by `real_of_num n`
- It is shown that the above expression is always negative for `n > 0` by using `POSITIVE_DIFF_LEMMA` to introduce an `x` such that `-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2)` is positive. This relies on `STIRLING_DELTA_DERIV` and `STIRLING_DELTA_LIMIT`.
- The proof introduces a real number `x` and discharges the assumption that `x:real`.
- The goal is then reduced to showing a series of inequalities through rewriting with real arithmetic and properties of exponentiation.
- Finally, real arithmetic is applied to discharge the assumptions and complete the proof.

### Mathematical insight
This theorem `STIRLING_DECREASES` demonstrates that the continuous extension of the factorial function, represented by the `stirling` function, decreases as its argument increases from 0 to some point, after which it begins to increase. This behavior reflects the properties of the Gamma function, which exhibits a minimum value. This behaviour is also important within the more general development of `stirling` as it ensures that `stirling` does not tend towards negative infinity for small values.

### Dependencies
- `GSYM REAL_SUB_LT`
- `STIRLING_DIFF`
- `REAL_SUB_LT`
- `REAL_MUL_SYM`
- `GSYM REAL_LT_LDIV_EQ`
- `REAL_ARITH &0 < &n + &1 / &2`
- `POSITIVE_DIFF_LEMMA`
- `STIRLING_DELTA_DERIV`
- `STIRLING_DELTA_LIMIT`
- `real_div`
- `REAL_MUL_LNEG`
- `REAL_MUL_LID`
- `REAL_ARITH --x < &0 <=> &0 < x`
- `REAL_LT_INV_EQ`
- `REAL_POW_2`
- `REAL_LT_MUL`

### Porting notes (optional)
- The proof relies heavily on real number arithmetic and properties of exponentiation. Ensure that the target proof assistant has adequate support for these mathematical domains.
- Particular attention needs to be given to how the target proof assistant handles the continuous extension of the factorial function or the Gamma function. The definition of `stirling` and related lemmas (`STIRLING_DIFF`, `STIRLING_DELTA_DERIV`, `STIRLING_DELTA_LIMIT`) must be accurately ported.


---

## OTHER_DERIV_LEMMA

### Name of formal statement
OTHER_DERIV_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OTHER_DERIV_LEMMA = prove
 (`!x. &0 < x
       ==> ((\x. &1 / (&12 * x * (x + &1) * (x + &1 / &2))) diffl
            --(&3 * x pow 2 + &3 * x + &1 / &2) /
              (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)) x`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all real numbers `x`, if `0 < x`, then the derivative of the function `f(x) = 1 / (12 * x * (x + 1) * (x + 1/2))` is equal to `- (3 * x^2 + 3 * x + 1/2) / (12 * (x * (x + 1) * (x + 1/2))^2)`.

### Informal sketch
The proof proceeds as follows:
- Strip the goal and repeatedly apply assumptions.
- Apply differentiation rules using `DIFF_CONV` to compute the derivative of the given function `f(x)`.
- Rewrite the implication `p ==> q` as `~p \/ q`.
- Discharge assumptions regarding the real numbers using `ANTS_TAC`.
 - Prove that `x` is a real number and is not equal to zero. This is done via `REAL_ENTIRE` and `ARITH_TAC`.
- Apply theorems related to the equality of implications.
- Apply theorems to `AP_THM_TAC` and `AP_TERM_TAC`.
- Rewrite using `REAL_POW_2` to expand the `pow 2` term.
- Apply the `REAL_FIELD` conversion to simplify the resulting expression using real field arithmetic.

### Mathematical insight
This theorem calculates the derivative for a specific rational function. It's a standard calculus exercise, but formalized for rigorous verification. The result is important when proving properties about the behaviour of this function, such as monotonicity or concavity, particularly when combined with inequalities.

### Dependencies
- `DIFF_CONV`
- `REAL_ENTIRE`
- `REAL_POW_2`
- `REAL_FIELD`
- `ARITH_TAC`

### Porting notes (optional)
- The tactic `CONV_TAC REAL_FIELD` relies on HOL Light's built-in rewriting for real fields. This may need to be adapted in other provers, possibly using automated simplification tactics for polynomial rings and rational functions.
- `DIFF_CONV` is a conversion for calculating derivatives automatically. Porting this will require either implementing a similar conversion or manually applying differentiation rules.


---

## STIRLING_INCREASES

### Name of formal statement
STIRLING_INCREASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_INCREASES = prove
 (`!n. ~(n = 0)
       ==> stirling(n + 1) - &1 / (&12 * (&(n + 1)))
           > stirling(n) - &1 / (&12 * &n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a - b > c - d <=> c - a < d - b`] THEN
  SIMP_TAC[REAL_FIELD
    `~(&n = &0) ==> &1 / (&12 * &n) - &1 / (&12 * (&n + &1)) =
                    &1 / (&12 * &n * (&n + &1))`] THEN
  SIMP_TAC[REAL_OF_NUM_EQ; STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_ARITH `a * b - &1 < c <=> b * a < c + &1`] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 / x + &1) / y = &1 / x / y + &1 / y`] THEN
  REWRITE_TAC[REAL_ARITH `a < b + c <=> &0 < b - (a - c)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. &1 / (x * (x + &1) * (&2 * x + &1) pow 2) -
                  (&3 * x pow 2 + &3 * x + &1 / &2) /
                  (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[STIRLING_DELTA_LIMIT] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_FIELD
     `inv(&12) * x * y * inv(&n + inv(&2)) = x * y * inv(&12 * &n + &6)`] THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(REAL_RAT_REDUCE_CONV `&0 * &0 * &0`)] THEN
    REPEAT(MATCH_MP_TAC SEQ_MUL THEN CONJ_TAC) THEN
    MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUBSEQ) THENL
     [DISCH_THEN(MP_TAC o SPECL [`1`; `1`]);
      DISCH_THEN(MP_TAC o SPECL [`12`; `6`])] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; ARITH; MULT_CLAUSES]] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
     [REAL_ARITH `&1 / x - y / z = --y / z - -- &1 / x`] THEN
    MATCH_MP_TAC DIFF_SUB THEN
    ASM_SIMP_TAC[STIRLING_DELTA_DERIV; OTHER_DERIV_LEMMA];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a - b < &0 <=> a < b`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_FIELD
   `&0 < x
    ==> &1 / (x * (x + &1) * (&2 * x + &1) pow 2) =
        (&3 * x * (x + &1)) /
        (&12 * (x * (x + &1) * (x + &1 / &2)) *
               (x * (x + &1) * (x + &1 / &2)))`] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to `0`, then `stirling(n + 1) - 1 / (12 * (n + 1))` is greater than `stirling(n) - 1 / (12 * n)`.

### Informal sketch
The proof demonstrates that the Stirling approximation improves as `n` increases.
- The proof begins by rewriting the goal using arithmetic simplification (`REAL_ARITH`) to rearrange the inequality.
- Simplification using `REAL_FIELD` rewrites the difference of reciprocals.
- The `STIRLING_DIFF` theorem is then applied, and further arithmetic simplifications are performed.
- Lemmas involving inequalities and division are used to simplify the goal into a form suitable for analysis.
- An `EXISTS_TAC` introduces a real-valued function `x` to proceed with the proof.
- The goal is split into two subgoals using `CONJ_TAC`, focusing on proving that the difference of two expressions is greater than zero.
- The first subgoal involves showing that `stirling(n)` approaches its limit, which requires using `STIRLING_DELTA_LIMIT`, properties of real division (`real_div`), and algebraic manipulations involving reciprocals. Theorems related to subsequences (`SEQ_SUB`, `SEQ_HARMONIC`, `SEQ_SUBSEQ`) handle the limit argument.
- The second subgoal is handled using a series of automated tactics and rewriting steps.
- The function `x` defined previously is manipulated, with derivatives and algebraic manipulation.
- The proof concludes with a series of inequalities and arithmetic reasoning using lemmas such as `REAL_LT_INV_EQ`, `REAL_LT_MUL` to complete the proof.

### Mathematical insight
This theorem establishes that the difference between the `stirling` function (likely representing a term in the Stirling's series) and a correction term decreases as `n` increases. This means that the Stirling approximation becomes a better estimate for large `n`.

### Dependencies
- `GSYM REAL_OF_NUM_EQ`
- `GSYM REAL_OF_NUM_ADD`
- `REAL_ARITH`
- `REAL_FIELD`
- `REAL_OF_NUM_EQ`
- `STIRLING_DIFF`
- `GSYM REAL_LT_RDIV_EQ`
- `real_div`
- `GSYM REAL_MUL_ASSOC`
- `GSYM REAL_INV_MUL`
- `POSITIVE_DIFF_LEMMA`
- `GSYM REAL_SUB_RZERO`
- `SEQ_SUB`
- `STIRLING_DELTA_LIMIT`
- `REAL_INV_MUL`
- `REAL_MUL_LID`
- `SYM(REAL_RAT_REDUCE_CONV `&0 * &0 * &0`)`
- `SEQ_MUL`
- `SPEC`
- `SEQ_HARMONIC`
- `SEQ_SUBSEQ`
- `ARITH`
- `MULT_CLAUSES`
- `REAL_ARITH`
- `DIFF_SUB`
- `STIRLING_DELTA_DERIV`
- `OTHER_DERIV_LEMMA`
- `GSYM REAL_POW_2`
- `REAL_LT_RMUL`
- `REAL_LT_INV_EQ`
- `REAL_LT_MUL`

### Porting notes (optional)
- The proof relies heavily on `REAL_ARITH` and other decision procedures like `REAL_FIELD`. Ensure that the target proof assistant has comparable automation for real arithmetic and field reasoning.
- The tactics `GEN_REWRITE_TAC RAND_CONV` may need to be adapted using the rewrite mechanisms in the target system.
- The use of `EXISTS_TAC` indicates that the proof involves finding a suitable real-valued function, which may require more manual intervention in systems lacking strong automation for real analysis.


---

## STIRLING_UPPERBOUND

### Name of formal statement
`STIRLING_UPPERBOUND`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_UPPERBOUND = prove
 (`!n. stirling(SUC n) <= &1`,
  INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STIRLING_DECREASES THEN
  ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the value of the Stirling number `stirling(SUC n)` is less than or equal to 1.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: Show that `stirling(SUC 0)` is less than or equal to 1. This involves rewriting `stirling(SUC 0)` using the definition of `stirling`, simplifying using arithmetic, and using the fact that `LN_1` (the natural log of 1 is 0).
- Inductive step: Assume that `stirling(SUC n)` is less than or equal to 1. We want to show that `stirling(SUC(SUC n))` is less than or equal to 1. The proof uses `REAL_LE_TRANS` to chain the inequality, combining the inductive hypothesis with the fact that `stirling(SUC(SUC n))` is less than `stirling(SUC n)` (`STIRLING_DECREASES`). The step `ARITH_RULE \`SUC(SUC n) = SUC n + 1\`` helps in rewriting the expression. `REAL_LT_IMP_LE` is also used to switch a strict inequality to a non-strict inequality, and `ARITH_TAC` to complete the reasoning.

### Mathematical insight
The theorem establishes an upper bound for the Stirling numbers of the first kind. It states that `stirling(SUC n)` is always less than or equal to 1. This is a crucial step, proving that the Stirling number of the first kind converges to some limit.

### Dependencies
- Definitions: `stirling`
- Theorems: `REAL_LE_TRANS`, `STIRLING_DECREASES`, `ARITH_RULE`, `REAL_LT_IMP_LE`
- Constants: `LN_1`


---

## STIRLING_LOWERBOUND

### Name of formal statement
STIRLING_LOWERBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_LOWERBOUND = prove
 (`!n. -- &1 <= stirling(SUC n)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS]] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `b > a ==> a <= b`) THEN
  MATCH_MP_TAC STIRLING_INCREASES THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, negative one is less than or equal to `stirling(SUC n)`.

### Informal sketch
The theorem is proved by induction on `n`.
- Base case: Show that `-1 <= stirling(SUC 0)`. This is done by simplifying `stirling(SUC 0)` to a numerical value and comparing it with `-1`.
- Inductive step: Assume `-1 <= stirling(SUC n)`. The goal is to prove `-1 <= stirling(SUC (SUC n))`.
    - Start by assuming `stirling(SUC n) >= -1`, and trying to prove `stirling(SUC (SUC n)) >= -1`.
    - Using `STIRLING_INCREASES` and `SUC(SUC n) = SUC n + 1`, we know that `stirling(SUC(SUC n)) >= stirling(SUC n)`.
    - By the induction hypothesis, `stirling(SUC n) >= -1`. Therefore, `stirling(SUC(SUC n)) >= -1`.

During both the base case and inductive step:
- The overall proof strategy involves showing that `stirling(SUC n) >= 1` by rewriting it as `stirling(SUC n) - 1 >= 0`, and then manipulating the inequality.
- Specifically, the proof attempts to show `stirling(SUC n) >= 1` by showing that `stirling(SUC n) - 1/ (12 * (SUC n)) >= 0`. Then it suffices to show that `stirling(SUC n) >= stirling(SUC n) - 1/ (12 * (SUC n))` i.e. `0 <= 1/(12 * (SUC n))`
- Tactics like `EXISTS_TAC` are used to introduce this intermediate term and split the proof into manageable goals.
- `MATCH_MP_TAC REAL_LE_TRANS` is used to apply transitivity rule to link the inequalities.
- `REAL_ARITH` is used for arithmetic simplification to check `a-b <= a <=> 0 <= b`

### Mathematical insight
This theorem establishes a lower bound for the Stirling approximation, showing that the `stirling` function (which approximates the natural logarithm of the factorial function) is always greater than or equal to -1 for positive integers.

### Dependencies
- `stirling`
- `REAL_LE_TRANS`
- `LN_1`
- `STIRLING_INCREASES`
- `REAL_OF_NUM_MUL`
- `REAL_POS`
- `REAL_DIV`
- `ARITH_RULE`
- `REAL_MUL_LID`
- `REAL_LE_INV_EQ`


---

## STIRLING_MONO

### Name of formal statement
STIRLING_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_MONO = prove
 (`!m n. ~(m = 0) /\ m <= n ==> stirling n <= stirling m`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `stirling(m + d)` THEN
  ASM_SIMP_TAC[ADD1; REAL_LT_IMP_LE; STIRLING_DECREASES; ADD_EQ_0]);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is not equal to 0 and `m` is less than or equal to `n`, then `stirling n` is less than or equal to `stirling m`.

### Informal sketch
The proof proceeds by induction.
- First, the assumptions are stripped and the assumption `m <= n` is rewritten as `EX d. n = m + d`.
- Then, existential instantiation is performed on `d` assuming `d:num`, and the variable `d` is instantiated in the goal.
- Induction is performed.
- In the base case, the goal `stirling n <= stirling (0:num)` is simplified using `ADD_CLAUSES` and `REAL_LE_REFL`.
- In the inductive step, it is assumed that `stirling(m + d) <= stirling m` and it must be shown that `stirling(m + d + 1) <= stirling (m + 1)`.
- `REAL_LE_TRANS` is used to relate `stirling (m + d + 1)` with `stirling (m + d)` and `stirling m`. Consequently, existence of `stirling(m + d)` needs to be proven
- Finally, the goal is simplified using assumptions and theorems `ADD1`, `REAL_LT_IMP_LE`, `STIRLING_DECREASES`, and `ADD_EQ_0`.

### Mathematical insight
The theorem `STIRLING_MONO` states that `stirling n` is monotonically decreasing with respect to `n`, for `n > 0`.

### Dependencies
- `LE_EXISTS`
- `ADD_CLAUSES`
- `REAL_LE_REFL`
- `REAL_LE_TRANS`
- `ADD1`
- `REAL_LT_IMP_LE`
- `STIRLING_DECREASES`
- `ADD_EQ_0`


---

## STIRLING_CONVERGES

### Name of formal statement
STIRLING_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_CONVERGES = prove
 (`?c. stirling --> c`,
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  REWRITE_TAC[GSYM convergent] THEN MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[mono; real_ge] THEN DISJ2_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC STIRLING_MONO THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  REWRITE_TAC[MR1_BOUNDED; GE; LE_REFL] THEN
  MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN REWRITE_TAC[LE_0] THEN
  SIMP_TAC[REAL_ARITH `-- &1 <= x /\ x <= &1 ==> abs(x) < &2`;
           STIRLING_UPPERBOUND; STIRLING_LOWERBOUND]);;
```

### Informal statement
There exists a real number `c` such that the sequence `stirling` converges to `c`.

### Informal sketch
The proof proceeds as follows:
- Show the existence of a limit `c` to which the `stirling` sequence converges.
- Rewrite the goal using `SEQ_SUC`.
- Rewrite using `convergent` to transform the goal into proving that the `stirling` sequence is convergent.
- Apply `SEQ_BCONV`.
- Split the goal into two subgoals via a conjunction.
- The first subgoal is solved automatically.
- The second subgoal involves showing convergence.
    - Rewrite using `mono` and `real_ge`.
    - Apply `DISJ2_TAC`.
    - Introduce universally quantified variables using `REPEAT GEN_TAC`.
    - Discharge the assumption.
    - Apply `STIRLING_MONO` using `MATCH_MP_TAC`.
    - Apply `MP_TAC` after popping an assumption.
    - Use `ARITH_TAC` to complete the proof
- Apply `MR1_BOUNDED; GE; LE_REFL` to show that the absolute value of the difference between the Stirling sequence and its limit is bounded.
- Introduce existential quantifiers for `2` and `0`.
- Rewrite using `LE_0`.
- Simplify using real arithmetic and the upper and lower bounds (`STIRLING_UPPERBOUND`, `STIRLING_LOWERBOUND`) of `stirling` sequence.

### Mathematical insight
This theorem establishes that the Stirling sequence, which is closely related to the factorial function through logarithms, converges to a real number. This convergence is crucial in approximating the factorial function for large values, as the Stirling formula provides an asymptotic approximation.

### Dependencies
- `convergent`
- `mono`
- `real_ge`
- `STIRLING_MONO`
- `MR1_BOUNDED`
- `GE`
- `LE_REFL`
- `LE_0`
- `STIRLING_UPPERBOUND`
- `STIRLING_LOWERBOUND`

### Porting notes (optional)
The proof relies on real number arithmetic and properties of monotonicity and boundedness. Ensure that the target proof assistant has adequate support for these concepts. The use of tactics like `ONCE_REWRITE_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, `CONJ_TAC`, `ALL_TAC`, `DISJ2_TAC`, `REPEAT GEN_TAC`, `DISCH_TAC`, `POP_ASSUM`, `MP_TAC`, `ARITH_TAC`, `EXISTS_TAC`, and `SIMP_TAC` indicates a proof style involving rewriting, matching, discharging assumptions, and arithmetic reasoning. The porter might need to adapt the specific proof steps based on the available automation in the target proof assistant.


---

## [PI2_LT;

### Name of formal statement
`PI2_LT`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let [PI2_LT; PI2_LE; PI2_NZ] = (CONJUNCTS o prove)
 (`&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)`,
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
The theorem states a collection of inequalities about `pi / 2`. Specifically, it asserts that 0 is strictly less than `pi / 2`, 0 is less than or equal to `pi / 2`, and `pi / 2` is not equal to 0 .

### Informal sketch
The proof proceeds by first applying the theorem `PI_POS`, which states that 0 < `pi`. Then `REAL_ARITH_TAC` is applied to derive the three inequalities.
- `PI_POS` provides `0 < pi`.
- `REAL_ARITH_TAC` then uses this fact to deduce: `0 < pi / 2`, `0 <= pi / 2`, and `~(pi / 2 = 0)`.

### Mathematical insight
This theorem establishes basic facts about the value of `pi / 2`, which are useful in reasoning about trigonometric functions and other mathematical contexts. `pi / 2` is a key constant in mathematics, representing a right angle in radians and appearing frequently in Fourier analysis, complex analysis, and various other areas.

### Dependencies
- `PI_POS`
- `REAL_ARITH_TAC`
- `MP_TAC`
- `CONJUNCTS`
- `prove`


---

## WALLIS_PARTS

### Name of formal statement
WALLIS_PARTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_PARTS = prove
 (`!n. (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`\x. sin(x) pow (n + 1)`; `\x. --cos(x)`;
                `\x. (&n + &1) * sin(x) pow n * cos(x)`;
                `\x. sin(x)`; `&0`; `pi / &2`] INTEGRAL_BY_PARTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN DIFF_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; ADD_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; SIN_0; COS_0] THEN
  REWRITE_TAC[REAL_ARITH `s pow k * s = s * s pow k`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ARITH_RULE `SUC(n + 1) = n + 2`] THEN
  REWRITE_TAC[GSYM ADD1; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_NEG_0; REAL_SUB_LZERO] THEN
  REWRITE_TAC[C MATCH_MP (SPEC_ALL SIN_CIRCLE) (REAL_RING
    `sin(x) pow 2 + cos(x) pow 2 = &1
     ==> (n * sn * cos(x)) * --cos(x) = (n * sn) * (sin(x) pow 2 - &1)`)] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `integral(&0,pi / &2)
        (\x. (&n + &1) * sin x pow (n + 2) - (&n + &1) * sin x pow n) =
    (&n + &1) * (integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) -
                 integral(&0,pi / &2) (\x. sin(x) pow n))`
   (fun th -> SUBST1_TAC th THEN REAL_ARITH_TAC) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `(&n + &1) *
    integral(&0,pi / &2) (\x. sin x pow (n + 2) - sin x pow n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CMUL;
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SUB] THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN SIMP_TAC[PI2_LE]);;
```

### Informal statement
For all natural numbers *n*, (&*n* + 2) multiplied by the integral from 0 to pi/2 of `sin(x)` raised to the power of (*n* + 2) is equal to (&*n* + 1) multiplied by the integral from 0 to pi/2 of `sin(x)` raised to the power of *n*.

### Informal sketch

*   The proof proceeds by induction on *n*. First, a generalisation tactic introduces the quantification over *n*.
*   The main step is to apply integration by parts to the integral term.
    *   The `INTEGRAL_BY_PARTS` tactic is applied with specific choices for the functions *u*, *v'*, *u'*, *v*, *a*, and *b* involved in the integration by parts formula `integral(a, b) (u * v') = [u * v](a, b) - integral(a, b) (u' * v)`.
    *   Specifically, `u = sin(x) pow (n + 1)` and `v' = --cos(x)`. Thus, `u' = (&n + &1) * sin(x) pow n * cos(x)` and `v = sin(x)`. The limits of integration are `0` and `pi / &2`.
*   Simplification tactics are used to rewrite the expressions and prove needed conditions.
*   The theorem `SIN_CIRCLE` stating that `sin(x) pow 2 + cos(x) pow 2 = &1` is instantiated appropriately to simplify trigonometric terms arising from the integration by parts.
*   The goal is transformed to isolate the integral of `sin(x) pow (n + 2)` and `sin(x) pow n` on both sides of the equation.
*   Finally, the proof proceeds by showing that the integral of (&*n* + 1) \* (`sin x` pow (*n* + 2) - `sin x` pow *n*)  is equivalent to (&*n* + 1) \* (the integral of `sin(x) pow (n + 2)` - the integral of `sin(x) pow n`). This is accomplished using linearity properties of integrals such as `INTEGRAL_CMUL` and `INTEGRAL_SUB`.

### Mathematical insight
This theorem represents a reduction formula for the definite integral of powers of the sine function. It essentially links the integral of `sin(x)` to the power (*n* + 2) with the integral of `sin(x)` to the power *n*. This type of reduction formula is a key part of evaluating Wallis' product, which provides an infinite product representation for pi/2.

### Dependencies
*   Theorems:
    *   `INTEGRAL_BY_PARTS`
    *   `SIN_PI2`, `COS_PI2`, `SIN_0`, `COS_0`
    *   `SIN_CIRCLE`
    *   `INTEGRAL_CMUL`
    *    `INTEGRAL_SUB`
*   Definitions:
    *   `real_pow`
    *   `integral`
*   Tactics
    *   `REAL_ARITH`

### Porting notes (optional)
*   The most challenging aspect of porting this theorem is likely the integration by parts step. The `INTEGRAL_BY_PARTS` tactic in HOL Light automatically applies the integration by parts formula, but other proof assistants may require manual application of the formula and management of the resulting terms. Special care should be taken to choose the correct *u* and *v'*.
*   The tactic `REAL_ARITH` is used extensively, which automatically proves equalities and inequalities in real arithmetic. Other proof assistants may require more manual reasoning about real numbers.
*   The `INTEGRABLE_CONV` ensures that the functions are integrable, which might need to be verified explicitly in other systems.


---

## WALLIS_PARTS'

### Name of formal statement
WALLIS_PARTS'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_PARTS' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MP_TAC WALLIS_PARTS THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all natural numbers `n`, the definite integral from 0 to pi/2 of `sin(x)` raised to the power of `n + 2` is equal to `(n + 1) / (n + 2)` times the definite integral from 0 to pi/2 of `sin(x)` raised to the power of `n`.

### Informal sketch
The proof proceeds as follows:
- Invoke the theorem `WALLIS_PARTS`.
- Apply `MP_TAC` to the result of `WALLIS_PARTS` to introduce the assumptions.
- Apply `MATCH_MP_TAC MONO_FORALL` to discharge a monotonicity assumption of the form `!x. f x ==> g x` using the assumption `!x. f x` after generalizing `x` with `MONO_FORALL`.
- Apply `REAL_FIELD` conversion tactic to simplify the resulting real expression.

### Mathematical insight
This theorem establishes a recurrence relation for the definite integral of `sin(x)^n` from 0 to pi/2. This recurrence is a key step in deriving Wallis' product formula for pi. By repeatedly applying this reduction, one can relate the integral to either the integral of `sin(x)^0` or `sin(x)^1`, which are easily computed.

### Dependencies
- Theorem: `WALLIS_PARTS`

### Porting notes (optional)
- The `REAL_FIELD` tactic in HOL Light is a powerful tool for simplifying expressions in the real field. Other proof assistants may require more manual rewriting to achieve the same result.
- The tactic `MATCH_MP_TAC` may require a corresponding step in other systems, for example using `apply` with a suitable lemma.


---

## WALLIS_0

### Name of formal statement
WALLIS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_0 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2`,
  REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
  SIMP_TAC[INTEGRAL_CONST; REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV;
           REAL_OF_NUM_LT; ARITH; REAL_MUL_LID; REAL_SUB_RZERO]);;
```

### Informal statement
The definite integral of the function that maps `x` to `sin(x)` raised to the power of 0, from 0 to pi/2, is equal to pi/2.

### Informal sketch
The proof proceeds by:
- Rewriting the integrand using the following identities: `real_pow` (anything to the power 0 is 1), `REAL_DIV_1` (1/1 = 1), and `REAL_MUL_LID` (1*x = x).
- Simplifying the integral using the following theorems or tactics: `INTEGRAL_CONST` (the integral of a constant is the constant times the interval length), `REAL_LT_IMP_LE` (less than implies less than or equal), `PI_POS` (pi is positive), `REAL_LT_DIV` (inequalities and division), `REAL_OF_NUM_LT` (real number representation of a natural number is less than another), `ARITH` (arithmetic reasoning), `REAL_MUL_LID` (1 is the left identity for multiplication on reals) and `REAL_SUB_RZERO` (x - 0 = x). The use of `ARITH` suggests that some reasoning about inequalities is done automatically.

### Mathematical insight
This theorem calculates a specific definite integral. The integrand `sin(x)^0` simplifies to 1 (except where sin(x) = 0), so the integral represents the length of the interval of integration, from 0 to pi/2, which is pi/2. This result is a basic integral and is used in the derivation of Wallis' product formula for pi.

### Dependencies
- `real_pow`
- `REAL_DIV_1`
- `REAL_MUL_LID`
- `INTEGRAL_CONST`
- `REAL_LT_IMP_LE`
- `PI_POS`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `REAL_SUB_RZERO`


---

## WALLIS_1

### Name of formal statement
WALLIS_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_1 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 1) = &1`,
  MATCH_MP_TAC DEFINT_INTEGRAL THEN REWRITE_TAC[PI2_LE; REAL_POW_1] THEN
  MP_TAC(SPECL [`\x. --cos(x)`; `\x. sin x`; `&0`; `pi / &2`] FTC1) THEN
  REWRITE_TAC[COS_0; COS_PI2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC);;
```
### Informal statement
The definite integral of `sin(x)` raised to the power of 1, from 0 to pi/2, equals 1.

### Informal sketch
The proof proceeds as follows:
- First, the integral `integral(&0,pi / &2) (\x. sin(x) pow 1)` is recognized as a definite integral construct `DEFINT_INTEGRAL`.
- Simplify the expression `sin(x) pow 1` via `REAL_POW_1` to `sin(x)`.
- Apply the Fundamental Theorem of Calculus (FTC1) using `MATCH_MP_TAC` together with known derivative of `cos(x)` is `-sin(x)`. That is, we find an antiderivative of `sin x` to be `-cos(x)`. The antiderivative is evaluated at `x = pi/2` and `x = 0`.
- Evaluate `-cos(x)` at `0` and `pi/2`. `COS_0` states that `cos(0) = 1` and `COS_PI2` says that `cos(pi/2) = 0`.
- Simplify the resulting arithmetic expression using `REAL_RAT_REDUCE_CONV` to get `1`.
- Perform several steps of simplification and finally use real arithmetic reasoning (`REAL_ARITH_TAC`) to complete the proof.

### Mathematical insight
This theorem provides a specific evaluation of a definite integral involving the sine function. It is a fundamental result in calculus, demonstrating how to compute the area under the curve of `sin(x)` from `0` to `pi/2`. This result could be used as a component in larger proofs or calculations involving trigonometric functions.

### Dependencies
**Theorems/Definitions:**
- `DEFINT_INTEGRAL`
- `PI2_LE`
- `REAL_POW_1`
- `COS_0`
- `COS_PI2`
- `FTC1`


---

## WALLIS_EVEN

### Name of formal statement
WALLIS_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_EVEN = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) =
         (&(FACT(2 * n)) / (&2 pow n * &(FACT n)) pow 2) * pi / &2`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; WALLIS_PARTS'] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (&2 * y) * (x * z)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(SUC(2 * n))`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers `n`, the definite integral of `sin(x)` raised to the power of `2 * n` from `0` to `pi / 2` is equal to `((FACT(2 * n)) / ((2 pow n) * (FACT n)) pow 2) * pi / 2`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 0`. The goal `integral(&0,pi / &2) (\x. sin(x) pow (2 * 0)) = (&(FACT(2 * 0)) / (&2 pow 0 * &(FACT 0)) pow 2) * pi / &2` is simplified using `NUM_REDUCE_CONV`, `REAL_RAT_REDUCE_CONV`, and the theorem `WALLIS_0` to a form directly provable by `REAL_ARITH_TAC`.
- Inductive step: Assume the theorem holds for `n`. We need to prove it for `SUC n`.
  - The assumption is rewritten using the arithmetic rule `2 * SUC n = 2 * n + 2` and the theorem `WALLIS_PARTS'`, which relates the integral of `sin(x)` to the power of `2 * n + 2` to the integral of `sin(x)` to the power of `2 * n`.
  - Associativity and simplification rules are applied: `REAL_MUL_ASSOC`, `FACT`, `real_pow`, `REAL_OF_NUM_MUL`, `REAL_POW_MUL`, `real_div`, `REAL_INV_MUL`, `REAL_MUL_ASSOC`, `REAL_OF_NUM_SUC`, `REAL_POW_2`.
  - The goal is then reduced using `REAL_FIELD` to a form provable by the field tactics.

### Mathematical insight
This theorem provides an explicit formula for the definite integral of `sin(x)^(2n)` from 0 to pi/2. This is a key step in deriving Wallis' product formula for pi. The inductive proof leverages integration by parts (`WALLIS_PARTS'`) to relate the integral for `n+1` to the integral for `n`.

### Dependencies
- Theorems: `WALLIS_0`, `WALLIS_PARTS'`
- Definitions: `FACT`, `real_pow`, `real_div`, `REAL_INV_MUL`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_SUC`, `REAL_POW_2`
- Arithmetic rules: `2 * SUC n = 2 * n + 2`, `2 * n + 2 = SUC(SUC(2 * n))`

### Porting notes (optional)
- The proof relies heavily on simplification using real field arithmetic. Ensure the target proof assistant has comparable automation.
- The use of `GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)` might need a specific analogue in other systems, as it performs a targeted rewrite at a specific subterm.


---

## WALLIS_ODD

### Name of formal statement
WALLIS_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_ODD = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
         (&2 pow n * &(FACT n)) pow 2 / &(FACT(2 * n + 1))`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n + 1 = (2 * n + 1) + 2`;
                  WALLIS_PARTS'] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (x * z) * (&2 * y)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `2 * n + 1` FACT_LT) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all natural numbers `n`, the definite integral from 0 to pi/2 of `sin(x)^(2*n+1)` is equal to `(2^n * FACT(n))^2 / FACT(2*n+1)`.

### Informal sketch
The theorem is proved by induction on `n`.

*   Base case (`n = 0`): Evaluate the integral `integral(&0, pi / &2) (\x. sin(x) pow 1)` using `WALLIS_1` and simplify.
*   Inductive step: Assume the theorem holds for `n`. We need to prove it for `SUC n`.
    *   Rewrite `2 * SUC n + 1` to `(2 * n + 1) + 2`.
    *   Use integration by parts (`WALLIS_PARTS'`) to relate the integral for `SUC n` to the integral for `n`.
    *   Apply algebraic simplifications, including rewriting using `FACT`, `real_pow`, and rearranging terms.
    *   Use `FACT_LT` to ensure the arguments to `FACT` are non-negative.
    *   Use field arithmetic to simplify the expression to the desired form.

### Mathematical insight
The theorem provides a closed-form expression for a specific definite integral involving powers of the sine function. The Wallis product formula, of which this is a key component, provides an infinite product representation of pi/2 by relating to the integral of sine and cosine functions.

### Dependencies
- Theorems: `FACT_LT`
- Definitions: `FACT`, `WALLIS_1`, `WALLIS_PARTS'`, `real_pow`, `real_div`
- Other: `REAL_ARITH` (tactical)


---

## WALLIS_QUOTIENT

### Name of formal statement
WALLIS_QUOTIENT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_EVEN; WALLIS_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_POW_INV; REAL_INV_INV] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the ratio of the integral from 0 to pi/2 of `sin(x)` raised to the power of `2*n`, to the integral from 0 to pi/2 of `sin(x)` raised to the power of `2*n + 1`, is equal to `(FACT(2*n) * FACT(2*n + 1)) / ((2^n * FACT(n))^4) * pi / 2`.

### Informal sketch
The proof proceeds as follows:

- First, rewrite the integrals using the recurrence relations `WALLIS_EVEN` and `WALLIS_ODD` for integrals of `sin(x)^(2n)` and `sin(x)^(2n+1)` respectively.

- Then, perform algebraic simplifications using `real_div`, `REAL_INV_MUL`, `GSYM REAL_POW_INV`, and `REAL_INV_INV` to rewrite the expression to a suitable form, presumably canceling out terms and isolating the desired expression.

- Finally, use `REAL_ARITH_TAC` to automatically prove the resulting equality, likely by simplifying and canceling terms.

### Mathematical insight
This theorem relates the ratio of two definite integrals involving powers of the sine function to factorials and powers of 2. It reflects Wallis' product formula for pi, connecting continuous quantities (integrals) to discrete ones (factorials). The result is obtained by iterative application of reduction formulas for the integrals, expressing them in terms of factorials.

### Dependencies
- `WALLIS_EVEN` (Recurrence relation for the integral of `sin(x)^(2n)`)
- `WALLIS_ODD` (Recurrence relation for the integral of `sin(x)^(2n+1)`)
- `real_div` (Definition/properties of real division)
- `REAL_INV_MUL` (Properties of multiplicative inverse and multiplication in reals)
- `REAL_POW_INV` (Properties of real power and inverse)
- `REAL_INV_INV` (The inverse of the inverse is the original number)
- `FACT` (Factorial function)

### Porting notes (optional)
- The main challenge in porting this theorem lies in the automation provided by `REAL_ARITH_TAC`. Other proof assistants may require more explicit steps to prove the final algebraic equality. Porting `WALLIS_EVEN` and `WALLIS_ODD` is necessary. Make sure that `FACT` is defined for natural numbers, and real numbers. Also, special attention should be given to `pow` operation, as different proof assistants could have different implementations or notations.


---

## WALLIS_QUOTIENT'

### Name of formal statement
WALLIS_QUOTIENT'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_QUOTIENT] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM REAL_INV_DIV] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
  MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers `n`, the following equation holds, where the integral is from 0 to pi/2:

(Integral of `sin(x)` raised to `2*n`) divided by (Integral of `sin(x)` raised to `2*n + 1`), multiplied by `2/pi`, equals `(factorial(2*n) * factorial(2*n + 1)) / (2^n * factorial(n))^4`.

### Informal sketch
The proof proceeds as follows:

- First, the theorem `WALLIS_QUOTIENT` is rewritten.
- Then, several applications of `REAL_INV_DIV` are applied using `GEN_REWRITE_TAC` with `LAND_CONV o LAND_CONV o RAND_CONV`.
- The definition of real division, `real_div`, is rewritten using `GSYM real_div`.
- `MATCH_MP_TAC REAL_DIV_RMUL` is used.
- `PI2_NZ` is discharged with `MP_TAC`.
- `REAL_FIELD` is employed via `CONV_TAC` to complete the proof.

### Mathematical insight
The theorem `WALLIS_QUOTIENT'` relates the ratio of two definite integrals involving powers of the sine function to an expression involving factorials. This provides a computational formula and highlights a connection between continuous integration and discrete arithmetic. The presence of `pi` suggests a connection to the Wallis product formula.

### Dependencies
- Theorems: `WALLIS_QUOTIENT`, `REAL_DIV_RMUL`, `PI2_NZ`, `REAL_INV_DIV`, `real_div`
- Tactics: `GEN_TAC`, `REWRITE_TAC`, `GEN_REWRITE_TAC`, `LAND_CONV`, `RAND_CONV`, `GSYM`, `MATCH_MP_TAC`, `MP_TAC`, `CONV_TAC`, `REAL_FIELD`

### Porting notes (optional)
- The main challenge will be ensuring that the real number arithmetic and field simplification tactics are handled equivalently in the target proof assistant. In particular, the `REAL_FIELD` tactic might need to be replaced by multiple calls to simpler tactics with some manual rewriting in other proof assistants like Coq or Lean.


---

## WALLIS_MONO

### Name of formal statement
WALLIS_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_MONO = prove
 (`!m n. m <= n
         ==> integral(&0,pi / &2) (\x. sin(x) pow n)
                <= integral(&0,pi / &2) (\x. sin(x) pow m)`,
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE; MATCH_MP_TAC REAL_POW_1_LE] THEN
  REWRITE_TAC[SIN_BOUNDS] THEN
  (MP_TAC(SPEC `x:real` SIN_POS_PI_LE) THEN
   ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
   REPEAT(POP_ASSUM MP_TAC) THEN MP_TAC PI2_LT THEN REAL_ARITH_TAC));;
```

### Informal statement
For all real numbers `m` and `n`, if `m` is less than or equal to `n`, then the integral from 0 to pi/2 of `sin(x)` raised to the power of `n` is less than or equal to the integral from 0 to pi/2 of `sin(x)` raised to the power of `m`.

### Informal sketch
The proof demonstrates that the integral of `sin(x)^n` from 0 to `pi/2` is a decreasing function of `n`.
- Show that the integrals exist by proving that `sin(x)^n` and `sin(x)^m` are integrable on the interval `[0, pi/2]`.
- It uses `INTEGRAL_LE` to show that to prove the inequality of the integrals, it suffices to prove that `sin(x)^n <= sin(x)^m` for all `x` in `[0, pi/2]`.
- The goal is then reduced to proving `sin(x)^n <= sin(x)^m` given `0 <= x <= pi/2` and `m <= n`.
- Rewrite `sin(x)^n` as `sin(x)^m * sin(x)^(n-m)`.
- Prove that `sin(x)^(n-m) <= 1`, since `sin(x) <= 1` for `0 <= x <= pi/2` and `n-m >= 0`.
- Multiply both sides of `sin(x)^(n-m) <= 1` by `sin(x)^m`, to get the desired inequality `sin(x)^n <= sin(x)^m` via `REAL_LE_LMUL`.

### Mathematical insight
This theorem establishes the monotonicity of the definite integral of `sin(x)` raised to a power `n`, over the interval `[0, pi/2]`. As the exponent `n` increases, the value of the integral decreases. This property is crucial in calculating the Wallis product, and its proof relies on bounding the sine function and using properties of real powers.

### Dependencies
- `LE_EXISTS`
- `INTEGRAL_LE`
- `INTEGRABLE_CONV`
- `PI2_LE`
- `REAL_POW_ADD`
- `REAL_MUL_RID`
- `REAL_LE_LMUL`
- `REAL_POW_LE`
- `REAL_POW_1_LE`
- `SIN_BOUNDS`
- `SIN_POS_PI_LE`
- `PI2_LT`

### Porting notes (optional)
The proof relies on properties of real number arithmetic, inequalities, and the sine function. Porting to other proof assistants may require careful handling of real number axioms and the definition of `sin(x)`. The tactic `ONCE_DEPTH_CONV INTEGRABLE_CONV` is used to prove integrability of the functions. In other proof assistants, the integrability condition may need to be proved explicitly using definitions and theorems specific to integration theory in those systems.


---

## WALLIS_LT

### Name of formal statement
WALLIS_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_LT = prove
 (`!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MATCH_MP_TAC ODDEVEN_INDUCT THEN
  REWRITE_TAC[WALLIS_0; WALLIS_1; PI2_LT; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WALLIS_PARTS'] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, 0 is less than the definite integral from 0 to pi/2 of the function `sin(x)^n`.

### Informal sketch
The proof proceeds by induction on whether `n` is odd or even.
- Base cases: The theorem is proven for `n = 0` and `n = 1` using `WALLIS_0`, `WALLIS_1`, `PI2_LT`, `REAL_OF_NUM_LT`, and `ARITH`.
- Inductive step: Assume the theorem holds for `n = k` and `n = k + 1`. We need to show it holds for `n = k + 2`.
  - The assumption `&0 < integral(&0,pi / &2) (\x. sin(x) pow n)` is rewritten using `WALLIS_PARTS'`.
  - The result is proven using `REAL_LT_MUL`, `REAL_LT_DIV`, and `REAL_ARITH_TAC`.

### Mathematical insight
The theorem states that the integral of `sin(x)^n` from 0 to pi/2 is positive for all natural numbers `n`. This is a component of Wallis' product formula for pi. The positivity is not immediately obvious from the integral definition in HOL Light and requires a specific proof.

### Dependencies
- Theorems: `WALLIS_0`, `WALLIS_1`, `PI2_LT`, `REAL_OF_NUM_LT`, `WALLIS_PARTS'`, `REAL_LT_MUL`, `REAL_LT_DIV`
- Tactics: `ODDEVEN_INDUCT`, `MATCH_MP_TAC`, `REWRITE_TAC`, `STRIP_TAC`, `ASM_REWRITE_TAC`, `REAL_ARITH_TAC`

### Porting notes (optional)
The proof relies on real arithmetic and inequalities. Ensure that the target proof assistant has adequate support for real number reasoning and automated arithmetic tactics. The `ODDEVEN_INDUCT` tactic used in HOL Light might need manual expansion in other proof assistants.


---

## WALLIS_NZ

### Name of formal statement
WALLIS_NZ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_NZ = prove
 (`!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)`,
  MP_TAC WALLIS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, it is not the case that the integral from 0 to pi/2 of the function `sin(x)` raised to the power of `n` is equal to 0.

### Informal sketch
The proof proceeds by:
- First, utilizing `WALLIS_LT` (presumably a theorem stating that the integral of `sin(x)` to the power of `n` from 0 to pi/2 is greater than 0).
- Instantiating this result for all `n` using `MONO_FORALL`.
- Finally, discharging the goal using `REAL_ARITH_TAC` (presumably using real arithmetic to derive the desired result).

### Mathematical insight
The theorem `WALLIS_NZ` states that the definite integral of `sin(x)^n` from 0 to `pi/2` is non-zero for all natural numbers `n`. This is an important intermediate result in the development of Wallis' product formula for `pi`. This formula offers a way to approximate the value of `pi` through an infinite product involving ratios of factorials or the gamma function. The stated theorem is a key property: the integral is always positive.

### Dependencies
- Theorems: `WALLIS_LT`

### Porting notes (optional)
The main challenge in porting this theorem might be the specific tactic `REAL_ARITH_TAC`. Other proof assistants might require a more explicit proof of the inequality based on real arithmetic principles, rather than relying on an automated procedure. The theorem `WALLIS_LT` needs to be ported first, and care must be taken to ensure correct handling of real number arithmetic in the target system.


---

## WALLIS_BOUNDS

### Name of formal statement
WALLIS_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_BOUNDS = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 1))
        <= integral(&0,pi / &2) (\x. sin(x) pow n) /\
       integral(&0,pi / &2) (\x. sin(x) pow n) <=
        (&n + &2) / (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow (n + 1))`,
  GEN_TAC THEN SIMP_TAC[WALLIS_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &2) / (&n + &1) *
              integral (&0,pi / &2) (\x. sin x pow (n + 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WALLIS_PARTS'] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[WALLIS_MONO; ARITH_RULE `n + 1 <= n + 2`] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC);;
```

### Informal statement
For all `n`, the integral from 0 to pi/2 of `sin(x)^(n+1)` is less than or equal to the integral from 0 to pi/2 of `sin(x)^n`, and the integral from 0 to pi/2 of `sin(x)^n` is less than or equal to `(n+2)/(n+1)` times the integral from 0 to pi/2 of `sin(x)^(n+1)`.

### Informal sketch

*   The proof starts by generalizing the goal using `GEN_TAC` and then simplifying using `WALLIS_MONO` (monotonicity of the Wallis integral) and `LE_ADD`.
*   It then applies `REAL_LE_TRANS`, which requires proving an intermediate inequality.  We introduce an existential variable `(&n + &2) / (&n + &1) * integral (&0,pi / &2) (\x. sin x pow (n + 2))` as witness.
*   The proof splits into two parts to prove the two inequalities required by `REAL_LE_TRANS`.
    *   The first part involves rewriting using the result of integration by parts, i.e. `WALLIS_PARTS'`, then using the fact that equality implies less than or equal, and finally simplifying the resulting term using real field arithmetic.
    *   The second part is trivially true.
*   Lastly, it applies `REAL_LE_LMUL` and then simplifies with `WALLIS_MONO` and a simple arithmetic fact, followed by `REAL_LE_DIV` and `REAL_ARITH_TAC`.

### Mathematical insight
This theorem establishes bounds for the Wallis integral, which is the definite integral of `sin(x)^n` from 0 to pi/2. The theorem states that the integral of `sin(x)^(n+1)` is always less than or equal to the integral of `sin(x)^n`, reflecting the decreasing nature of `sin(x)^n` as `n` increases on the interval [0, pi/2]. It further provides an upper bound for the integral of `sin(x)^n` in terms of the integral of `sin(x)^(n+1)`. These are important inequalities in analysis and are used in the derivation of Wallis' product formula for pi.

### Dependencies
*   Theorems/Definitions:
    *   `WALLIS_MONO`
    *   `WALLIS_PARTS'`
    *   `LE_ADD`
    *   `REAL_LE_TRANS`
    *   `REAL_EQ_IMP_LE`
    *   `REAL_LE_LMUL`
    *   `REAL_LE_DIV`

*   Tactics:
    *   `GEN_TAC`
    *   `SIMP_TAC`
    *   `MATCH_MP_TAC`
    *   `EXISTS_TAC`
    *   `CONJ_TAC`
    *   `REWRITE_TAC`
    *   `CONV_TAC`
    *   `REAL_FIELD`
    *   `ALL_TAC`
    *   `ARITH_RULE`
    *   `REAL_ARITH_TAC`


---

## WALLIS_RATIO_BOUNDS

### Name of formal statement
WALLIS_RATIO_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_RATIO_BOUNDS = prove
 (`!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)`,
  GEN_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; WALLIS_LT; REAL_MUL_LID; WALLIS_BOUNDS];
    SIMP_TAC[REAL_LE_LDIV_EQ; WALLIS_LT; WALLIS_BOUNDS]]);;
```
### Informal statement
For all natural numbers `n`, the following holds:

`1` is less than or equal to the result of dividing the integral from `0` to `pi / 2` of `sin(x)` raised to the power of `n`, by the integral from `0` to `pi / 2` of `sin(x)` raised to the power of `n + 1`; and

the result of dividing the integral from `0` to `pi / 2` of `sin(x)` raised to the power of `n`, by the integral from `0` to `pi / 2` of `sin(x)` raised to the power of `n + 1` is less than or equal to `(n + 2) / (n + 1)`.

### Informal sketch
The proof proceeds by splitting the main goal into two subgoals, corresponding to the lower and upper bounds on the ratio of the integrals. Both subgoals are then discharged by simplification using the following steps:

- Apply real number arithmetic lemmas `REAL_LE_RDIV_EQ` and `REAL_LE_LDIV_EQ` to manipulate inequalities involving division.
- Utilize `WALLIS_LT` which I expect to be a strict inequality to help establish the lower and upper bounds.
- Use `REAL_MUL_LID` to simplify expressions involving multiplication by the identity `1`.
- Use `WALLIS_BOUNDS`, which I expect to be an existing theorem providing bounds on the ratio.

### Mathematical insight
This theorem provides upper and lower bounds for the ratio of successive integrals of `sin(x)` raised to integer powers from `0` to `pi/2`. These bounds are crucial for establishing the Wallis product formula, which relates an infinite product to `pi/2`.

### Dependencies
- `REAL_LE_RDIV_EQ`
- `WALLIS_LT`
- `REAL_MUL_LID`
- `WALLIS_BOUNDS`
- `REAL_LE_LDIV_EQ`


---

## WALLIS

### Name of formal statement
WALLIS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS = prove
 (`(\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
   --> pi / &2`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC SEQ_INV THEN
  CONJ_TAC THENL [ALL_TAC; MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD] THEN
  REWRITE_TAC[GSYM WALLIS_QUOTIENT'] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [REAL_ARITH `x = (x - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!d. &1 <= x /\ x <= d /\ d - &1 <= e ==> abs(x - &1) <= e`) THEN
  EXISTS_TAC `(&(2 * n) + &2) / (&(2 * n) + &1)` THEN
  REWRITE_TAC[WALLIS_RATIO_BOUNDS] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_FIELD
   `(&2 * &n + &2) / (&2 * &n + &1) - &1 = &1 / (&2 * &n + &1)`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;
```

### Informal statement
For every natural number `n`, the following equation holds: `(&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1)))` converges to `pi / &2` as `n` tends to infinity.

### Informal sketch
The proof demonstrates that the given sequence converges to `pi / &2`.

- The proof starts by manipulating the expression using `REAL_INV_DIV` and `SEQ_INV`.
- It uses `WALLIS_QUOTIENT'` theorem after some real field manipulations.
- Then, the expression is rewritten based on properties of real multiplication, namely, `REAL_MUL_SYM` and `REAL_MUL_RID`.
- The proof relies heavily on a series of rewrites and matching with sequences, focusing on `SEQ_MUL`, `SEQ_CONST`, `SEQ_ADD`, and `SEQ_LE_0`.
- A key step involves converting `x` to `(x - &1) + &1`. Applying `REAL_ADD_LID`.
- The proof requires showing there exists some `\n. &1 / &n`, by using `SEQ_HARMONIC`. Also requires showing there exists `1`, by using the theorem GE.
- To show `\&1 <= x /\ x <= d /\ d - \&1 <= e ==> abs(x - \&1) <= e`, an existential instantiation is done with `(&(2 * n) + &2) / (&(2 * n) + &1)`.
- The proof relies on bounding the Wallis ratio.
- It applies `WALLIS_RATIO_BOUNDS` and uses some simplifications in real field.
- In the end, the `REAL_LE_INV2` is used with hypothesis, after which it simplifies `REAL_OF_NUM_LE` with `REAL_ARITH_TAC`.

### Mathematical insight
The Wallis product provides an infinite product representation of `pi/2`. The theorem formalizes the convergence of a related quotient, which converges to `pi/2`. This result links the factorial function to a fundamental constant in mathematics and serves a historical landmark in the analysis of infinite products.

### Dependencies
- `GSYM REAL_INV_DIV`
- `SEQ_INV`
- `PI2_NZ`
- `REAL_FIELD`
- `GSYM WALLIS_QUOTIENT'`
- `REAL_MUL_SYM`
- `GSYM REAL_MUL_RID`
- `SEQ_MUL`
- `SEQ_CONST`
- `REAL_ARITH x = (x - &1) + &1`
- `GSYM REAL_ADD_LID`
- `SEQ_ADD`
- `SEQ_LE_0`
- `SEQ_HARMONIC`
- `GE`
- `REAL_ARITH !d. &1 <= x /\ x <= d /\ d - &1 <= e ==> abs(x - &1) <= e`
- `WALLIS_RATIO_BOUNDS`
- `GSYM REAL_OF_NUM_MUL`
- `REAL_FIELD (&2 * &n + &2) / (&2 * &n + &1) - &1 = &1 / (&2 * &n + &1)`
- `real_div`
- `REAL_MUL_LID`
- `REAL_ABS_INV`
- `REAL_ABS_NUM`
- `REAL_LE_INV2`
- `GSYM REAL_OF_NUM_LE`
- `REAL_ARITH_TAC`

### Porting notes (optional)
- The proof relies heavily on `REAL_ARITH`. Make sure the target proof assistant has similar automation.
- The tactics `ONCE_REWRITE_TAC, MATCH_MP_TAC, REWRITE_TAC` are frequently used, demonstrating the importance of rewriting and modus ponens in HOL Light.


---

## LN_WALLIS

### Name of formal statement
LN_WALLIS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_WALLIS = prove
 (`(\n. &4 * &n * ln(&2) + &4 * ln(&(FACT n)) -
        (ln(&(FACT(2 * n))) + ln(&(FACT(2 * n + 1))))) --> ln(pi / &2)`,
  REWRITE_TAC[REAL_ARITH `&4 * x + &4 * y - z = &4 * (x + y) - z`] THEN
  SUBGOAL_THEN `!n. &0 < &2 pow n`
   (fun th -> SIMP_TAC[th; GSYM LN_POW; REAL_OF_NUM_LT; ARITH; GSYM LN_MUL;
                       FACT_LT; REAL_POW_LT; REAL_LT_MUL; GSYM LN_DIV]) THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC CONTL_SEQ THEN REWRITE_TAC[WALLIS] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `inv(pi / &2)` THEN
  MP_TAC(SPEC `pi / &2` (DIFF_CONV `\x. ln(x)`)) THEN
  SIMP_TAC[ETA_AX; PI2_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RID]);;
```

### Informal statement
The limit, as `n` tends to infinity, of `4 * n * ln(2) + 4 * ln(FACT n) - (ln(FACT(2 * n)) + ln(FACT(2 * n + 1)))` is equal to `ln(pi / 2)`.

### Informal sketch
The proof proceeds as follows:

- First, rewrite the goal using the identity `&4 * x + &4 * y - z = &4 * (x + y) - z`.
- Next, prove the subgoal `!n. &0 < &2 pow n` which is needed for applying `LN_POW` later.
  - This involves simplification using theorems like `LN_POW`, `REAL_OF_NUM_LT`, `LN_MUL`, `FACT_LT`, `REAL_POW_LT`, `REAL_LT_MUL`, and `LN_DIV`.
  - Simplify further with real power and arithmetic lemmas
- Apply `CONTL_SEQ` and rewrite the expression with `WALLIS`.
- Apply `DIFF_CONT` which states that if a sequence converges, there exists a continuous function that agrees with the sequence. Instantiate the existential with `inv(pi / &2)`.
- Specialize the `DIFF_CONV` theorem `\x. ln(x)` with `pi / &2` and apply Modus Ponens.
- Simplify using `ETA_AX`, `PI2_LT`, `REAL_LT_DIV`, `REAL_OF_NUM_LT`, and arithmetic lemmas.
- Rewrite using `REAL_MUL_RID`.

### Mathematical insight
This theorem provides the value of the limit related to Wallis' product formula, expressed in terms of logarithms. It connects the factorial function, the natural logarithm, and the constant `pi` in a non-trivial manner.

### Dependencies
- `REAL_ARITH`
- `LN_POW`
- `REAL_OF_NUM_LT`
- `ARITH`
- `LN_MUL`
- `FACT_LT`
- `REAL_POW_LT`
- `REAL_LT_MUL`
- `LN_DIV`
- `CONTL_SEQ`
- `WALLIS`
- `DIFF_CONT`
- `DIFF_CONV`
- `ETA_AX`
- `PI2_LT`
- `REAL_LT_DIV`
- `REAL_MUL_RID`


---

## STIRLING

### Name of formal statement
STIRLING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING = prove
 (`(\n. ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n + ln(&2 * pi) / &2))
   --> &0`,
  REWRITE_TAC[REAL_ARITH `a - (b - c + d) = (a - (b - c)) - d`] THEN
  SUBST1_TAC(SYM(SPEC `ln(&2 * pi) / &2` REAL_SUB_REFL)) THEN
  MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[SEQ_CONST] THEN
  X_CHOOSE_THEN `C:real` MP_TAC STIRLING_CONVERGES THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[stirling] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `1`] o MATCH_MP SEQ_SUBSEQ) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `0`] o MATCH_MP SEQ_SUBSEQ) THEN
  REWRITE_TAC[ARITH; ADD_CLAUSES; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEQ_MUL o CONJ (SPEC `&4` SEQ_CONST)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  MP_TAC LN_WALLIS THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  REWRITE_TAC[ARITH_RULE
   `(a + &4 * x - (y + z)) - (&4 * (x - b) - ((y - c) + (z - d))) =
    (a + &4 * b) - (c + d)`] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `C = ln(&2 * pi) / &2` (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC `&2 * ln(&2)` SEQ_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  SIMP_TAC[LN_DIV; PI_POS; REAL_OF_NUM_LT; ARITH; LN_MUL] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + p - l - (&4 * C - (C + C)) =
                          (l + p) - &2 * C`] THEN
  SIMP_TAC[REAL_ARITH `C = (l + p) / &2 <=> (l + p) - &2 * C = &0`] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
    SEQ_UNIQ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_ARITH
   `a + (b + &4 * (c - x)) - ((d - &2 * x) + (e - (&2 * x + &1))) =
    (a + b + &4 * c + &1) - (d + e)`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + &4 * n * l + &4 * (n + &1 / &2) * x + &1 =
                          (&4 * n + &2) * (l + x) + &1`] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_MUL; REAL_OF_NUM_LT; ARITH; LT_0] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ARITH
   `((&4 * n + &2) * l + &1) - ((&2 * n + &1 / &2) * l + z) =
    (&2 * n + &3 / &2) * l + &1 - z`] THEN
  REWRITE_TAC[REAL_ARITH
   `(&2 * n + &3 / &2) * l + &1 - ((&2 * n + &1) + &1 / &2) * l' =
    (&2 * n + &3 / &2) * (l - l') + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&0 = -- &1 + &1`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * (b - c) = --(a * (c - b))`] THEN
  REWRITE_TAC[GSYM SEQ_NEG] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; LT_0; ARITH;
           REAL_ARITH `&0 < &2 * &n + &1`] THEN
  SIMP_TAC[REAL_OF_NUM_LT; LT_0; REAL_FIELD
   `&0 < x ==> (&2 * x + &1) / (&2 * x) = &1 + &1 / (&2 * x)`] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  MP_TAC SEQ_SUBSEQ THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o GENL [`f:num->real`; `l:real`] o
   SPECL [`f:num->real`; `l:real`; `2`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH; REAL_OF_NUM_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&1 = &1 + &3 / &2 * &0`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[LN_LIM_LEMMA] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  MP_TAC LN_LIM_LEMMA THEN MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_MUL) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_ASSOC; REAL_MUL_LINV;
           REAL_MUL_RID; REAL_OF_NUM_EQ; NOT_SUC]);;
```

### Informal statement
For all natural numbers `n`, the limit as `n` approaches infinity of the difference between the natural logarithm of the factorial of `n` and the expression `(n + 1/2) * ln(n) - n + ln(2 * pi) / 2` is equal to 0.

### Informal sketch
The proof demonstrates that the error term in Stirling's approximation converges to 0.

- First, rewrite the goal using real arithmetic to isolate the constant `ln(2 * pi) / 2`.
- Introduce a real constant `C` such that the sequence converges to `C`, using the theorem `STIRLING_CONVERGES`.
- Apply rewriting rules to prepare the expression for the application of `stirling` theorem.
- Use inequalities about sequences to manipulate the terms.
- Simplify using arithmetic and algebraic properties of real numbers and logarithms.
- Apply the `LN_WALLIS` theorem.
- Introduce a subgoal to prove that `C = ln(2 * pi) / 2`, and rewrite the goal using this equality.
- Simplify using properties of logarithms, arithmetic, and the uniqueness of limits.
- Apply a series of rewrites and simplifications involving logarithmic and arithmetic identities to massage the expression into a suitable form. Key steps involve distributing terms, combining logarithms, and using facts about real number arithmetic.
- Apply sequence operations and properties of limits, including `SEQ_ADD`, `SEQ_CONST`, `SEQ_NEG`, `SEQ_SUC`, and `SEQ_SUBSEQ`.
- Apply lemmas about the limit of logarithms (`LN_LIM_LEMMA`).
- Use the fact that the harmonic series diverges (`SEQ_HARMONIC`).
- Simplify the final expression using properties of division, multiplication, and arithmetic.

### Mathematical insight
The theorem states that the difference between `ln(FACT n)` and `(n + 1/2) * ln(n) - n + ln(2 * pi) / 2` approaches 0 as `n` tends to infinity. This is a precise way of saying that `ln(FACT n)` is asymptotically equal to `(n + 1/2) * ln(n) - n + ln(2 * pi) / 2`. Exponentiating, this gives Stirling's approximation for the factorial function: `n! ≈ sqrt(2 * pi * n) * (n/e)^n`. The theorem quantifies the asymptotic convergence in the logarithm scale.

### Dependencies
- Theorems: `STIRLING_CONVERGES`, `LN_WALLIS`, `SEQ_UNIQ`, `RIGHT_IMP_FORALL_THM`
- Definitions: `FACT`, `ln`, `pi`, `EXP`
- Constants: `SEQ_CONST`
- Lemmas: `LN_LIM_LEMMA`, `SEQ_HARMONIC`


---

