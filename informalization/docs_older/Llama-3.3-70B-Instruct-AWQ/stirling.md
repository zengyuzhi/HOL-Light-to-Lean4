# stirling.ml

## Overview

Number of statements: 32

The `stirling.ml` file formalizes Stirling's approximation, a mathematical concept used to approximate large factorials. It builds upon definitions and theorems imported from `analysis.ml` and `transc.ml`, suggesting a focus on analytical and transcendental functions. The file likely contains definitions, theorems, and constructions related to Stirling's approximation, providing a foundation for further mathematical derivations and proofs. Its scope is centered around the mathematical formalization of this approximation, contributing to the larger library's coverage of mathematical analysis.

## ODDEVEN_INDUCT

### Name of formal statement
ODDEVEN_INDUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODDEVEN_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH])
```

### Informal statement
For all properties P, if P holds for 0 and 1, and for every natural number n, if P holds for n then it also holds for n + 2, then P holds for all natural numbers n.

### Informal sketch
* The proof starts by assuming a property P and its validity for 0 and 1.
* It then proceeds by induction, using `INDUCT_TAC`, to show that if P holds for some n, it also holds for n + 2, leveraging the assumption that P n implies P(n + 2).
* The `SUBGOAL_THEN` tactic is used to derive an intermediate result, which is then used by `MESON_TAC` to simplify the proof.
* The `ASM_SIMP_TAC` tactic is applied with specific theorems (`ADD1`, `GSYM ADD_ASSOC`, and `ARITH`) to simplify arithmetic expressions and establish the inductive step.

### Mathematical insight
This theorem provides a basis for proving statements about natural numbers by induction, specifically when a property holds for even and odd numbers alternately. It's a variant of the standard induction principle, tailored for properties that exhibit a periodic or alternating pattern.

### Dependencies
* `ADD1`
* `GSYM ADD_ASSOC`
* `ARITH`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how they handle induction and arithmetic reasoning. Some systems may have built-in support for arithmetic simplification or induction tactics that can be used similarly to `ASM_SIMP_TAC` and `INDUCT_TAC`. Additionally, the representation of natural numbers and their properties might differ, requiring adjustments to the theorem statement and its proof.

---

## LN_LIM_BOUND

### Name of formal statement
LN_LIM_BOUND

### Type of the formal statement
Theorem

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
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers $n$, the absolute value of $n \cdot \ln\left(1 + \frac{1}{n}\right) - 1$ is less than or equal to $\frac{1}{2n}$.

### Informal sketch
* The proof starts by assuming $n$ is a non-zero natural number.
* It then applies the `MCLAURIN_LN_POS` theorem with specific values to establish a relationship involving $\ln\left(1 + \frac{1}{n}\right)$.
* The tactic `ASM_SIMP_TAC` is used with various theorems to simplify expressions involving real numbers, including `SUM_2`, `REAL_LT_DIV`, and `REAL_OF_NUM_LT`.
* A real number $t$ is chosen such that certain conditions are met, utilizing `DISCH_THEN` and `X_CHOOSE_THEN`.
* Further simplifications and rewrites are applied using various `REWRITE_TAC` and `ASM_REWRITE_TAC` steps, involving properties of real numbers such as `REAL_INV_0`, `REAL_MUL_RZERO`, and `REAL_ADD_LID`.
* The proof involves showing that the absolute value of an expression is bounded by another expression, utilizing `MATCH_MP_TAC` with `REAL_LE_LMUL` and `REAL_LE_RMUL`, and applying `CONV_TAC` with `REAL_RAT_REDUCE_CONV`.
* The final steps involve simplifying inequalities and applying `REAL_ARITH_TAC` to conclude the proof.

### Mathematical insight
This theorem provides a bound on the expression $n \cdot \ln\left(1 + \frac{1}{n}\right) - 1$ for non-zero natural numbers $n$. The bound $\frac{1}{2n}$ indicates how quickly this expression converges to a limit as $n$ increases. This is a crucial step in establishing limits and asymptotic behavior in mathematical analysis, particularly in the study of functions involving logarithms.

### Dependencies
* Theorems:
  - `MCLAURIN_LN_POS`
  - `SUM_2`
  - `REAL_LT_DIV`
  - `REAL_OF_NUM_LT`
  - `LT_NZ`
  - `ARITH`
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
  - `REAL_OF_NUM_EQ`
  - `REAL_FIELD`
  - `REAL_ARITH`
  - `REAL_MUL_RINV`
  - `REAL_ABS_NEG`
  - `REAL_ABS_MUL`
  - `REAL_INV_MUL`
  - `REAL_LE_LMUL`
  - `REAL_LE_RMUL`
  - `REAL_LE_INV_EQ`
  - `REAL_POS`
  - `REAL_ABS_INV`
  - `REAL_INV_LE_1`
  - `REAL_LE_MUL2`
* Tactics and convs:
  - `REPEAT`
  - `STRIP_TAC`
  - `MP_TAC`
  - `ASM_SIMP_TAC`
  - `DISCH_THEN`
  - `X_CHOOSE_THEN`
  - `ASM_REWRITE_TAC`
  - `REWRITE_TAC`
  - `CONV_TAC`
  - `MATCH_MP_TAC`
  - `GEN_REWRITE_TAC`
  - `UNDISCH_TAC`
  - `REAL_ARITH_TAC`

---

## LN_LIM_LEMMA

### Name of formal statement
LN_LIM_LEMMA

### Type of the formal statement
Theorem

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
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the limit as `n` approaches infinity of `n * ln(1 + 1/n)` approaches 1.

### Informal sketch
* The proof begins by applying `GEN_REWRITE_TAC` to transform the expression `n * ln(1 + 1/n)` using the `REAL_ARITH` rule.
* It then applies `MATCH_MP_TAC` with `SEQ_ADD` to establish a relationship between the sequence and its limit.
* The proof continues by applying `EXISTS_TAC` to introduce a function `1/n` and rewriting using `SEQ_HARMONIC`.
* Further steps involve applying `MATCH_MP_TAC` with `SEQ_LE_0` and `REAL_LE_TRANS` to establish inequalities and limits.
* Key tactics like `ASM_SIMP_TAC` with `LN_LIM_BOUND` and `MATCH_MP_TAC` with `REAL_LE_INV2` are used to simplify and derive the final limit.
* The proof concludes with `REAL_ARITH_TAC` to finalize the limit calculation.

### Mathematical insight
This theorem is important because it establishes a fundamental limit property involving the natural logarithm function, which is crucial in various mathematical analyses, particularly in calculus and analysis. The limit `n * ln(1 + 1/n)` approaching 1 as `n` approaches infinity has implications in understanding the behavior of functions and sequences in mathematical analysis.

### Dependencies
* Theorems:
  - `SEQ_ADD`
  - `SEQ_LE_0`
  - `REAL_LE_TRANS`
  - `REAL_LE_INV2`
* Definitions:
  - `REAL_ARITH`
  - `LN_LIM_BOUND`
  - `SEQ_HARMONIC`
  - `REAL_OF_NUM_EQ`
* Tactics and rules:
  - `GEN_REWRITE_TAC`
  - `MATCH_MP_TAC`
  - `EXISTS_TAC`
  - `REWRITE_TAC`
  - `ASM_SIMP_TAC`
  - `UNDISCH_TAC`
  - `REAL_ARITH_TAC`

---

## POSITIVE_DIFF_LEMMA

### Name of formal statement
POSITIVE_DIFF_LEMMA

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC)
```

### Informal statement
For all functions `f` and `f'`, if for all `x` greater than `0`, `f` is differentiable at `x` with derivative `f'` and `f'(x)` is less than `0`, and the limit of `f(n)` as `n` approaches infinity is `0`, then for all non-zero natural numbers `n`, `0` is less than `f(n)`.

### Informal sketch
* Assume `f` and `f'` satisfy the given conditions.
* Use the `MVT_ALT` theorem to establish a relationship between `f(m)` and `f(p)` for `m` and `p` satisfying certain conditions.
* Apply `REAL_ARITH` and `REAL_LT_MUL` to derive inequalities involving `f(m)` and `f(p)`.
* Use these inequalities to show that `f(n+1)` is less than `0` for all `n`.
* Apply the `GEN_REWRITE_RULE` and `SEQ` rules to derive a contradiction.
* Conclude that `0` is less than `f(n)` for all non-zero natural numbers `n`.
* Key steps involve using the `MVT_ALT` theorem, applying arithmetic properties, and using proof by contradiction.

### Mathematical insight
This lemma provides a sufficient condition for a function to be positive at all non-zero natural numbers, based on its differentiability and limit properties. The condition involves the derivative of the function being negative for all positive `x`, which implies that the function is decreasing. The lemma is useful in proving inequalities involving limits and derivatives.

### Dependencies
* Theorems:
  + `MVT_ALT`
  + `REAL_ARITH`
  + `REAL_LT_MUL`
  + `LT_NZ`
  + `LTE_TRANS`
  + `REAL_OF_NUM_LT`
  + `REAL_LTE_TRANS`
  + `REAL_SUB_LT`
  + `REAL_OF_NUM_LT`
  + `REAL_LT_TRANS`
* Definitions:
  + `diffl` (differentiability)
  + `SEQ` (sequence)

### Porting notes
When translating this lemma into other proof assistants, pay attention to the handling of binders and the `MVT_ALT` theorem, which may have different formulations or requirements. Additionally, the use of `REAL_ARITH` and `REAL_LT_MUL` may need to be adapted to the target system's arithmetic and inequality handling.

---

## stirling

### Name of formal statement
stirling

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let stirling = new_definition
 `stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)`
```

### Informal statement
The `stirling` function is defined as the natural logarithm of the factorial of `n`, minus the product of `n` plus one half and the natural logarithm of `n`, plus `n`.

### Informal sketch
* The definition involves calculating the natural logarithm of the factorial of a given number `n`.
* Then, it calculates the product of `n` plus one half and the natural logarithm of `n`.
* Finally, it subtracts the result of the product from the natural logarithm of the factorial of `n` and adds `n`.

### Mathematical insight
The `stirling` function appears to be related to Stirling's approximation, which is a method for approximating the factorial of a number. This definition likely plays a role in numerical analysis or combinatorics, providing an approximate value for the factorial function using logarithmic and linear components.

### Dependencies
* `FACT` 
* `ln` 

### Porting notes
When translating this definition into other proof assistants, ensure that the `FACT` function (likely representing the factorial) and the `ln` function (natural logarithm) are properly defined and accessible. Note that different systems may handle the definition of these functions or the arithmetic operations slightly differently, so adjustments may be necessary to ensure compatibility.

---

## STIRLING_DIFF

### Name of formal statement
STIRLING_DIFF

### Type of the formal statement
Theorem

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
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers `n`, the difference between `stirling(n)` and `stirling(n + 1)` is equal to `((n + 1) / 2) * ln((n + 1) / n) - 1`.

### Informal sketch
* The proof begins with a universal quantification over `n`, assuming `n` is not equal to 0.
* It then applies various simplification and rewriting steps using tactics such as `REWRITE_TAC` and `SIMP_TAC` to manipulate the expression involving `stirling(n)` and `stirling(n + 1)`.
* The `MATCH_MP_TAC` tactic is used with a specific `REAL_ARITH` rule to establish an equality involving the terms `f`, `f'`, `nl`, `nl'`, `n`, and `n'`.
* Further simplifications and rewrites are applied, including the use of `LN_MUL`, `FACT_LT`, and `REAL_OF_NUM_LT` to handle logarithmic and arithmetic expressions.
* The proof concludes with `REAL_ARITH_TAC`, which presumably resolves any remaining arithmetic equalities.

### Mathematical insight
This theorem provides a relationship between successive terms of the `stirling` sequence, which is likely related to Stirling numbers or the Stirling approximation. The expression involving logarithms and arithmetic operations suggests a connection to asymptotic analysis or combinatorial identities.

### Dependencies
* `stirling`
* `REAL_ARITH`
* `LN_MUL`
* `FACT_LT`
* `REAL_OF_NUM_LT`
* `ADD_EQ_0`
* `ARITH`
* `LT_NZ`
* `REAL_OF_NUM_ADD`
* `REWRITE_RULE`
* `ADD1`
* `FACT`
* `GSYM`
* `REAL_OF_NUM_MUL`
* `LN_DIV`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of real arithmetic, logarithms, and the specific `stirling` function. Ensure that the target system can handle the required level of arithmetic and logical manipulation. Additionally, be mindful of potential differences in the treatment of binders, quantifiers, and the `MATCH_MP_TAC` tactic, which may require alternative approaches in other systems.

---

## STIRLING_DELTA_DERIV

### Name of formal statement
STIRLING_DELTA_DERIV

### Type of the formal statement
Theorem

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
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
```

### Informal statement
For all `x` greater than 0, the function `f(x) = ln((x + 1) / x) - 1 / (x + 1/2)` is differentiable at `x`, and its derivative is `-1 / (x * (x + 1) * (2 * x + 1)^2)`.

### Informal sketch
* The proof starts by assuming `x` is greater than 0.
* It then applies the `GEN_TAC` and `DISCH_TAC` tactics to set up the goal.
* The `DIFF_CONV` tactic is used to convert the differentiability statement into a more manageable form.
* The `REWRITE_TAC[IMP_IMP]` and `ANTS_TAC` tactics are used to break down the implication and handle the antecedent and consequent separately.
* The proof then proceeds by cases, using `REPEAT CONJ_TAC` and `MATCH_MP_TAC REAL_LT_DIV` to establish the necessary inequalities.
* The `AP_THM_TAC` and `AP_TERM_TAC` tactics are used to apply the `EQ_IMP` theorem and rearrange the terms.
* Finally, the `REWRITE_TAC[REAL_POW_2]` tactic is used to simplify the expression, and the `POP_ASSUM MP_TAC` and `CONV_TAC REAL_FIELD` tactics are used to discharge the assumption and convert the conclusion to a more convenient form.

### Mathematical insight
This theorem provides a derivative for a specific function related to Stirling's approximation, which is crucial in many mathematical and computational contexts, especially in approximating factorials. The derivative is essential for further calculations, such as optimization problems or numerical analysis.

### Dependencies
* `REAL_LT_DIV`
* `IMP_IMP`
* `EQ_IMP`
* `REAL_POW_2`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of differentiation and the specific form of the derivative. The `DIFF_CONV` tactic and the use of `REAL_POW_2` may require special care, as different systems may have different mechanisms for handling these concepts. Additionally, the use of `GEN_TAC` and `DISCH_TAC` may need to be adapted to the target system's approach to universal quantification and assumption discharge.

---

## STIRLING_DELTA_LIMIT

### Name of formal statement
STIRLING_DELTA_LIMIT

### Type of the formal statement
Theorem

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
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC])
```

### Informal statement
For all natural numbers `n`, the limit as `n` approaches infinity of the function `ln((n + 1) / n) - 1 / (n + 1/2)` approaches 0.

### Informal sketch
* The proof involves showing the limit of a sequence approaches 0 by applying various mathematical properties and theorems.
* It starts with a `GEN_REWRITE_TAC` to transform the expression into a more suitable form for limit analysis.
* The `MATCH_MP_TAC SEQ_SUB` and `MATCH_MP_TAC SEQ_LE_0` tactics are used to establish the sequence's behavior, utilizing the `EXISTS_TAC` to introduce a function `1/n` and `EXISTS_TAC 1` to set a lower bound.
* The proof then proceeds with a series of simplifications and applications of real arithmetic properties, including `REAL_ARITH`, `LN_POS`, `LN_LE`, and `REAL_LE_DIV`, to establish the limit's approach to 0.
* Key steps involve manipulating the expression to apply these properties, ultimately leading to the conclusion that the limit approaches 0.

### Mathematical insight
This theorem is related to Stirling's approximation, which is a method for approximating the factorial of a number. The limit in question is part of the analysis of the asymptotic behavior of this approximation. Understanding such limits is crucial for analyzing the accuracy and applicability of Stirling's approximation in various mathematical and computational contexts.

### Dependencies
* Theorems:
  + `SEQ_SUB`
  + `SEQ_LE_0`
  + `LN_POS`
  + `LN_LE`
  + `REAL_LE_DIV`
  + `REAL_ARITH`
* Definitions:
  + `REAL_OF_NUM_LE`
  + `GSYM REAL_SUB_RZERO`
  + `SEQ_HARMONIC`
  + `REAL_FIELD`
  + `REAL_LE_RDIV_EQ`
  + `REAL_LE_INV2`
  + `REAL_MUL_LID`
  + `real_div`

### Porting notes
When porting this theorem to another proof assistant, pay special attention to the handling of limits, sequences, and real arithmetic properties. The use of `GEN_REWRITE_TAC`, `MATCH_MP_TAC`, and `EXISTS_TAC` may need to be adapted to the target system's tactic language. Additionally, ensure that the target system has equivalent theorems and definitions for sequence limits, real arithmetic, and logarithmic properties.

---

## STIRLING_DECREASES

### Name of formal statement
STIRLING_DECREASES

### Type of the formal statement
Theorem

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
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers $n$, the inequality $\text{stirling}(n + 1) < \text{stirling}(n)$ holds.

### Informal sketch
* Start with the assumption that $n$ is not equal to $0$.
* Apply the definition of `stirling` and simplify using `STIRLING_DIFF`.
* Utilize `REAL_SUB_LT` and `REAL_MUL_SYM` to manipulate the inequality.
* Employ `POSITIVE_DIFF_LEMMA` with a witness function to establish the inequality.
* Use `STIRLING_DELTA_DERIV` and `STIRLING_DELTA_LIMIT` to analyze the behavior of the `stirling` function.
* Perform case analysis and apply `REAL_ARITH` to simplify the inequality.
* Apply `REAL_LT_MUL` and `REAL_LT_INV_EQ` to finalize the proof.

### Mathematical insight
The `STIRLING_DECREASES` theorem provides insight into the behavior of the `stirling` function, showing that it decreases as the input increases, for non-zero natural numbers. This property is important for understanding the growth rate of the `stirling` function and its applications in combinatorics and analysis.

### Dependencies
* `STIRLING_DIFF`
* `POSITIVE_DIFF_LEMMA`
* `STIRLING_DELTA_DERIV`
* `STIRLING_DELTA_LIMIT`
* `REAL_ARITH`
* `REAL_LT_MUL`
* `REAL_LT_INV_EQ`
* `REAL_SUB_LT`
* `REAL_MUL_SYM`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of real arithmetic and the `stirling` function. The `REAL_ARITH` and `REAL_LT_MUL` tactics may need to be replaced with equivalent tactics or libraries in the target system. Additionally, the `STIRLING_DIFF`, `STIRLING_DELTA_DERIV`, and `STIRLING_DELTA_LIMIT` definitions and lemmas may require careful translation to ensure that the ported theorem is equivalent to the original.

---

## OTHER_DERIV_LEMMA

### Name of formal statement
OTHER_DERIV_LEMMA

### Type of the formal statement
Theorem

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
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
```

### Informal statement
For all `x`, if `0` is less than `x`, then the derivative of the function `f(x) = 1 / (12 * x * (x + 1) * (x + 1/2))` at `x` is equal to `-(3 * x^2 + 3 * x + 1/2) / (12 * (x * (x + 1) * (x + 1/2))^2)`.

### Informal sketch
* The proof starts by assuming `0 < x` and then applies the `DIFF_CONV` tactic to the function `f(x) = 1 / (12 * x * (x + 1) * (x + 1/2))` to find its derivative.
* The `REWRITE_TAC[IMP_IMP]` and `ANTS_TAC` tactics are used to simplify the implication and apply the `EQ_IMP` theorem.
* The `AP_THM_TAC` and `AP_TERM_TAC` tactics are used to apply the `REAL_POW_2` theorem and rewrite the expression.
* The final steps involve simplifying the expression using `ARITH_TAC` and `CONV_TAC REAL_FIELD`.

### Mathematical insight
This theorem provides a derivative of a specific rational function, which is useful in various mathematical and scientific applications, such as optimization and physics. The proof demonstrates how to apply various mathematical concepts, such as differentiation and algebraic manipulation, to derive the derivative of a complex function.

### Dependencies
* Theorems:
	+ `IMP_IMP`
	+ `EQ_IMP`
	+ `REAL_ENTIRE`
	+ `REAL_POW_2`
* Tactics:
	+ `DIFF_CONV`
	+ `REWRITE_TAC`
	+ `ANTS_TAC`
	+ `MATCH_MP_TAC`
	+ `AP_THM_TAC`
	+ `AP_TERM_TAC`
	+ `CONV_TAC REAL_FIELD`

### Porting notes
When porting this theorem to other proof assistants, note that the `DIFF_CONV` tactic may need to be replaced with a similar tactic or a manual proof of the derivative. Additionally, the `REAL_FIELD` and `REAL_POW_2` theorems may need to be imported or proved separately. The `REPEAT STRIP_TAC` and `W` tactics may also need to be adapted to the target proof assistant's syntax and tactics.

---

## STIRLING_INCREASES

### Name of formal statement
STIRLING_INCREASES

### Type of the formal statement
Theorem

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
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers `n`, the inequality `stirling(n + 1) - 1 / (12 * (n + 1)) > stirling(n) - 1 / (12 * n)` holds.

### Informal sketch
* The proof starts by rewriting the given inequality using `REAL_OF_NUM_EQ` and `REAL_OF_NUM_ADD`.
* It then applies `REAL_ARITH` to transform the inequality into a more manageable form.
* The `SIMP_TAC` with `REAL_FIELD` and `STIRLING_DIFF` simplifies the expression further.
* The proof proceeds with a series of `REWRITE_TAC` and `SIMP_TAC` applications to manipulate the inequality.
* The `MATCH_MP_TAC POSITIVE_DIFF_LEMMA` and `EXISTS_TAC` introduce a witness term to establish the inequality.
* The subsequent steps involve `CONJ_TAC`, `GEN_REWRITE_TAC`, and `MATCH_MP_TAC` to further simplify and prove the inequality.
* Key tactics include `REAL_ARITH`, `REAL_LT_RDIV_EQ`, `REAL_INV_MUL`, and `REAL_MUL_LID`, which are used to manipulate and simplify the expressions.
* The proof also involves `SEQ_SUB`, `STIRLING_DELTA_LIMIT`, and `SEQ_HARMONIC`, which are used to establish the limit and sequence properties.

### Mathematical insight
The `STIRLING_INCREASES` theorem provides an inequality involving the Stirling numbers, which are used to approximate factorials. The theorem shows that the difference between consecutive Stirling numbers, normalized by a factor, increases as `n` increases. This result has implications for the asymptotic behavior of Stirling numbers and their applications in combinatorics and analysis.

### Dependencies
* `REAL_OF_NUM_EQ`
* `REAL_OF_NUM_ADD`
* `REAL_ARITH`
* `STIRLING_DIFF`
* `STIRLING_DELTA_LIMIT`
* `SEQ_SUB`
* `SEQ_HARMONIC`
* `POSITIVE_DIFF_LEMMA`
* `REAL_FIELD`
* `REAL_LT_RDIV_EQ`
* `REAL_INV_MUL`
* `REAL_MUL_LID`

### Porting notes
When porting this theorem to other proof assistants, attention should be paid to the manipulation of real numbers and the use of `REAL_ARITH` and `REAL_FIELD` tactics. The `STIRLING_DIFF` and `STIRLING_DELTA_LIMIT` theorems may require special attention, as they involve specific properties of Stirling numbers. Additionally, the `SEQ_SUB` and `SEQ_HARMONIC` theorems may need to be adapted to the target proof assistant's sequence and limit libraries.

---

## STIRLING_UPPERBOUND

### Name of formal statement
STIRLING_UPPERBOUND

### Type of the formal statement
Theorem

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
  ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the `stirling` function applied to the successor of `n` is less than or equal to 1.

### Informal sketch
* The proof proceeds by induction on `n`.
* In the base case, the `stirling` function is rewritten and simplified using `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV`.
* The inductive step uses `REAL_LE_TRANS` to establish a transitive inequality, with `stirling(SUC n)` as an intermediate value.
* The `STIRLING_DECREASES` theorem is applied to show that `stirling(SUC n)` is less than `stirling(SUC (SUC n))`, which is then used to establish the desired inequality.
* Arithmetic properties are used to simplify expressions and establish the final result.

### Mathematical insight
This theorem provides an upper bound for the `stirling` function, which is crucial in understanding its behavior and convergence properties. The `stirling` function is likely related to Stirling numbers, which appear in various combinatorial and asymptotic contexts.

### Dependencies
* Theorems:
	+ `STIRLING_DECREASES`
	+ `REAL_LE_TRANS`
	+ `REAL_LT_IMP_LE`
* Definitions:
	+ `stirling`
* Axioms and rules:
	+ `INDUCT_TAC`
	+ `MATCH_MP_TAC`
	+ `EXISTS_TAC`
	+ `ASM_REWRITE_TAC`
	+ `ARITH_RULE`
	+ `NUM_REDUCE_CONV`
	+ `REAL_RAT_REDUCE_CONV`

### Porting notes
When translating this theorem to other proof assistants, attention should be paid to the handling of induction, transitive inequalities, and arithmetic properties. The `STIRLING_DECREASES` theorem and the `stirling` function definition will need to be ported as well. Additionally, the use of `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV` may require equivalent convolution or simplification mechanisms in the target system.

---

## STIRLING_LOWERBOUND

### Name of formal statement
STIRLING_LOWERBOUND

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC STIRLING_INCREASES THEN ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the inequality `1 <= stirling(SUC n)` holds, where `stirling` denotes the Stirling function and `SUC n` represents the successor of `n`.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce a universal quantifier over `n`.
* It then uses `MATCH_MP_TAC REAL_LE_TRANS` to apply a transitive property of less-than-or-equal-to, introducing an intermediate value `stirling(SUC n) - &1 / (&12 * &(SUC n))`.
* The proof proceeds by cases, using `CONJ_TAC` and `INDUCT_TAC` for induction over `n`.
* In the base case, it simplifies the `stirling` function and applies various rewrite rules (`REAL_ARITH`, `real_div`, `REAL_MUL_LID`, `REAL_LE_INV_EQ`, `REAL_OF_NUM_MUL`, `REAL_POS`) to establish the base case inequality.
* In the inductive step, it applies `MATCH_MP_TAC REAL_LE_TRANS` again, introducing another intermediate value, and then uses `MATCH_MP_TAC` with `STIRLING_INCREASES` to leverage the increasing property of the `stirling` function.
* The proof concludes with arithmetic manipulations using `ARITH_TAC`.

### Mathematical insight
This theorem provides a lower bound for the `stirling` function, which is crucial in various mathematical contexts, such as asymptotic analysis and combinatorics. The `stirling` function is used to approximate factorials, and understanding its bounds is essential for many applications.

### Dependencies
* `REAL_LE_TRANS`
* `stirling`
* `STIRLING_INCREASES`
* `REAL_ARITH`
* `real_div`
* `REAL_MUL_LID`
* `REAL_LE_INV_EQ`
* `REAL_OF_NUM_MUL`
* `REAL_POS`
* `LN_1`
* `NUM_REDUCE_CONV`
* `REAL_RAT_REDUCE_CONV`
* `ARITH_RULE` 

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of real arithmetic and the `stirling` function. The `MATCH_MP_TAC` and `GEN_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `INDUCT_TAC` and `CONJ_TAC` tactics may require adjustments to accommodate differences in the inductive reasoning and conjunction handling between HOL Light and the target system.

---

## STIRLING_MONO

### Name of formal statement
STIRLING_MONO

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[ADD1; REAL_LT_IMP_LE; STIRLING_DECREASES; ADD_EQ_0])
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is not equal to 0 and `m` is less than or equal to `n`, then `stirling(n)` is less than or equal to `stirling(m)`.

### Informal sketch
* The proof starts by assuming the existence of `m` and `n` such that `m` is not 0 and `m` is less than or equal to `n`.
* It then uses the `LE_EXISTS` rule to introduce a witness `d` such that `n = m + d`.
* The proof proceeds by induction, using the `INDUCT_TAC` tactic to break down the problem into smaller sub-problems.
* The base case is handled using `REWRITE_TAC` with `ADD_CLAUSES` and `REAL_LE_REFL`.
* The inductive step uses `MATCH_MP_TAC` with `REAL_LE_TRANS` to establish a transitive inequality.
* The `EXISTS_TAC` tactic is used to introduce an intermediate value `stirling(m + d)`.
* Finally, `ASM_SIMP_TAC` is used to simplify the resulting expression using various properties, including `ADD1`, `REAL_LT_IMP_LE`, `STIRLING_DECREASES`, and `ADD_EQ_0`.

### Mathematical insight
This theorem establishes a monotonicity property of the `stirling` function, which is likely used in a broader context to reason about combinatorial or number-theoretic properties. The `stirling` function is often used to count the number of ways to partition a set, and this theorem may be used to establish bounds or limits on these counts.

### Dependencies
* `LE_EXISTS`
* `ADD_CLAUSES`
* `REAL_LE_REFL`
* `REAL_LE_TRANS`
* `ADD1`
* `REAL_LT_IMP_LE`
* `STIRLING_DECREASES`
* `ADD_EQ_0`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of quantifiers, induction, and the `EXISTS_TAC` tactic. The `STIRLING_DECREASES` property may need to be defined or imported separately, and the `REWRITE_TAC` and `ASM_SIMP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `INDUCT_TAC` tactic may need to be replaced with a more explicit induction principle, depending on the target system's support for induction.

---

## STIRLING_CONVERGES

### Name of formal statement
STIRLING_CONVERGES

### Type of the formal statement
Theorem

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
           STIRLING_UPPERBOUND; STIRLING_LOWERBOUND])
```

### Informal statement
There exists a real number `c` such that the `stirling` sequence converges to `c`. This involves showing that the sequence is bounded and monotonic, leveraging properties of `mono`, `real_ge`, `STIRLING_MONO`, `MR1_BOUNDED`, and the bounds established by `STIRLING_UPPERBOUND` and `STIRLING_LOWERBOUND`.

### Informal sketch
* The proof begins by applying `SEQ_SUC` to establish a relationship between the `stirling` sequence and its convergence.
* It then utilizes `GSYM convergent` to relate the sequence's convergence to the concept of convergence in general.
* The `SEQ_BCONV` theorem is applied to establish that the sequence is convergent if it is bounded and monotonic.
* The proof splits into two main parts: one showing the sequence is bounded, and the other that it is monotonic.
* For boundedness, `MR1_BOUNDED`, `GE`, and `LE_REFL` are used to establish that the sequence is bounded within certain limits.
* For monotonicity, `STIRLING_MONO` is key, showing that the sequence increases in a manner that supports convergence.
* The proof concludes by demonstrating that there exists a real number `&2` (greater than 0) such that the absolute value of the sequence terms is less than `&2`, using `REAL_ARITH`, `STIRLING_UPPERBOUND`, and `STIRLING_LOWERBOUND` to finalize the convergence argument.

### Mathematical insight
This theorem is crucial for establishing the convergence of the `stirling` sequence, which is significant in mathematics for approximating factorials. The proof's structure highlights the importance of boundedness and monotonicity in ensuring convergence, leveraging key properties of real sequences and specific bounds related to the `stirling` sequence.

### Dependencies
* Theorems:
  - `SEQ_BCONV`
  - `STIRLING_MONO`
  - `MR1_BOUNDED`
* Definitions:
  - `stirling`
  - `mono`
  - `real_ge`
  - `STIRLING_UPPERBOUND`
  - `STIRLING_LOWERBOUND`
* Axioms/Inductive rules: None explicitly mentioned, but the use of `SEQ_SUC` and `GSYM convergent` implies reliance on foundational properties of sequences and convergence.

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles sequence convergence, boundedness, and monotonicity. The `STIRLING_MONO`, `MR1_BOUNDED`, `STIRLING_UPPERBOUND`, and `STIRLING_LOWERBOUND` will need to be defined or imported appropriately, considering the target system's libraries and syntax for real analysis and sequence properties. Additionally, the tactic structure may need to be adapted, as direct translations of tactics like `ONCE_REWRITE_TAC` or `MATCH_MP_TAC` might not be available or might work differently in the target system.

---

## [PI2_LT;

### Name of formal statement
PI2_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let [PI2_LT; PI2_LE; PI2_NZ] = (CONJUNCTS o prove)
 (`&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)`,
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
There exist three statements: `PI2_LT`, `PI2_LE`, and `PI2_NZ`, which are proven to be true. These statements assert that 0 is less than pi divided by 2, 0 is less than or equal to pi divided by 2, and pi divided by 2 is not equal to 0, respectively.

### Informal sketch
* The proof begins by using the `MP_TAC` tactic with `PI_POS` to establish a foundation for the subsequent reasoning steps.
* Then, `REAL_ARITH_TAC` is applied to perform real arithmetic manipulations, which helps derive the required inequalities and equality involving pi.
* The `CONJUNCTS` function is used to extract the individual conclusions from the proof, which are the three statements `PI2_LT`, `PI2_LE`, and `PI2_NZ`.

### Mathematical insight
This formal item is important because it establishes fundamental properties of pi, which is a crucial constant in mathematics. The inequalities and non-equality statement provide a foundation for further reasoning about pi and its relationships with other mathematical objects. The use of `PI_POS` as a premise suggests that this theorem is part of a larger development of pi's properties, where `PI_POS` is a previously established fact.

### Dependencies
* Theorems:
	+ `PI_POS`
* Definitions:
	+ `pi`
* Tactics:
	+ `MP_TAC`
	+ `REAL_ARITH_TAC`

### Porting notes
When translating this item into other proof assistants, pay attention to the handling of real arithmetic and the specific tactics used. The `MP_TAC` and `REAL_ARITH_TAC` tactics may have counterparts in other systems, but their exact behavior and requirements might differ. Additionally, the representation of pi and the `CONJUNCTS` function may need to be adapted to the target system's syntax and semantics.

---

## WALLIS_PARTS

### Name of formal statement
WALLIS_PARTS

### Type of the formal statement
Theorem

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
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN SIMP_TAC[PI2_LE])
```

### Informal statement
For all natural numbers `n`, the following equation holds: 
(`&n + &2`) times the integral from `0` to `pi/2` of `sin(x)` raised to the power of `n + 2` equals (`&n + &1`) times the integral from `0` to `pi/2` of `sin(x)` raised to the power of `n`.

### Informal sketch
* The proof begins with a generalization over `n`, then applies the `INTEGRAL_BY_PARTS` tactic to transform the integral expression.
* It proceeds to simplify and manipulate the resulting expression using various `REWRITE_TAC` and `SIMP_TAC` steps, leveraging properties of real numbers, trigonometric functions, and integration.
* Key steps involve recognizing the relationship between `sin(x)` and `cos(x)` through the `SIN_CIRCLE` theorem, and applying `INTEGRAL_CMUL` and `INTEGRAL_SUB` to further simplify the integral expressions.
* The proof concludes by demonstrating the equivalence of the initial and final expressions through a series of logical manipulations and applications of `REAL_ARITH_TAC` for arithmetic reasoning.

### Mathematical insight
This theorem relates the integrals of powers of `sin(x)` over the interval `[0, pi/2]`, providing a recurrence relation that can be used to compute these integrals for arbitrary natural numbers `n`. The relationship is fundamental in various mathematical and physical applications, particularly in the study of trigonometric functions and their integrals.

### Dependencies
#### Theorems
* `INTEGRAL_BY_PARTS`
* `SIN_CIRCLE`
* `REAL_LT_IMP_LE`
* `PI_POS`
* `REAL_LT_DIV`
* `REAL_OF_NUM_LT`
* `ARITH`
* `INTEGRAL_CMUL`
* `INTEGRAL_SUB`
#### Definitions
* `sin`
* `cos`
* `integral`
* `real_pow`

---

## WALLIS_PARTS'

### Name of formal statement
WALLIS_PARTS'

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_PARTS' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MP_TAC WALLIS_PARTS THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all natural numbers $n$, the integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)$ raised to the power of $n + 2$ is equal to $\frac{n + 1}{n + 2}$ times the integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)$ raised to the power of $n$.

### Informal sketch
* The proof starts by applying the `WALLIS_PARTS` theorem using `MP_TAC`, which is likely a modus ponens tactic.
* Then, it applies `MATCH_MP_TAC MONO_FORALL` to handle the universal quantification over $n$, utilizing a monotonicity property for the universal quantifier.
* The `CONV_TAC REAL_FIELD` tactic is used for converting the expression to a form suitable for real numbers, possibly simplifying or rearranging terms to fit the real field.
* The main logical stages involve recognizing the relationship between the integrals of $\sin(x)$ raised to different powers and applying the `WALLIS_PARTS` theorem to establish this relationship.

### Mathematical insight
This theorem provides a recurrence relation for integrals of powers of the sine function over the interval from $0$ to $\frac{\pi}{2}$. It's a key step in evaluating such integrals, which are important in various mathematical and physical contexts, such as calculus, trigonometry, and signal processing. The theorem's importance lies in its ability to reduce the evaluation of higher-power sine integrals to the evaluation of lower-power ones, facilitating the computation of these integrals.

### Dependencies
* Theorems:
  - `WALLIS_PARTS`
  - `MONO_FORALL`
* Definitions and tactics:
  - `MP_TAC`
  - `MATCH_MP_TAC`
  - `CONV_TAC`
  - `REAL_FIELD`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles universal quantification, modus ponens, and the conversion of expressions for real numbers. The `WALLIS_PARTS` theorem and `MONO_FORALL` property may need to be established or imported first, depending on the target system's library. Additionally, the tactic scripts may differ significantly between systems, requiring a good understanding of the underlying mathematical structure and the proof assistant's tactic language.

---

## WALLIS_0

### Name of formal statement
WALLIS_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_0 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2`,
  REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
  SIMP_TAC[INTEGRAL_CONST; REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV;
           REAL_OF_NUM_LT; ARITH; REAL_MUL_LID; REAL_SUB_RZERO])
```

### Informal statement
The definite integral from 0 to π/2 of the function sin(x) raised to the power of 0 is equal to π/2.

### Informal sketch
* The proof starts with the definition of the integral and the fact that `sin(x) pow 0` simplifies to 1, since any non-zero number raised to the power of 0 is 1.
* The `REWRITE_TAC` tactic is used to apply several simplification rules, including `real_pow`, `REAL_DIV_1`, and `REAL_MUL_LID`, to rewrite the integral in a more manageable form.
* The `SIMP_TAC` tactic is then applied with a list of theorems, including `INTEGRAL_CONST`, `REAL_LT_IMP_LE`, `PI_POS`, `REAL_LT_DIV`, `REAL_OF_NUM_LT`, `ARITH`, `REAL_MUL_LID`, and `REAL_SUB_RZERO`, to simplify the expression further and ultimately prove the equality.

### Mathematical insight
This theorem provides a basic property of definite integrals, specifically for a constant function over a given interval. The result is intuitive since the integral of 1 over any interval is the length of that interval. In this case, the length of the interval from 0 to π/2 is π/2, which is the expected result.

### Dependencies
* Theorems:
  * `real_pow`
  * `REAL_DIV_1`
  * `REAL_MUL_LID`
  * `INTEGRAL_CONST`
  * `REAL_LT_IMP_LE`
  * `PI_POS`
  * `REAL_LT_DIV`
  * `REAL_OF_NUM_LT`
  * `ARITH`
  * `REAL_MUL_LID`
  * `REAL_SUB_RZERO`
* Definitions:
  * `integral`
  * `sin`
  * `pow`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how the system handles definite integrals, the simplification of `sin(x) pow 0`, and the application of the various theorems listed in the `SIMP_TAC` tactic. The key challenge will be ensuring that the target system's simplification and rewriting mechanisms can replicate the steps taken in the HOL Light proof, potentially requiring custom tactics or strategic use of the system's automation features.

---

## WALLIS_1

### Name of formal statement
WALLIS_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_1 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 1) = &1`,
  MATCH_MP_TAC DEFINT_INTEGRAL THEN REWRITE_TAC[PI2_LE; REAL_POW_1] THEN
  MP_TAC(SPECL [`\x. --cos(x)`; `\x. sin x`; `&0`; `pi / &2`] FTC1) THEN
  REWRITE_TAC[COS_0; COS_PI2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC)
```

### Informal statement
The definite integral from 0 to π/2 of sin(x) is equal to 1.

### Informal sketch
* The proof begins by applying the `DEFINT_INTEGRAL` definition to express the integral in a form that can be manipulated.
* It then uses `FTC1` (the Fundamental Theorem of Calculus, part 1) with specific functions `-\cos(x)` and `sin(x)`, and limits `0` and `π/2`, to relate the integral to the evaluation of a function.
* The `COS_0` and `COS_PI2` theorems are used to simplify the expression involving cosine at 0 and π/2.
* Further simplifications are made using `REAL_RAT_REDUCE_CONV` to reduce rational expressions and `REAL_ARITH_TAC` to perform real arithmetic, ultimately showing the integral equals 1.

### Mathematical insight
This theorem is a fundamental result in calculus, demonstrating the relationship between the sine function and its antiderivative over a specific interval. It is a key example of applying the Fundamental Theorem of Calculus to evaluate definite integrals.

### Dependencies
* Theorems:
  - `DEFINT_INTEGRAL`
  - `FTC1`
  - `COS_0`
  - `COS_PI2`
* Definitions:
  - `REAL_POW_1`
  - `PI2_LE`
* Tactics and Conversions:
  - `MATCH_MP_TAC`
  - `REWRITE_TAC`
  - `MP_TAC`
  - `CONV_TAC`
  - `REAL_RAT_REDUCE_CONV`
  - `DISCH_THEN`
  - `REPEAT`
  - `STRIP_TAC`
  - `DIFF_TAC`
  - `REAL_ARITH_TAC`

---

## WALLIS_EVEN

### Name of formal statement
WALLIS_EVEN

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all natural numbers `n`, the definite integral from `0` to `π/2` of `sin(x)` raised to the power of `2n` is equal to `((2n)! / (2^n * n!)^2) * π/2`.

### Informal sketch
* The proof starts with an induction over `n`, using `INDUCT_TAC`.
* The base case involves simplifying the expression using `CONV_TAC NUM_REDUCE_CONV` and `CONV_TAC REAL_RAT_REDUCE_CONV`, and then applying `WALLIS_0` and `REAL_ARITH_TAC`.
* The inductive step uses `ASM_REWRITE_TAC` to apply `ARITH_RULE` and `WALLIS_PARTS'`, followed by various rewrites and applications of `AP_THM_TAC` and `AP_TERM_TAC`.
* Key rewrites involve `REAL_MUL_ASSOC`, `FACT`, `real_pow`, and `REAL_OF_NUM_MUL`.
* The proof also uses `GEN_REWRITE_TAC` with `REAL_POW_MUL` and simplifications involving `real_div`, `REAL_INV_MUL`, and `REAL_MUL_ASSOC`.
* The final steps involve further rewrites and applications of `AP_THM_TAC` and `AP_TERM_TAC`, ultimately concluding with `CONV_TAC REAL_FIELD`.

### Mathematical insight
This theorem provides a closed-form expression for a specific definite integral involving `sin(x)` raised to an even power, which is a classic result in mathematics. The proof demonstrates a combination of algebraic manipulations, arithmetic properties, and careful application of mathematical theorems to derive the result.

### Dependencies
* Theorems:
	+ `WALLIS_0`
	+ `WALLIS_PARTS'`
	+ `FACT`
	+ `real_pow`
	+ `REAL_OF_NUM_MUL`
	+ `REAL_POW_MUL`
* Definitions:
	+ `integral`
	+ `sin`
	+ `pow`
* Inductive rules:
	+ `INDUCT_TAC`

---

## WALLIS_ODD

### Name of formal statement
WALLIS_ODD

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all natural numbers `n`, the definite integral from 0 to π/2 of `sin(x)` raised to the power of `2n + 1` is equal to `((2^n * n!)^2) / (2n + 1)!`.

### Informal sketch
* The proof starts by applying induction on `n`.
* The base case involves simplifying the expression using `NUM_REDUCE_CONV`, `REAL_RAT_REDUCE_CONV`, and `WALLIS_1`.
* The inductive step involves rewriting the expression using `ARITH_RULE`, `WALLIS_PARTS`, and various properties of real numbers and factorials.
* Key steps include applying `GEN_REWRITE_TAC` with `REAL_MUL_SYM`, rewriting with `FACT`, `real_pow`, and `GSYM REAL_OF_NUM_MUL`.
* The proof also involves using `ONCE_REWRITE_TAC` with `REAL_ARITH`, `GEN_REWRITE_TAC` with `REAL_POW_MUL`, and `AP_TERM_TAC`.
* The final steps involve rewriting with `real_div`, `GSYM REAL_MUL_ASSOC`, and applying `MP_TAC` with `SPEC` and `FACT_LT`.

### Mathematical insight
This theorem provides a closed-form expression for a specific definite integral involving powers of sine, which is a fundamental result in mathematics and has applications in various fields such as calculus, analysis, and physics. The proof demonstrates a sophisticated use of mathematical induction, algebraic manipulations, and properties of real numbers and factorials.

### Dependencies
* `WALLIS_1`
* `WALLIS_PARTS`
* `FACT`
* `FACT_LT`
* `REAL_OF_NUM_MUL`
* `REAL_OF_NUM_ADD`
* `REAL_OF_NUM_SUC`
* `REAL_POW_2`
* `REAL_MUL_SYM`
* `REAL_ARITH`
* `NUM_REDUCE_CONV`
* `REAL_RAT_REDUCE_CONV`
* `GEN_REWRITE_TAC`
* `ONCE_REWRITE_TAC`
* `AP_TERM_TAC`
* `MP_TAC` 

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of binders, induction, and real number arithmetic. The use of `GEN_REWRITE_TAC` and `ONCE_REWRITE_TAC` may need to be adapted to the target system's rewriting mechanisms. Additionally, the `REAL_FIELD` convolution may require careful handling of non-standard real number representations.

---

## WALLIS_QUOTIENT

### Name of formal statement
WALLIS_QUOTIENT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_EVEN; WALLIS_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_POW_INV; REAL_INV_INV] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers n, the quotient of the integral from 0 to π/2 of sin(x) raised to the power of 2n and the integral from 0 to π/2 of sin(x) raised to the power of 2n+1 is equal to the product of the factorial of 2n and the factorial of 2n+1, divided by the product of 2 raised to the power of n, the factorial of n, all raised to the power of 4, and then multiplied by π/2.

### Informal sketch
* The proof starts by applying the `GEN_TAC` tactic to introduce a universal quantifier for n.
* It then uses `REWRITE_TAC` with `WALLIS_EVEN` and `WALLIS_ODD` to rewrite the integrals in terms of known expressions.
* Further simplification is achieved by applying `REWRITE_TAC` with `real_div`, `REAL_INV_MUL`, `GSYM REAL_POW_INV`, and `REAL_INV_INV` to manipulate the real-valued expressions.
* The final step involves `REAL_ARITH_TAC` to perform real arithmetic and simplify the expression to the desired form.
* The key steps involve recognizing the patterns that allow the application of `WALLIS_EVEN` and `WALLIS_ODD`, and then carefully simplifying the resulting expressions using real arithmetic properties.

### Mathematical insight
This theorem relates to the Wallis product, a famous result in mathematics that provides an infinite product representation for π. The theorem here specifically deals with the quotient of two integrals involving powers of sine, which is crucial for deriving the Wallis product formula. Understanding this theorem requires recognizing how the factorial expressions and the powers of 2 and π relate to the integrals of sine functions over specific intervals.

### Dependencies
* `WALLIS_EVEN`
* `WALLIS_ODD`
* `real_div`
* `REAL_INV_MUL`
* `GSYM REAL_POW_INV`
* `REAL_INV_INV`
* `FACT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles real arithmetic, integration, and factorial functions. The `REAL_ARITH_TAC` and `REWRITE_TAC` tactics have counterparts in other systems, but the specific syntax and application may differ. Additionally, the representation of the `WALLIS_EVEN` and `WALLIS_ODD` theorems, as well as the `FACT` function, will need to be appropriately defined or imported in the target system.

---

## WALLIS_QUOTIENT'

### Name of formal statement
WALLIS_QUOTIENT'

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_QUOTIENT] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM REAL_INV_DIV] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
  MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD)
```

### Informal statement
For all natural numbers n, the quotient of the integral from 0 to π/2 of sin(x) raised to the power of 2n and the integral from 0 to π/2 of sin(x) raised to the power of 2n+1, multiplied by 2/π, is equal to the product of the factorial of 2n and the factorial of 2n+1, divided by the fourth power of the product of 2 raised to the power of n and the factorial of n.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce a universal quantifier for n.
* It then uses `REWRITE_TAC` with `WALLIS_QUOTIENT` to rewrite the expression, followed by `GEN_REWRITE_TAC` with `GSYM REAL_INV_DIV` to manipulate the division.
* The `REWRITE_TAC` with `GSYM real_div` is applied to further simplify the expression.
* The proof then proceeds with `MATCH_MP_TAC REAL_DIV_RMUL` to handle the division, and `MP_TAC PI2_NZ` to utilize the fact that π/2 is non-zero.
* Finally, `CONV_TAC REAL_FIELD` is used to conclude the proof by applying properties of real numbers.

### Mathematical insight
This theorem provides a closed-form expression for the quotient of two integrals involving powers of sine, which is a fundamental result in mathematics and has applications in various fields such as calculus, analysis, and physics. The `WALLIS_QUOTIENT'` theorem is likely used to establish a connection between the given integrals and the factorial function, which is a crucial component in many mathematical derivations.

### Dependencies
* `WALLIS_QUOTIENT`
* `REAL_INV_DIV`
* `real_div`
* `REAL_DIV_RMUL`
* `PI2_NZ`
* `REAL_FIELD`
* `FACT`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of real numbers, division, and the factorial function. The `GEN_REWRITE_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `CONV_TAC REAL_FIELD` tactic may require manual instantiation of the real field properties in the target system.

---

## WALLIS_MONO

### Name of formal statement
WALLIS_MONO

### Type of the formal statement
Theorem

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
   REPEAT(POP_ASSUM MP_TAC) THEN MP_TAC PI2_LT THEN REAL_ARITH_TAC))
```

### Informal statement
For all real numbers $m$ and $n$ such that $m \leq n$, the definite integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^n$ is less than or equal to the definite integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^m$.

### Informal sketch
* The proof begins by assuming $m \leq n$ and aiming to show the inequality between the two integrals.
* It applies `INTEGRAL_LE` to establish the relationship between the integrals, leveraging the fact that $\sin(x)$ is non-negative over the interval $[0, \frac{\pi}{2}]$.
* The `CONV_TAC` with `INTEGRABLE_CONV` ensures the integrability of $\sin(x)^n$ and $\sin(x)^m$ over the given interval.
* The proof then simplifies using `REAL_POW_ADD` and `GSYM REAL_MUL_RID` to manipulate the expressions involving powers of $\sin(x)$.
* It applies `REAL_LE_LMUL` and uses `REAL_POW_LE` and `REAL_POW_1_LE` to reason about the monotonicity of $\sin(x)^n$ with respect to $n$.
* The `SIN_BOUNDS` and `SIN_POS_PI_LE` are used to establish bounds on $\sin(x)$ within the interval, which is crucial for comparing the integrals.
* The final steps involve arithmetic manipulations and applications of `PI2_LT` to conclude the proof.

### Mathematical insight
This theorem, `WALLIS_MONO`, captures a monotonic property of the integral of $\sin(x)^n$ over $[0, \frac{\pi}{2}]$ with respect to $n$. It's a key insight because it relates the behavior of these integrals as $n$ increases, which is useful in various mathematical and physical applications involving trigonometric functions and their powers.

### Dependencies
* Theorems:
  - `INTEGRAL_LE`
  - `REAL_LE_LMUL`
  - `REAL_POW_LE`
  - `REAL_POW_1_LE`
  - `SIN_BOUNDS`
  - `SIN_POS_PI_LE`
  - `PI2_LT`
* Definitions:
  - `integral`
  - `sin`
  - `pow`
  - `REAL_POW_ADD`
  - `GSYM REAL_MUL_RID`
* Tactics and Conversions:
  - `REWRITE_TAC`
  - `STRIP_TAC`
  - `ASM_REWRITE_TAC`
  - `MATCH_MP_TAC`
  - `CONV_TAC`
  - `GEN_REWRITE_TAC`
  - `MP_TAC`
  - `ANTS_TAC`
  - `REAL_ARITH_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how each system handles:
- Quantifiers and their scope
- Real-valued functions and their properties (e.g., `sin`, `pow`)
- Integral calculus and the specific properties of definite integrals (e.g., `INTEGRAL_LE`)
- Tactics for rewriting and simplifying expressions, especially those involving real numbers and inequalities (e.g., `REAL_LE_LMUL`, `REAL_POW_LE`)
- The representation of mathematical constants like $\pi$ and how they are manipulated in proofs (e.g., `PI2_LT`)
- Differences in automation levels and the need for explicit vs. implicit handling of certain properties or theorems.

---

## WALLIS_LT

### Name of formal statement
WALLIS_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_LT = prove
 (`!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MATCH_MP_TAC ODDEVEN_INDUCT THEN
  REWRITE_TAC[WALLIS_0; WALLIS_1; PI2_LT; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WALLIS_PARTS'] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers n, the integral from 0 to π/2 of sin(x) raised to the power of n is greater than 0.

### Informal sketch
* The proof uses `ODDEVEN_INDUCT` to proceed by induction on whether n is even or odd.
* It then applies various rewrites using `WALLIS_0`, `WALLIS_1`, `PI2_LT`, `REAL_OF_NUM_LT`, and `ARITH` to simplify the expression.
* After stripping and rewriting using `WALLIS_PARTS'`, it applies `REAL_LT_MUL` and `REAL_LT_DIV` to establish the inequality.
* The proof concludes with `REAL_ARITH_TAC`, which likely performs arithmetic reasoning to finalize the comparison.

### Mathematical insight
This theorem is related to Wallis' formula, which is an infinite product for π. The statement here specifically addresses the integrability and positivity of `sin(x)` raised to a power over a specific interval, laying groundwork for further results involving Wallis' formula and its applications.

### Dependencies
#### Theorems
* `ODDEVEN_INDUCT`
* `REAL_LT_MUL`
* `REAL_LT_DIV`
#### Definitions
* `WALLIS_0`
* `WALLIS_1`
* `PI2_LT`
* `REAL_OF_NUM_LT`
* `WALLIS_PARTS'`
#### Tactics
* `MATCH_MP_TAC`
* `REWRITE_TAC`
* `REPEAT`
* `STRIP_TAC`
* `ASM_REWRITE_TAC`
* `REAL_ARITH_TAC`

---

## WALLIS_NZ

### Name of formal statement
WALLIS_NZ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_NZ = prove
 (`!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)`,
  MP_TAC WALLIS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers n, the integral from 0 to π/2 of sin(x) raised to the power of n is not equal to 0.

### Informal sketch
* The proof starts by applying the `WALLIS_LT` theorem, which is likely related to the Wallis formula or a similar inequality.
* Then, it uses `MATCH_MP_TAC` to apply the `MONO_FORALL` rule, which is probably related to monotonicity or universal quantification.
* Finally, it applies `REAL_ARITH_TAC`, which suggests the use of real arithmetic tactics to simplify or evaluate the expression.
* The key idea is to leverage existing theorems and properties of integrals, trigonometric functions, and real arithmetic to establish the non-zero value of the integral.

### Mathematical insight
This theorem is likely related to the Wallis formula, which is a well-known result in mathematics for calculating π. The statement itself asserts that a specific integral is non-zero for all natural numbers n, which has implications for various mathematical constructions and proofs involving trigonometric functions and integration.

### Dependencies
* Theorems:
  + `WALLIS_LT`
* Tactics:
  + `MP_TAC`
  + `MATCH_MP_TAC`
  + `REAL_ARITH_TAC`
* Definitions:
  + `MONO_FORALL`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of universal quantification, real arithmetic, and trigonometric functions. The `MATCH_MP_TAC` and `MP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `REAL_ARITH_TAC` tactic might require manual rewriting or replacement with a similar tactic or a set of tactics that achieve the same effect in the target system.

---

## WALLIS_BOUNDS

### Name of formal statement
WALLIS_BOUNDS

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers $n$, the following inequalities hold:
1. The integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^{n+1}$ is less than or equal to the integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^n$.
2. The integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^n$ is less than or equal to $\frac{n+2}{n+1}$ times the integral from $0$ to $\frac{\pi}{2}$ of $\sin(x)^{n+1}$.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce a universal quantifier over $n$.
* It then uses `SIMP_TAC` with `WALLIS_MONO` and `LE_ADD` to simplify the statement.
* The `MATCH_MP_TAC REAL_LE_TRANS` tactic is applied to introduce a intermediate value for the inequality.
* An existential quantifier is introduced using `EXISTS_TAC` with the term `(&n + &2) / (&n + &1) * integral (&0,pi / &2) (\x. sin x pow (n + 2))`.
* The proof then proceeds by splitting into two cases using `CONJ_TAC`, and applying various simplification and arithmetic tactics to establish the inequalities.

### Mathematical insight
This theorem provides bounds on the integral of $\sin(x)^n$ over the interval $[0, \frac{\pi}{2}]$. The bounds are in terms of the integral of $\sin(x)^{n+1}$ and involve a simple rational function of $n$. This result is likely used in the proof of Wallis's formula, which is a famous result in mathematics for computing the value of $\pi$.

### Dependencies
* `WALLIS_MONO`
* `LE_ADD`
* `WALLIS_PARTS'`
* `REAL_LE_TRANS`
* `REAL_EQ_IMP_LE`
* `REAL_LE_LMUL`
* `REAL_LE_DIV`
* `ARITH_RULE`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of the `integral` function and the `pow` function, as well as the tactics `GEN_TAC`, `SIMP_TAC`, `MATCH_MP_TAC`, and `EXISTS_TAC`. The `CONV_TAC REAL_FIELD` tactic may also require special handling, as it is specific to HOL Light's real number implementation. Additionally, the `REAL_ARITH_TAC` tactic may need to be replaced with a similar tactic in the target proof assistant.

---

## WALLIS_RATIO_BOUNDS

### Name of formal statement
WALLIS_RATIO_BOUNDS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WALLIS_RATIO_BOUNDS = prove
 (`!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)`,
  GEN_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; WALLIS_LT; REAL_MUL_LID; WALLIS_BOUNDS];
    SIMP_TAC[REAL_LE_LDIV_EQ; WALLIS_LT; WALLIS_BOUNDS]])
```

### Informal statement
For all natural numbers `n`, the following inequality holds: `1` is less than or equal to the ratio of the integral from `0` to `π/2` of `sin(x)` raised to the power of `n` to the integral from `0` to `π/2` of `sin(x)` raised to the power of `n+1`, and this ratio is less than or equal to `(n + 2) / (n + 1)`.

### Informal sketch
* The proof involves establishing a double inequality for a specific ratio involving integrals of powers of `sin(x)`.
* It starts by applying `GEN_TAC` to introduce the variable `n`, followed by `CONJ_TAC` to split the goal into two separate inequalities.
* The left inequality is then proved using `SIMP_TAC` with a list of theorems including `REAL_LE_RDIV_EQ`, `WALLIS_LT`, `REAL_MUL_LID`, and `WALLIS_BOUNDS`.
* Similarly, the right inequality is proved using `SIMP_TAC` with a different arrangement of theorems: `REAL_LE_LDIV_EQ`, `WALLIS_LT`, and `WALLIS_BOUNDS`.
* The use of these specific tactics and theorems suggests that the proof relies on simplification and properties of real numbers, inequalities, and possibly previous results related to Wallis' formula or similar mathematical constructs.

### Mathematical insight
This theorem provides bounds on the ratio of successive integrals of powers of `sin(x)` over the interval from `0` to `π/2`. This is related to Wallis' formula, which is a famous result for the value of `π` expressed as an infinite product. The theorem's importance lies in its application to mathematical analysis, particularly in the study of trigonometric functions and their integrals. It demonstrates how mathematical induction and properties of real numbers can be used to establish non-trivial inequalities.

### Dependencies
* Theorems:
  - `REAL_LE_RDIV_EQ`
  - `WALLIS_LT`
  - `REAL_MUL_LID`
  - `WALLIS_BOUNDS`
  - `REAL_LE_LDIV_EQ`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of real numbers, inequalities, and the specific mathematical properties used (e.g., `WALLIS_LT`, `WALLIS_BOUNDS`). The porting process may require re-establishing these properties or using equivalent constructs available in the target system. Additionally, the automation level and tactic structure might differ, requiring adjustments to the proof script to align with the target system's proof assistant mechanisms.

---

## WALLIS

### Name of formal statement
WALLIS

### Type of the formal statement
Theorem

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
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the expression `((2^n * n!)^4 / (FACT(2*n) * FACT(2*n + 1)))` converges to `pi / 2`.

### Informal sketch
* The proof begins by applying `ONCE_REWRITE_TAC` with `GSYM REAL_INV_DIV` to transform the expression.
* Then, it uses `MATCH_MP_TAC` with `SEQ_INV` to establish the convergence of the sequence.
* The proof proceeds by applying various rewrite tactics, such as `REWRITE_TAC` with `GSYM WALLIS_QUOTIENT'` and `REAL_MUL_SYM`, to simplify the expression.
* The `GEN_REWRITE_TAC` with `RAND_CONV` and `GSYM REAL_MUL_RID` is used to further simplify the expression.
* The proof then applies `MATCH_MP_TAC` with `SEQ_MUL` and `SEQ_ADD` to establish the convergence of the sequence.
* The `EXISTS_TAC` is used to introduce a witness term, and `REWRITE_TAC` with `SEQ_HARMONIC` is applied to simplify the expression.
* The proof concludes by applying `MATCH_MP_TAC` with `REAL_LE_INV2` and `REAL_ARITH_TAC` to establish the final result.
* Key steps involve using `WALLIS_QUOTIENT'`, `SEQ_INV`, `SEQ_MUL`, `SEQ_ADD`, and `REAL_LE_INV2` to reason about the convergence of the sequence.

### Mathematical insight
The `WALLIS` theorem provides a famous infinite product representation for `pi`, which is a fundamental constant in mathematics. This theorem is important because it provides a way to compute `pi` using an infinite product, which can be useful in various mathematical and computational contexts. The proof of this theorem involves a series of intricate steps, including the use of various rewrite tactics and the application of key theorems such as `SEQ_INV` and `REAL_LE_INV2`.

### Dependencies
* Theorems:
	+ `SEQ_INV`
	+ `SEQ_MUL`
	+ `SEQ_ADD`
	+ `REAL_LE_INV2`
	+ `PI2_NZ`
* Definitions:
	+ `WALLIS_QUOTIENT'`
	+ `FACT`
	+ `SEQ_HARMONIC`
* Other:
	+ `REAL_ARITH`
	+ `REAL_FIELD`

---

## LN_WALLIS

### Name of formal statement
LN_WALLIS

### Type of the formal statement
Theorem

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
  REWRITE_TAC[REAL_MUL_RID])
```

### Informal statement
For all natural numbers `n`, the expression `4 * n * ln(2) + 4 * ln(FACT n) - (ln(FACT(2 * n)) + ln(FACT(2 * n + 1)))` converges to `ln(pi / 2)`.

### Informal sketch
* The proof begins by applying the `REWRITE_TAC` tactic to rearrange the terms in the expression using `REAL_ARITH`.
* It then uses `SUBGOAL_THEN` to establish that `2` raised to the power of `n` is greater than `0` for all `n`, which is used to simplify the expression using `SIMP_TAC` with various theorems such as `GSYM LN_POW`, `REAL_OF_NUM_LT`, and `FACT_LT`.
* The proof continues by applying `SIMP_TAC` again to simplify the expression further, and then uses `MATCH_MP_TAC` with `CONTL_SEQ` and `DIFF_CONT` to establish the convergence of the sequence.
* The `EXISTS_TAC` tactic is used to introduce `inv(pi / 2)` as a witness, and `MP_TAC` is applied with `DIFF_CONV` to establish the differentiability of the natural logarithm function.
* Finally, the proof concludes by applying `SIMP_TAC` with various theorems such as `ETA_AX`, `PI2_LT`, and `REAL_OF_NUM_LT` to simplify the expression and establish the convergence to `ln(pi / 2)`.

### Mathematical insight
This theorem provides a formal proof of Wallis' formula, which relates the limit of a particular sequence to the natural logarithm of `pi / 2`. The formula is a classic result in mathematics and has numerous applications in calculus and analysis. The proof demonstrates the power of formal reasoning in establishing mathematical results with high confidence.

### Dependencies
* Theorems:
	+ `REAL_ARITH`
	+ `GSYM LN_POW`
	+ `REAL_OF_NUM_LT`
	+ `ARITH`
	+ `GSYM LN_MUL`
	+ `FACT_LT`
	+ `REAL_POW_LT`
	+ `REAL_LT_MUL`
	+ `GSYM LN_DIV`
	+ `CONTL_SEQ`
	+ `DIFF_CONT`
	+ `ETA_AX`
	+ `PI2_LT`
	+ `REAL_OF_NUM_LT`
* Definitions:
	+ `WALLIS`
	+ `FACT`
	+ `LN_POW`
	+ `LN_MUL`
	+ `LN_DIV`

---

## STIRLING

### Name of formal statement
STIRLING

### Type of the formal statement
Theorem

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
           REAL_MUL_RID; REAL_OF_NUM_EQ; NOT_SUC])
```

### Informal statement
For all natural numbers `n`, the difference between the natural logarithm of `n` factorial and the expression `((n + 1/2) * ln(n) - n + ln(2 * pi) / 2)` approaches `0` as `n` increases.

### Informal sketch
* The proof starts with the definition of `STIRLING` and applies several rewriting and substitution steps to simplify the expression.
* It then uses `MATCH_MP_TAC` to apply the `SEQ_SUB` theorem, which is used to prove the convergence of a sequence.
* The proof also uses `X_CHOOSE_THEN` to choose a real number `C` and applies `MP_TAC` to `STIRLING_CONVERGES` to establish a relationship between `C` and the sequence.
* The `GEN_REWRITE_TAC` and `REWRITE_TAC` tactics are used to simplify the expression and apply various mathematical properties, such as `REAL_ARITH` and `LN_MUL`.
* The proof also involves applying `SEQ_ADD` and `SEQ_MUL` theorems to establish the convergence of the sequence.
* The `LN_WALLIS` theorem is used to establish a relationship between the natural logarithm and the `ln` function.
* The proof concludes by applying `MATCH_MP_TAC` to `SEQ_UNIQ` to establish the uniqueness of the limit.

### Mathematical insight
The `STIRLING` theorem provides an approximation of the natural logarithm of `n` factorial, which is a fundamental concept in mathematics. The theorem shows that the difference between the natural logarithm of `n` factorial and the given expression approaches `0` as `n` increases, which is a key result in mathematics and computer science.

### Dependencies
* Theorems:
	+ `SEQ_SUB`
	+ `STIRLING_CONVERGES`
	+ `LN_WALLIS`
	+ `SEQ_UNIQ`
	+ `SEQ_ADD`
	+ `SEQ_MUL`
* Definitions:
	+ `stirling`
	+ `FACT`
	+ `ln`
* Axioms:
	+ `REAL_ARITH`
	+ `LN_MUL`
	+ `REAL_OF_NUM_LT`
	+ `LT_0`
	+ `REAL_FIELD`

### Porting notes
When porting this theorem to other proof assistants, such as Lean or Coq, the following challenges may arise:
* The `MATCH_MP_TAC` tactic may need to be replaced with a similar tactic, such as `apply` or `exact`.
* The `GEN_REWRITE_TAC` and `REWRITE_TAC` tactics may need to be replaced with similar tactics, such as `rewrite` or `simp`.
* The `X_CHOOSE_THEN` tactic may need to be replaced with a similar tactic, such as `choose` or `exists`.
* The `MP_TAC` tactic may need to be replaced with a similar tactic, such as `apply` or `exact`.
* The `SEQ_SUB`, `STIRLING_CONVERGES`, `LN_WALLIS`, `SEQ_UNIQ`, `SEQ_ADD`, and `SEQ_MUL` theorems may need to be re-proved or imported from a library.
* The `stirling`, `FACT`, and `ln` definitions may need to be re-defined or imported from a library.
* The `REAL_ARITH`, `LN_MUL`, `REAL_OF_NUM_LT`, `LT_0`, and `REAL_FIELD` axioms may need to be re-proved or imported from a library.

---

