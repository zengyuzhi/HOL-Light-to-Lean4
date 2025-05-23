# pnt.ml

## Overview

Number of statements: 89

`pnt.ml` formalizes a proof of the Prime Number Theorem, following Newman's approach. It depends on Cauchy's integral theorem, Pocklington's criterion, and Mangoldt's function. The file culminates in a formal statement and proof of the Prime Number Theorem.


## LT_NORM_CPOW_NUM

### Name of formal statement
LT_NORM_CPOW_NUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LT_NORM_CPOW_NUM = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> &1 < norm(Cx(&n) cpow s)`,
  SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 0 < n`] THEN
  REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
  SIMP_TAC[REAL_LT_MUL; LOG_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 1 < n`]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than 0 and `n` is greater than or equal to 2, then 1 is strictly less than the norm of `(Cx(&n) cpow s)`, where `Cx` is the complex embedding of a real, `&n` is the real embedding of `n`, and `cpow` is the complex power function.

### Informal sketch
The proof proceeds as follows:
- First, simplify the expression `norm(Cx(&n) cpow s)` using `NORM_CPOW_REAL`, `REAL_CX`, `RE_CX`, `REAL_OF_NUM_LT`, and the arithmetic rule `2 <= n ==> 0 < n`. This reduces the goal to a statement about real exponentiation and norms.
- Next, rewrite using `REAL_EXP_0` (in reverse using `GSYM`) and `REAL_EXP_MONO_LT` to compare the real exponential with 1.  `REAL_EXP_0` likely relates `exp 0` to `1`, and `REAL_EXP_MONO_LT` asserts the monotonicity of the real exponential function.
- Finally, apply further simplification using `REAL_LT_MUL`, `LOG_POS_LT`, `REAL_OF_NUM_LT`, and the arithmetic rule `2 <= n ==> 1 < n` to complete the proof. These likely deal with properties of real multiplication, logarithms and embeddings of natural numbers into the reals.

### Mathematical insight
The theorem provides a lower bound for the norm of the complex power of the complex embedding of a natural number `n` (where `n >= 2`) raised to a complex power `s`, given that the real part of `s` is positive. This type of bound is useful in analytic number theory, particularly when dealing with estimates involving complex functions, such as in the context of the Prime Number Theorem.

### Dependencies
- `Multivariate/cauchy.ml`
- `Library/pocklington.ml`
- `Examples/mangoldt.ml`
- `NORM_CPOW_REAL`
- `REAL_CX`
- `RE_CX`
- `REAL_OF_NUM_LT`
- `REAL_EXP_0`
- `REAL_EXP_MONO_LT`
- `REAL_LT_MUL`
- `LOG_POS_LT`


---

## CPOW_NUM_NE_1

### Name of formal statement
CPOW_NUM_NE_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CPOW_NUM_NE_1 = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> ~(Cx(&n) cpow s = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SYM o AP_TERM `norm:complex->real`) THEN
  ASM_SIMP_TAC[LT_NORM_CPOW_NUM; COMPLEX_NORM_CX; REAL_ABS_NUM;
               REAL_LT_IMP_NE]);;
```
### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than 0 and `n` is greater than or equal to 2, then `Cx(&n)` raised to the power of `s` is not equal to `Cx(&1)`.

### Informal sketch
The proof proceeds by assuming the negation of the goal and proceeds as follows:
- Simplify the assumption using `norm:complex->real` to get the norm of `Cx(&n) cpow s`.
- Simplify the assumption (using `ASM_SIMP_TAC`) with lemmas about the norm of a complex power (`LT_NORM_CPOW_NUM`), the norm of a complex number constructed from a real (`COMPLEX_NORM_CX`), the absolute value of a real number (`REAL_ABS_NUM`), and the implication between less than and not equal (`REAL_LT_IMP_NE`). This is sufficient to prove the theorem.

### Mathematical insight
This theorem states that for a natural number `n` greater than or equal to 2, and a complex number `s` with a positive real part, the complex number `n` raised to the power of `s` is never equal to 1. This is a basic result about complex exponentiation and provides a constraint on the values that complex powers of natural numbers can take.

### Dependencies
- Theorems: `LT_NORM_CPOW_NUM`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `REAL_LT_IMP_NE`


---

## FINITE_ATMOST

### Name of formal statement
FINITE_ATMOST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_ATMOST = prove
 (`!P n. FINITE {m:num | P m /\ m <= n}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  SIMP_TAC[LE_0; FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG]);;
```

### Informal statement
For any predicate `P` on natural numbers and any natural number `n`, the set of natural numbers `m` such that `P(m)` holds and `m` is less than or equal to `n` is finite.

### Informal sketch
The theorem states that the elements satisfying predicate `P` up to a number `n` form a finite set. The proof proceeds as follows:
- It uses the theorem `FINITE_SUBSET`, which states that a subset of a finite set is finite.
- It shows that `{m:num | P m /\ m <= n}` is a subset of `0..n` by using  `IN_ELIM_THM`. We can show that if `m` is in the set `{m:num | P m /\ m <= n}`, then `P m /\ m <= n` is true which means `m <= n` is true.
- It uses `EXISTS_TAC \`0..n\`` to show that there exists a set such as `0..n`.
- `FINITE_NUMSEG` proves that the set `0..n` is finite if `n` is a natural number.
- `LE_0` introduces the trivial `0 <= n` fact (used in constructing a numerical segment).
- `SUBSET` says that `{m:num | P m /\ m <= n}` is a subset of `0..n`.

### Mathematical insight
This theorem demonstrates a basic result about finiteness in the natural numbers. Any set of natural numbers bounded above is finite. This is a fundamental property used in various areas of mathematics, especially when dealing with inductive proofs or combinatorial arguments.

### Dependencies
- `FINITE_SUBSET`
- `LE_0`
- `FINITE_NUMSEG`
- `SUBSET`
- `IN_ELIM_THM`
- `IN_NUMSEG`


---

## PRIME_ATMOST_ALT

### Name of formal statement
PRIME_ATMOST_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_ATMOST_ALT = prove
 (`{p | prime p /\ p <= n} = {p | p IN 1..n /\ prime p}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC);;
```
### Informal statement
The set of primes `p` such that `p` is less than or equal to `n` is equal to the set of primes `p` such that `p` is an element of the integer interval from `1` to `n`.

### Informal sketch
The theorem states the equivalence of two definitions of primes less than or equal to `n`. The proof proceeds by:

- Rewriting using `EXTENSION`, `IN_ELIM_THM`, and `IN_NUMSEG` to expand the set comprehension on both sides. This expands set equality to element-wise equivalence.
- Introducing a universal quantifier over `p:num` using `X_GEN_TAC`.
- Performing case splitting on whether `prime p` is true or false using `ASM_CASES_TAC`.
- Simplifying using `ASM_REWRITE_TAC[]`.
- Using `PRIME_IMP_NZ` to establish that `p` not prime implies `p` must be 0 (or 1 if the case split is done in a different order), then using `ARITH_TAC` to discharge the arithmetic reasoning.

### Mathematical insight
The theorem expresses a natural and useful alternative way to characterize the set of primes less than or equal to a given number `n`. This is useful because it connects the concept of primality with the concept of an integer interval.

### Dependencies
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `IN_NUMSEG`, `PRIME_IMP_NZ`


---

## nearzeta

### Name of formal statement
- nearzeta

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let nearzeta = new_definition
 `nearzeta n s = infsum (from n)
                        (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                               Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))`;;
```

### Informal statement
- Define `nearzeta n s` to be the infinite sum, starting from `n`, of the terms given by the expression `(s - 1) / m^s - (1 / m^(s - 1) - 1 / (m+1)^(s - 1))`, where `n` and `m` are natural numbers, and `s` is a complex number.

### Informal sketch
- The definition introduces `nearzeta n s` as an infinite sum starting at `n`.
- The summand is given by `(s - Cx(&1)) / Cx(&m) cpow s - (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) - Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1)))`.
- The `infsum` operator represents the infinite summation.

### Mathematical insight
- `nearzeta n s` is introduced as an auxiliary zeta function, designed to have good analytic properties within the right half-plane.
- The definition likely aims to isolate or cancel out problematic terms that would otherwise prevent the direct definition of the zeta function.
- The expression `(s - 1) / m^s - (1 / m^(s - 1) - 1 / (m+1)^(s - 1))` is carefully crafted to ensure convergence and analyticity in the desired region.

### Dependencies
- Definitions:
  - `infsum`
  - `cpow`
  - `Cx`
  - `/`
  - `-`

### Porting notes (optional)
- Ensure that the target proof assistant has support for complex numbers and infinite sums.
- Pay attention to the convergence conditions implied by `infsum` and ensure they are correctly translated.
- The port should address the nuances of complex exponentiation (`cpow`).


---

## genzeta

### Name of formal statement
- genzeta

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let genzeta = new_definition
 `genzeta n s = if s = Cx(&1) then complex_derivative (nearzeta n) (Cx(&1))
                else (nearzeta n s + Cx(&1) / Cx(&n) cpow (s - Cx(&1))) /
                     (s - Cx(&1))`;;
```
### Informal statement
- The function `genzeta n s` is defined as follows: If `s` is equal to the complex number 1, then `genzeta n s` is the complex derivative of `nearzeta n` evaluated at the complex number 1. Otherwise, `genzeta n s` is equal to ( `nearzeta n s` plus the complex number 1 divided by the complex number `n` times the complex power of `n` raised to `s` minus the complex number 1) divided by (`s` minus the complex number 1).

### Informal sketch
- The definition of `genzeta` provides a way to compute values of a function, using an auxiliary function called `nearzeta`.
- If `s` equals the complex number 1, then derivative of the function `nearzeta n` w.r.t `s` at the point `Cx &1` is computed.
- Otherwise, a separate formula, which uses function `nearzeta`, is used to define `genzeta n s`.
- This formula likely provides a continuous extension of the function to complex values of `s`.

### Mathematical insight
- `genzeta` is defined to be equal to `nearzeta` everywhere, where `s` is not equal to 1. The reason for doing this is to subtract `1/(s-1)` from `nearzeta` which may have a pole at `s=1`. The definition uses the limit obtained by finding the derivative of nearzeta with respect to `s` when `s=1`, so that the definition does not have a pole value.

### Dependencies
- Definitions: `nearzeta`, `complex_derivative`, `cpow`


---

## zeta

### Name of formal statement
zeta

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zeta = new_definition
 `zeta s = genzeta 1 s`;;
```

### Informal statement
The function `zeta` of `s` is defined as `genzeta` applied to `1` and `s`.

### Informal sketch
- The definition introduces `zeta` in terms of `genzeta`. The definition essentially specializes the `genzeta` function at the value 1.
- The mathematical content is trivial since it is a direct definition; no real proof is involved.

### Mathematical insight
The `zeta` function is being defined here, most likely as a specific case, variant, or specialization of the more general `genzeta` function. This could be the starting point for defining the Riemann zeta function or some other zeta function.

### Dependencies
- Definition: `genzeta`



---

## NEARZETA_BOUND_LEMMA

### Name of formal statement
NEARZETA_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_BOUND_LEMMA = prove
 (`!s n. ~(n = 0) /\ &0 <= Re s + &1
         ==> norm((s - Cx(&1)) / Cx(&n) cpow s -
                  (Cx(&1) / Cx(&n) cpow (s - Cx(&1)) -
                   Cx(&1) / Cx(&(n + 1)) cpow (s - Cx(&1)))) <=
             norm(s * (s - Cx(&1)) / Cx(&n) cpow (s + Cx(&1)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then Cx(&1) / z cpow (s - Cx(&1))
           else if n = 1 then (Cx(&1) - s) / z cpow s
           else s * (s - Cx(&1)) / z cpow (s + Cx(&1))`;
    `1`; `segment[Cx(&n),Cx(&n) + Cx(&1)]`;
    `norm(s * (s - Cx (&1)) / Cx(&n) cpow (s + Cx(&1)))`] COMPLEX_TAYLOR) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_SEGMENT] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `z:complex`] THEN STRIP_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC] THEN
    (SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
      [MATCH_MP_TAC RE_POS_SEGMENT THEN
       MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
       ASM_REWRITE_TAC[RE_ADD; RE_CX; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
       ASM_ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[RE_CX; REAL_LT_REFL];
       ALL_TAC])
    THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
        (ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`)) THEN
      ASM_REWRITE_TAC[ARITH] THEN COMPLEX_DIFF_TAC THEN
      ASM_REWRITE_TAC[CPOW_EQ_0] THEN
      SIMP_TAC[COMPLEX_POW_2; CPOW_ADD; CPOW_SUB; CPOW_N; COMPLEX_POW_1] THEN
      (SUBGOAL_THEN `~(z cpow s = Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[CPOW_EQ_0]; UNDISCH_TAC `~(z = Cx(&0))`]) THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `real z` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
      ASM_SIMP_TAC[REAL_CX; REAL_ADD];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[RE_ADD; RE_CX] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    UNDISCH_TAC `z IN segment[Cx (&n),Cx (&n) + Cx (&1)]` THEN
    REWRITE_TAC[segment; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE_CX] THEN
    UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CONV `0..1`] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; COMPLEX_MUL_RID] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx(&n)`; `Cx(&n) + Cx(&1)`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; COMPLEX_NORM_CX; COMPLEX_ADD_SUB] THEN
  REWRITE_TAC[VECTOR_ADD_RID; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_RID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; complex_div] THEN
  CONV_TAC COMPLEX_RING);;
```
### Informal statement
For all complex numbers `s` and natural numbers `n`, if `n` is not equal to 0 and the real part of `s` plus 1 is greater than or equal to 0, then the norm of `(s - 1) / n^s - (1 / n^(s-1) - 1 / (n+1)^(s-1))` is less than or equal to the norm of `s * (s - 1) / n^(s+1)`.

### Informal sketch
The proof uses a Taylor series expansion with remainder to bound the difference of certain complex power terms.

- The proof starts by stripping the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- It then applies a specialized Taylor series expansion theorem `COMPLEX_TAYLOR` to the function `\n z. if n = 0 then Cx(&1) / z cpow (s - Cx(&1)) else if n = 1 then (Cx(&1) - s) / z cpow s else s * (s - Cx(&1)) / z cpow (s + Cx(&1))` at `n = 1` over the segment `segment[Cx(&n),Cx(&n) + Cx(&1)]`, with an error bound `norm(s * (s - Cx (&1)) / Cx(&n) cpow (s + Cx(&1)))`.
- Several rewriting steps involving arithmetic, convex segments, and complex differentiation are employed to simplify and manipulate the inequality.
- Case splitting is performed based on `i <= 1 ==> i = 0 \/ i = 1`.
- The proof uses properties of complex powers, norms, and conjugates and field arithmetic over complexes.
- It uses monotonicity of the real exponential function and simplification of exponential and logarithmic terms to estimate the inequality.
- Finally, it uses arithmetic reasoning and properties of segments in the complex plane to complete the proof.

### Mathematical insight
This lemma provides a bound on the difference between certain terms related to the Hurwitz zeta function. It arises in the context of analyzing the convergence and analytical properties of specific series related to the zeta function, particularly in estimating the error when approximating the zeta function by a truncated series.

### Dependencies
- `ARITH`
- `RE_POS_SEGMENT`
- `RE_CX`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_LT`
- `REAL_LT_REFL`
- `CPOW_EQ_0`
- `COMPLEX_POW_2`
- `CPOW_ADD`
- `CPOW_SUB`
- `CPOW_N`
- `COMPLEX_POW_1`
- `COMPLEX_FIELD`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_DIV`
- `COMPLEX_NORM_POW`
- `real_div`
- `REAL_MUL_ASSOC`
- `REAL_LE_LMUL`
- `REAL_LE_MUL`
- `NORM_POS_LE`
- `REAL_LE_INV2`
- `COMPLEX_NORM_NZ`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `REAL_SEGMENT`
- `REAL_CX`
- `REAL_ADD`
- `NORM_CPOW_REAL`
- `RE_CX`
- `REAL_OF_NUM_LT`
- `LT_NZ`
- `REAL_EXP_MONO_LE`
- `RE_ADD`
- `EXP_LOG`
- `RE_CMUL`
- `ENDS_IN_SEGMENT`
- `COMPLEX_NORM_CX`
- `COMPLEX_ADD_SUB`
- `VECTOR_ADD_RID`
- `COMPLEX_MUL_LID`
- `REAL_ABS_NUM`
- `REAL_POW_ONE`
- `REAL_DIV_1`
- `REAL_MUL_RID`
- `GSYM REAL_OF_NUM_ADD`
- `CX_ADD`
- `complex_div`
- `COMPLEX_RING`
- `COMPLEX_TAYLOR`
- `CONVEX_SEGMENT`
- `NUMSEG_CONV 0..1`
- `VSUM_CLAUSES`
- `FINITE_INSERT`
- `FINITE_RULES`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `complex_pow`

### Porting notes (optional)
- The `COMPLEX_TAYLOR` theorem is a key dependency and might require a similar theorem to be constructed or found in other proof assistants.
- Pay careful attention to the handling of complex numbers, powers, and norms, as implementations might vary across systems.
- The heavy use of rewriting and arithmetic tactics suggests the need for strong simplification and automation capabilities in the target proof assistant.


---

## NORM_CPOW_LOWERBOUND

### Name of formal statement
NORM_CPOW_LOWERBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_CPOW_LOWERBOUND = prove
 (`!m s n. &m <= Re s /\ ~(n = 0) ==> &n pow m <= norm(Cx(&n) cpow s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&m * log(&n))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_LE_REFL];
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_EXP_0; EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    SIMP_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;
```
### Informal statement
For all real numbers `m` and complex numbers `s` and natural numbers `n`, if `m` is less than or equal to the real part of `s` and `n` is not equal to 0, then `n` raised to the power of `m` is less than or equal to the norm of `Cx(&n) cpow s`.

### Informal sketch
The theorem provides a lower bound for the norm of a complex power. The proof proceeds as follows:
- Start by stripping the quantifiers and assumptions.
- Simplify the expression `Cx(&n) cpow s` using `NORM_CPOW_REAL`, `REAL_CX`, `RE_CX`, `REAL_OF_NUM_LT`, and `LT_NZ`. This will reduce the goal to bounding `exp(Re s * log(&n))` from below.
- Apply `REAL_LE_TRANS` by introducing `exp(&m * log(&n))` as an intermediate term. This splits the goal into two subgoals: `&n pow m <= exp(&m * log(&n))` and `exp(&m * log(&n)) <= exp(Re s * log(&n))`.
- The first subgoal `&n pow m <= exp(&m * log(&n))` simplifies using `REAL_EXP_N` and `EXP_LOG`.
- The second subgoal `exp(&m * log(&n)) <= exp(Re s * log(&n))` simplifies using `REAL_EXP_MONO_LE` and the assumption `&m <= Re s`. The condition `0 < log &n` from `REAL_EXP_MONO_LE` is discharged using `EXP_LOG`, `REAL_OF_NUM_LT`, and `LT_NZ`.

### Mathematical insight
The theorem provides a lower bound for the norm of a complex power in terms of the real power, which is useful in various analytical contexts when dealing with complex exponentiation. The complex power `z cpow s` is defined as `exp(s * log z)`, so its norm is `exp(Re s * log |z|)` when `z` is a complex number. Here, `z` is `Cx n` where `n` is a natural number and `s` is a complex number. The theorem states that `n^m <= |(Cx n)^s|` if `m <= Re s`.

### Dependencies
- `NORM_CPOW_REAL`
- `REAL_CX`
- `RE_CX`
- `REAL_OF_NUM_LT`
- `LT_NZ`
- `REAL_LE_TRANS`
- `REAL_EXP_N`
- `EXP_LOG`
- `REAL_LE_REFL`
- `REAL_EXP_MONO_LE`
- `REAL_LE_RMUL`
- `REAL_EXP_0`
- `REAL_OF_NUM_LE`
- `GSYM REAL_EXP_MONO_LE`

### Porting notes (optional)
- The proof depends heavily on real analysis lemmas. Ensure that the target proof assistant has similar results available, especially for exponential and logarithmic functions.
- The use of automation tactics such as `ASM_SIMP_TAC` and `ASM_ARITH_TAC` might need to be replaced by more explicit reasoning steps in other proof assistants.


---

## ZETATERM_BOUND

### Name of formal statement
ZETATERM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETATERM_BOUND = prove
 (`!s n m. &m <= Re s /\ ~(n = 0)
           ==> norm(Cx(&1) / Cx(&n) cpow s) <= inv(&n pow m)`,
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_CPOW_LOWERBOUND; REAL_OF_NUM_LT; LT_NZ]);;
```
### Informal statement
For all real numbers `s`, natural numbers `n`, and natural numbers `m`, if `m` is less than or equal to the real part of `s` and `n` is not equal to 0, then the norm of the complex number `1/n^s` is less than or equal to `1/(n^m)`.

### Informal sketch
The proof proceeds as follows:
- Apply `COMPLEX_NORM_DIV`, `COMPLEX_NORM_CX`, and `REAL_ABS_NUM` to simplify the norm of the complex division.
- Simplify using `real_div` and `REAL_MUL_LID`.
- Remove the universal quantifiers using `REPEAT STRIP_TAC`.
- Use `REAL_LE_INV2` to transform the inequality.
- Use assumption based simplification applying `REAL_POW_LT`, `NORM_CPOW_LOWERBOUND`, `REAL_OF_NUM_LT`, and `LT_NZ` to prove the resulting goal..

### Mathematical insight
The theorem provides an upper bound on the magnitude of the complex term `1/n^s`, where `n` is a natural number and `s` is a complex number whose real part is bounded below by `m`.
This result is likely used in the analysis of series involving terms of this kind, such as Dirichlet series or the Riemann zeta function, where bounding individual terms is crucial for proving convergence or other properties.

### Dependencies
- Theorems: `COMPLEX_NORM_DIV`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `real_div`, `REAL_MUL_LID`, `REAL_LE_INV2`, `REAL_POW_LT`, `NORM_CPOW_LOWERBOUND`, `REAL_OF_NUM_LT`, `LT_NZ`


---

## ZETA_CONVERGES_LEMMA

### Name of formal statement
ZETA_CONVERGES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_CONVERGES_LEMMA = prove
 (`!n s. &2 <= Re s ==> summable (from n) (\m. Cx(&1) / Cx(&m) cpow s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
  MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n - &1) - inv(&(n + 1) - &1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `lift(inv(&n - &1))` THEN
    MP_TAC(ISPECL [`\n. lift(inv(&n - &1))`; `n:num`] SERIES_DIFFS) THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    REWRITE_TAC[SEQ_HARMONIC];
    ALL_TAC] THEN
  EXISTS_TAC `2` THEN REWRITE_TAC[GE; IN_FROM] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_FIELD
   `&2 <= x ==> inv(x - &1) - inv((x + &1) - &1) = inv(x * (x - &1))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&n pow 2 <= x ==> &n * (&n - &1) <= x`) THEN
  MATCH_MP_TAC NORM_CPOW_LOWERBOUND THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than or equal to 2, then the series whose general term is `1/m^s` is summable from `n` onwards, where `m` ranges over the natural numbers.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting `summable` to its definition.
- Utilize the `SERIES_COMPARISON` theorem to compare the complex series `1/m^s ` with a real series that is known to converge. Specifically, we will compare it with `inv(n-1) - inv(n+1-1) = inv(n-1) - inv(n)`.
- Show that the real series `inv(n-1) - inv(n)` is the difference of successive terms of a summable sequence `lift(inv(n-1))`. This is done by using `SERIES_DIFFS`, rewriting using `o_DEF` and `LIFT_SUB`, using `SEQ_OFFSET_REV` for reindexing, and then showing that `SEQ_HARMONIC` gives the desired result.
- Establish the inequality `|1/m^s| <= inv(m*(m-1))`. This is done by: taking m = 2, simplifying, using the fact that the real part of `s` is greater than or equal to 2, applying basic properties of complex norms and real numbers including `COMPLEX_NORM_DIV`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `real_div`, and `REAL_MUL_LID`. The reciprocals are compared by reducing to `REAL_LE_INV2`. A step consists of proving the intermediate result with the `REAL_ARITH` of the form `&n pow 2 <= x ==> &n * (&n - &1) <= x`. Finally, apply the `NORM_CPOW_LOWERBOUND` theorem.

### Mathematical insight
The theorem states a standard result from complex analysis: that the series defining the Riemann zeta function converges for complex numbers with real part greater than 1. The proof demonstrates a comparison test approach: bounding the complex series by a real-valued series and showing that the real-valued series converges.

### Dependencies
**Definitions:**
- `summable`
- `Cx`
- `cpow`
- `o_DEF`
- `LIFT_SUB`
- `COMPLEX_NORM_DIV`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `real_div`

**Theorems:**
- `SERIES_COMPARISON`
- `SERIES_DIFFS`
- `SEQ_OFFSET_REV`
- `SEQ_HARMONIC`
- `REAL_LE_INV2`
- `NORM_CPOW_LOWERBOUND`

**Axioms/Rules:**
- `GE`
- `IN_FROM`

**Conversion Theorems:**
- `GSYM REAL_OF_NUM_ADD`
- `REAL_OF_NUM_LE`

**Real Field Facts:**
- `REAL_FIELD \`&2 <= x ==> inv(x - &1) - inv((x + &1) - &1) = inv(x * (x - &1))\``
- `REAL_MUL_LID`

**Arithmetic tactics:**
- `REAL_ARITH \`(x + &1) - &1 = x\``
- `REAL_ARITH \`&n pow 2 <= x ==> &n * (&n - &1) <= x\``

### Porting notes (optional)
- The proof relies heavily on real and complex analysis libraries. These libraries, or suitable substitutes, need to be available in the target proof assistant.
- The tactic `ASM_ARITH_TAC` may need to be replaced with a more explicit proof involving inequalities in other proof assistants.
- The conversion tactics that invoke the real field solver `REAL_FIELD` may need to be replaced with appropriate rewriting or simplification steps to achieve the equivalent effect.


---

## ZETADIFF_CONVERGES

### Name of formal statement
ZETADIFF_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETADIFF_CONVERGES = prove
 (`!n s. &0 < Re(s)
         ==> ((\m. Cx(&1) / Cx(&m) cpow s - Cx(&1) / Cx(&(m + 1)) cpow s)
              sums Cx(&1) / Cx(&n) cpow s) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. Cx(&1) / Cx(&m) cpow s`; `n:num`] SERIES_DIFFS) THEN
  REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\n. lift(&1 / exp (Re s * log (&n)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 VECTOR_SUB_REFL; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &1 / (Re s * log(&n))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_EXP; real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < x /\ (&0 <= x ==> &1 + u <= v) ==> &0 < x /\ u <= v`) THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= n ==> 1 < n`];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `exp(inv(Re s * e))` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 2` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN
  SUBGOAL_THEN `&0 < log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `N + 2 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL;
               REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n` THEN ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 2 <= n ==> N <= n`] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EXP_LOG THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than 0, then the series whose `m`-th term is `Cx(&1) / Cx(&m) cpow s - Cx(&1) / Cx(&(m + 1)) cpow s` sums to `Cx(&1) / Cx(&n) cpow s` from `n` onwards.

### Informal sketch
The proof demonstrates the convergence of a telescoping series.
- The main idea is to rewrite the series as a difference of partial sums using `SERIES_DIFFS`.
- Show that the limit of the remainder `Cx(&1) / Cx(&n) cpow s` tends to zero as `n` approaches infinity, provided the real part of `s` is positive.
- Decompose the complex norm using `COMPLEX_NORM_DIV`, `COMPLEX_NORM_CX` and `REAL_ABS_NUM`.
- Reduce the problem to show that `&1 / exp (Re s * log (&n))` converges to zero using `LIM_TRANSFORM` and `LIM_NULL_COMPARISON`.
- Apply standard real analysis results for limits and inequalities to prove the convergence.
- Use `REAL_ARCH` to choose a suitable `N` based on `e` and demonstrate the convergence.
- Employ various algebraic simplifications such as `REAL_ABS_DIV`, `REAL_ABS_MUL`, and properties of logarithms and exponentials.

### Mathematical insight
The theorem establishes the convergence of a series related to the Riemann zeta function. By expressing the series as a telescoping sum and demonstrating the convergence of the remaining term, the theorem reveals an important property of complex powers and demonstrates a way to manipulate such series. This is a foundational theorem for dealing with zeta function-related series in formal settings.

### Dependencies
- `SERIES_DIFFS`
- `CPOW_1`
- `COMPLEX_DIV_1`
- `LIM_NULL_NORM`
- `COMPLEX_NORM_DIV`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `LIM_TRANSFORM`
- `LIM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `NORM_CPOW_REAL`
- `REAL_CX`
- `RE_CX`
- `REAL_OF_NUM_LT`
- `VECTOR_SUB_REFL`
- `LE_1`
- `LIM_NULL_COMPARISON`
- `NORM_LIFT`
- `REAL_ABS_INV`
- `REAL_ABS_EXP`
- `REAL_MUL_LID`
- `REAL_LE_INV2`
- `REAL_EXP_LE_X`
- `LOG_POS_LT`
- `REAL_LT_MUL`
- `ARITH_RULE`
- `LIM_SEQUENTIALLY`
- `REAL_ARCH`
- `REAL_MUL_RID`
- `dist`
- `VECTOR_SUB_RZERO`
- `NORM_LIFT`
- `LOG_POS_LT`
- `REAL_ABS_DIV`
- `REAL_ABS_MUL`
- `REAL_ARITH`
- `REAL_INV_MUL`
- `REAL_LT_LDIV_EQ`
- `REAL_MUL_LID`
- `REAL_EXP_MONO_LT`
- `REAL_LTE_TRANS`
- `REAL_LE_TRANS`
- `REAL_OF_NUM_LE`
- `REAL_EQ_IMP_LE`
- `EXP_LOG`

### Porting notes (optional)
- The proof relies heavily on real and complex analysis libraries. Ensure that the target proof assistant has comparable support.
- The use of `Cx` (complexification of a real number), `cpow` (complex power), and `Re` (real part of a complex number) needs corresponding translations.
- Tactics like `REPEAT STRIP_TAC`, `ASM_SIMP_TAC`, and `REWRITE_TAC` have equivalents in most proof assistants, but care must be taken to ensure the rewrite rules and simplification strategies are similar so that the proof is easily ported to new environments. Some arithmetic reasoning is done via `ARITH_TAC` which will need to be carefully reproduced in other theorem provers because the automation levels may be different.


---

## NEARZETA_CONVERGES_LEMMA

### Name of formal statement
NEARZETA_CONVERGES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_CONVERGES_LEMMA = prove
 (`!n s. &1 <= Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  REWRITE_TAC[summable] THEN MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\m. norm(s * (s - Cx(&1)) / Cx(&m) cpow (s + Cx(&1)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[IN_FROM; GE; LE_1; NEARZETA_BOUND_LEMMA;
                 REAL_ARITH `&1 <= s ==> &0 <= s + &1`]] THEN
  SUBGOAL_THEN
   `summable (from n)
     (\m. lift(((Cx (norm s) * Cx (norm (s - Cx (&1)))) *
                Cx (&1) / Cx (&m) cpow Cx (Re s + &1))$1))`
  MP_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPONENT THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC ZETA_CONVERGES_LEMMA THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM summable] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_FROM; o_THM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM RE_DEF] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; complex_div] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID; COMPLEX_NORM_INV] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LE_1] THEN
  REWRITE_TAC[GSYM CX_INV; RE_CX; RE_ADD]);;
```
### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than or equal to 1, then the series whose `m`-th term is `(s - 1) / m^s - (1 / m^(s - 1) - 1 / (m + 1)^(s - 1))` sums to `nearzeta n s` starting from `n` (i.e., the series converges to `nearzeta n s`).

### Informal sketch
The proof demonstrates the convergence of a series related to the `nearzeta` function.

- First, rewrite the goal using the definitions of `nearzeta` and `SUMS_INFSUM`.
- Then, rewrite using the definition of `summable`.
- Apply the `SERIES_COMPARISON` theorem, which allows proving summability by comparing with another series.
- Find a suitable comparison series whose `m`-th term is `norm(s * (s - 1) / m^(s + 1))`.
- Decompose the goal produced by `SERIES_COMPARISON` into two subgoals: proving that the terms of the original series are bounded by the terms of the comparison series, and proving the summability of the comparison series.
- For the first subgoal, use `NEARZETA_BOUND_LEMMA` and real arithmetic.
- For the second subgoal, show that the comparison series `summable` by relating it to `ZETA_CONVERGES_LEMMA`. This uses `SUMMABLE_COMPONENT` to reduce the number of terms via `DIMINDEX_2`, `SUMMABLE_COMPLEX_LMUL`, then invoking `ZETA_CONVERGES_LEMMA`. Then the goal needs `REAL_ARITH_TAC`. The `SUMMABLE_IFF_EVENTUALLY` theorem is then employed to show that starting from some point onwards (specifically 1), the summability condition is satisfied. This involves showing that the norms of the complex terms of the original series converge to those of our comparison series. This is achieved by successive rewriting of the complex terms and applying simplification rules regarding norms and complex operations.

### Mathematical insight
This lemma establishes the convergence of a specific series related to the `nearzeta` function. The series represents a telescoping series involving terms of the form `1/m^(s-1)`, and the convergence is shown by comparing it to a convergent zeta function series. This result is foundational for further analysis and manipulation with `nearzeta` function.

### Dependencies
- Definitions: `nearzeta`, `SUMS_INFSUM`, `summable`
- Theorems: `SERIES_COMPARISON`, `SUMMABLE_COMPONENT`, `SUMMABLE_COMPLEX_LMUL`, `ZETA_CONVERGES_LEMMA`, `SUMMABLE_IFF_EVENTUALLY`, `EQ_IMP`
- Lemmas: `NEARZETA_BOUND_LEMMA`
- Other: `IN_FROM`, `GE`, `LE_1`, `REAL_ARITH`

### Porting notes (optional)
- The `SERIES_COMPARISON` theorem is crucial and should be carefully ported, as it involves inequalities and summability conditions.
- The handling of complex numbers and their norms is system-dependent and should be adapted accordingly.
- The extensive rewriting and simplification steps might require equivalent automation in other systems.


---

## GENZETA_CONVERGES

### Name of formal statement
GENZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_CONVERGES = prove
 (`!n s. &1 < Re s
         ==> ((\m. Cx(&1) / Cx(&m) cpow s) sums genzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES_LEMMA o
        MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL [`n:num`; `s - Cx(&1)`] ZETADIFF_CONVERGES) THEN ANTS_TAC THENL
   [REWRITE_TAC[RE_SUB; RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[COMPLEX_RING `a + (b - a) = b:complex`; genzeta] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `&1 < Re s` THEN ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(s - Cx(&1))` o
     MATCH_MP SERIES_COMPLEX_LMUL) THEN
  SUBGOAL_THEN `~(s - Cx(&1) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV] THEN
  REWRITE_TAC[COMPLEX_MUL_AC; COMPLEX_ADD_AC]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is strictly greater than 1, then the partial sums of the series whose m-th term is the complex number 1 divided by m raised to the power of `s` (starting from `n`) converge to a limit denoted `genzeta n s`.

### Informal sketch
The proof demonstrates that the partial sums defining `genzeta n s` converge when `Re s > 1`.

- Start by stripping the quantifiers and the assumption.
- Apply `NEARZETA_CONVERGES_LEMMA` to deduce that the series `Σ (1/m^s), m = 1..` converges if `Re s > 1`. The lemma also needs `REAL_LT_IMP_LE`.
- Decompose the partial sum `genzeta n s` into `zeta s - sum(1/m^s, m = 1..(n-1))`.
- Apply the convergence of `ZETADIFF_CONVERGES` which states that the series whose general term is `Cx(&1) / Cx(&m) cpow s` converges to `zeta s - g` if `(\m. Cx(&1) / Cx(&m) cpow s) sums g`. The difference `s-Cx(&1)` is used as input to the `ZETADIFF_CONVERGES`.
- Verify that the real parts are well-behaved according to the assumptions and `RE_CX`. Ensure `&1 < Re s` after applying `ZETADIFF_CONVERGES`.
- Apply `SERIES_ADD` to show that if `Σ a_n` and `Σ b_n` converge, `Σ a_n + b_n` also converges.
- Simplify using `a+(b-a) = b` and definition of `genzeta`.
- Apply conditional case analysis (`COND_CASES_TAC`). Simplify the real part (`RE_CX`) to complete the conditional proof.
- Then, apply `SERIES_COMPLEX_LMUL` to show that the series `Σ c a_n` converges if `Σ a_n` converges.
- Verify that the scaling factor `inv(s - Cx(&1))` is not 0, simplifying with `COMPLEX_SUB_0` and `RE_CX`, and use real arithmetic.
- Simplify the main goal using complex arithmetic rules of associativity and commutativity, specifically using `complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV; COMPLEX_MUL_AC; COMPLEX_ADD_AC`.

### Mathematical insight
This theorem establishes the convergence of a generalized zeta function (Hurwitz zeta function) for complex arguments with real part greater than 1. This is a crucial result in analytic number theory, allowing the zeta function to be defined in a region of the complex plane beyond its original definition as a sum.

### Dependencies
- `NEARZETA_CONVERGES_LEMMA`
- `REAL_LT_IMP_LE`
- `ZETADIFF_CONVERGES`
- `SERIES_ADD`
- `SERIES_COMPLEX_LMUL`
- `complex_div`
- `COMPLEX_MUL_ASSOC`
- `COMPLEX_MUL_LINV`
- `COMPLEX_MUL_AC`
- `COMPLEX_ADD_AC`
- `complex_sub_0`
- `genzeta`

Categories:
- Complex Analysis: `RE_SUB`, `RE_CX`, `complex_div`, `COMPLEX_MUL_ASSOC`, `COMPLEX_MUL_LINV`, `COMPLEX_MUL_AC`, `COMPLEX_ADD_AC`
- Real Analysis: `REAL_LT_IMP_LE`
- Series: `NEARZETA_CONVERGES_LEMMA`, `SERIES_ADD`, `SERIES_COMPLEX_LMUL`, `ZETADIFF_CONVERGES`
- Ring Theory: `COMPLEX_SUB_0`

### Porting notes (optional)
- The use of tactics like `FIRST_ASSUM(MP_TAC o SPEC ...)` is specific to HOL Light's automation and may require adaptation.
- The proof relies on specific lemmas related to complex analysis and series convergence, which need to be available or proven in the target proof assistant.
- The heavy use of rewriting with complex arithmetic rules suggests that the target system should have good support for complex number manipulation.


---

## ZETA_CONVERGES

### Name of formal statement
ZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums zeta(s)) (from 1)`,
  REWRITE_TAC[zeta; GENZETA_CONVERGES]);;
```
### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the series whose `n`-th term is `Cx(&1) / Cx(&n) cpow s` sums (in the limit as `n` goes to infinity) to `zeta(s)`, starting from `n = 1`.

### Informal sketch
The theorem states that for complex arguments `s` with real part greater than 1, the series representation of the Riemann zeta function converges.

- The theorem is proved using `REWRITE_TAC` with the definitions of `zeta` and `GENZETA_CONVERGES`. This means the proof unfolds the definition of `zeta(s)` to `genzeta 1 s` and then applies the theorem `GENZETA_CONVERGES` to prove the convergence, essentially relying on the generalized zeta function's convergence properties.

### Mathematical insight
This theorem provides a crucial condition for the convergence of the series representation of the Riemann zeta function, namely that the real part of the complex argument `s` must be greater than 1. This condition is essential because the series diverges otherwise. The result is a cornerstone in the study of the zeta function and its applications in number theory.

### Dependencies
- Definitions: `zeta`
- Theorems: `GENZETA_CONVERGES`


---

## COMPLEX_DERIVATIVE_ZETA_CONVERGES

### Name of formal statement
COMPLEX_DERIVATIVE_ZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. --clog(Cx(&n)) / Cx(&n) cpow s) sums
            complex_derivative zeta s) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n z. Cx(&1) / Cx(&n) cpow z`;
    `\n z. --clog(Cx(&n)) / Cx(&n) cpow z`;
    `{s | Re s > &1}`;
    `from 1`]
   SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX) THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; LE_1];
      ALL_TAC] THEN
    POP_ASSUM(K ALL_TAC) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(Re z - &1) / &2`;
      `\n. Cx(&1) / Cx(&n) cpow (Cx(&1 + (Re z - &1) / &2))`;
      `42`] THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_SUB_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `Cx(&1 + (Re z - &1) / &2)` ZETA_CONVERGES) THEN
      ANTS_TAC THENL [REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[summable];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_FROM; CPOW_REAL_REAL; REAL_OF_NUM_LT; RE_CX; REAL_CX;
                 LE_1; COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_CX; RE_CX;
                real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[REAL_ABS_EXP; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--(a * x) <= --(b * x) <=> b * x <= a * x`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MP_TAC(SPEC `z - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_gt] THEN
  MAP_EVERY X_GEN_TAC [`f:complex->complex`; `g:complex->complex`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `b /\ c /\ d ==> e <=> b /\ c ==> d ==> e`]
                HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT) THEN
  EXISTS_TAC `Re s - &1` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. Cx(&1) / Cx(&n) cpow z`; `from 1`] THEN
  SUBGOAL_THEN `&1 < Re z` (fun th -> ASM_SIMP_TAC[th; ZETA_CONVERGES]) THEN
  MP_TAC(SPEC `z - s:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the series whose `n`-th term is `--clog(Cx(&n)) / Cx(&n) cpow s` sums from 1 to the complex derivative of the zeta function at `s`.

### Informal sketch
The proof proceeds as follows:
- Apply `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` to the functions `\n z. Cx(&1) / Cx(&n) cpow z` and `\n z. --clog(Cx(&n)) / Cx(&n) cpow z` with the set `{s | Re s > &1}` and starting point `from 1`.
- Simplify using `OPEN_HALFSPACE_RE_GT` and `IN_ELIM_THM`.
- Prove the antecedent by splitting it into subgoals.
  - The first subgoal involves showing that the given series is differentiable. `COMPLEX_DIFF_TAC` and other tactics are used for differentiation.
  - Transform the goal using the fact `(a ==> b) /\ a ==> a /\ b`.
  - Perform field simplification using `COMPLEX_FIELD`.
  - Simplify assumptions using `CPOW_EQ_0`, `CX_INJ`, `REAL_OF_NUM_EQ`, and `LE_1`.
  - Introduce a complex variable `z` for generality, rewrite `real_gt`, and introduce existential variables using `EXISTS_TAC`.
  - Simplify assumptions using `REAL_HALF` and `REAL_SUB_LT`.
  - Apply `ZETA_CONVERGES` to show that the series converges, and deduce summability.
  - Simplify assumptions further using facts like `IN_FROM`, `CPOW_REAL_REAL`, `REAL_OF_NUM_LT`, `RE_CX`, `REAL_CX`, `LE_1`, `COMPLEX_NORM_DIV`, and `NORM_CPOW_REAL`.
  - Rewrite using facts about cx, norm, and real arithmetic.
  - Rewrite inequalities and apply `REAL_LE_RMUL`.
  - Use `IN_BALL` and `COMPLEX_NORM_GE_RE_IM` to further simplify.
  - Simplify the new goal using `ASM_NORM_ARITH_TAC`.
- Rewrite using `LEFT_IMP_EXISTS_THM` and `real_gt`.
- Introduce general complex functions f and g.
- Use assumptions and simplify.
- Apply theorems `HAS_COMPLEX_DERIVATIVE_DERIVATIVE` and `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`.
- Use `SERIES_UNIQUE`, introduce existential variables, and simplify.
- Use `ZETA_CONVERGES` and `COMPLEX_NORM_GE_RE_IM` to finish the proof.

### Mathematical insight
This theorem proves that the derivative of the Riemann zeta function can be expressed as the sum of a series. This result is important in analytic number theory since it provides an explicit formula for computing the derivative and allows for its analysis using complex analysis techniques.

### Dependencies
- `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`
- `OPEN_HALFSPACE_RE_GT`
- `IN_ELIM_THM`
- `CPOW_EQ_0`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `LE_1`
- `real_gt`
- `REAL_HALF`
- `REAL_SUB_LT`
- `ZETA_CONVERGES`
- `IN_FROM`
- `CPOW_REAL_REAL`
- `REAL_OF_NUM_LT`
- `RE_CX`
- `REAL_CX`
- `COMPLEX_NORM_DIV`
- `NORM_CPOW_REAL`
- `GSYM CX_DIV`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `real_div`
- `REAL_MUL_LID`
- `REAL_LE_INV_EQ`
- `REAL_EXP_POS_LE`
- `REAL_ABS_EXP`
- `GSYM REAL_EXP_NEG`
- `REAL_EXP_MONO_LE`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `LOG_POS`
- `REAL_OF_NUM_LE`
- `IN_BALL`
- `COMPLEX_NORM_GE_RE_IM`
- `RE_SUB`
- `LEFT_IMP_EXISTS_THM`
- `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`
- `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`
- `REAL_SUB_LT`
- `SERIES_UNIQUE`
- `summable`

### Porting notes (optional)
- `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` may require careful porting due to HOL Light's specific handling of convergence and differentiation. Ensure that the target proof assistant has similar tools for reasoning about complex series and their derivatives.
- The extensive use of `ASM_SIMP_TAC` suggests a reliance on the simplifier reducing many goals to trivialities based on the current assumptions. The porter should ensure their target system has an equally powerful simplifier configured with similar rewrite rules.


---

## HOLOMORPHIC_NEARZETA_LEMMA

### Name of formal statement
HOLOMORPHIC_NEARZETA_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA_LEMMA = prove
 (`!n. 1 <= n
       ==> ?g g'. !s. s IN {s | Re(s) > &0}
                      ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                           (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                            Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
                           sums g s) (from n) /\
                           ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                                 Cx(&m) cpow s -
                                 (clog(Cx(&(m + 1))) /
                                  Cx(&(m + 1)) cpow (s - Cx(&1)) -
                                  clog(Cx(&m)) /
                                  Cx(&m) cpow (s - Cx(&1))))
                            sums g' s) (from n) /\
                       (g has_complex_derivative g' s) (at s)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `s:complex`] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt; from] THEN STRIP_TAC THEN
    COMPLEX_DIFF_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
  DISCH_TAC THEN EXISTS_TAC `min (Re s / &2) (&1)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; REAL_HALF] THEN
  EXISTS_TAC `\n. Cx(norm(s) + &2) pow 2 /
                  Cx(&n) cpow Cx((Re s / &2 + &1))` THEN
  EXISTS_TAC `1` THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MP_TAC(SPECL [`n:num`; `Cx(Re s / &2 + &1)`] GENZETA_CONVERGES) THEN
    REWRITE_TAC[RE_CX] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN MESON_TAC[summable];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN REWRITE_TAC[from; IN_ELIM_THM] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
                 GSYM CX_DIV; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND_LEMMA o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(w) = &1 /\ norm(z) <= x + &1
      ==> norm z <= abs(x + &2) /\ norm(z - w) <=  abs(x + &2)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
               REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_ADD; RE_CX] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` such that `1 <= n`, there exist complex-valued functions `g` and `g'` such that for all complex numbers `s` in the open half-plane where the real part of `s` is greater than 0, the following conditions hold:
1. The series of terms `(s - 1) / m^s - (1 / m^(s-1) - 1 / (m+1)^(s-1))` summed from `n` converges to `g(s)`.
2. The series of terms `(1 - (s - 1) * log(m)) / m^s - (log(m+1) / (m+1)^(s-1) - log(m) / m^(s-1))` summed from `n` converges to `g'(s)`.
3. The complex function `g` has a complex derivative `g'` at `s` with value `g'(s)`.

### Informal sketch
- The proof proceeds by discharging the assumption `1 <= n`.
- It uses `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` to relate the convergence of a function series to the derivative of its limit function.
- The goal is to show that the series converges, and that the term-by-term derivative also converges to the derivative of the limit.
- After rewriting with `OPEN_HALFSPACE_RE_GT`, the proof splits into two main subgoals corresponding to verifying the convergence of the function and its derivative.
- The proof involves showing the existence of appropriate `g` and `g'` satisfying the given conditions.
- The proof involves bounding the tail of the series using `GENZETA_CONVERGES`, which establishes convergence of a generalized zeta function under certain conditions, in order to prove summability.
- It uses `NEARZETA_BOUND_LEMMA` to bound the difference quotients appearing in the definition of the derivative.

### Mathematical insight
This theorem establishes the existence of a holomorphic function `g(s)` defined by a series closely related to the zeta function, and relates `g(s)` to the derivative of the series. This is a step in showing that the completed zeta function extends to a meromorphic function with a pole at s = 1.

### Dependencies
- `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`
- `OPEN_HALFSPACE_RE_GT`
- `IN_ELIM_THM`
- `real_gt`
- `COMPLEX_DIFF_TAC`
- `CPOW_EQ_0`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `REAL_LT_MIN`
- `REAL_LT_01`
- `REAL_HALF`
- `complex_div`
- `SUMMABLE_COMPLEX_LMUL`
- `GENZETA_CONVERGES`
- `RE_CX`
- `complex_div`
- `COMPLEX_MUL_LID`
- `summable`
- `from`
- `CPOW_REAL_REAL`
- `REAL_CX`
- `REAL_OF_NUM_LT`
- `LE_1`
- `GSYM CX_DIV`
- `GSYM CX_POW`
- `REAL_LE_DIV`
- `REAL_EXP_POS_LE`
- `REAL_POW_LE`
- `IN_BALL`
- `dist`
- `NEARZETA_BOUND_LEMMA`
- `COMPLEX_NORM_GE_RE_IM`
- `RE_SUB`
- `complex_div`
- `COMPLEX_MUL_ASSOC`
- `COMPLEX_NORM_MUL`
- `REAL_LE_MUL2`
- `NORM_POS_LE`
- `COMPLEX_NORM_MUL`
- `COMPLEX_POW_2`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `COMPLEX_NORM_INV`
- `NORM_CPOW_REAL`
- `LOG_POS`
- `REAL_OF_NUM_LE`
- `RE_ADD`

### Porting notes
- The proof relies heavily on complex analysis lemmas, particularly those related to complex differentiation, series convergence, and inequalities involving norms.
- The `NEARZETA_BOUND_LEMMA` is likely a key component that would need to be ported or re-proven.
- The `GENZETA_CONVERGES` lemma regarding the convergence of the generalized zeta function is also essential.


---

## HOLOMORPHIC_NEARZETA_STRONG

### Name of formal statement
HOLOMORPHIC_NEARZETA_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA_STRONG = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
               Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums (nearzeta n s)) (from n) /\
              ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                    Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) /
                     Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) /
                     Cx(&m) cpow (s - Cx(&1))))
               sums (complex_derivative(nearzeta n) s)) (from n) /\
          ((nearzeta n) has_complex_derivative
           complex_derivative(nearzeta n) s) (at s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_LEMMA) THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:complex->complex`; `g':complex->complex`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [FORALL_AND_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < Re s
        ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
    ASM_MESON_TAC[summable];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 < Re z ==> nearzeta n z = g z` ASSUME_TAC THENL
   [ASM_MESON_TAC[SERIES_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!z. &0 < Re z ==> ((nearzeta n) has_complex_derivative g' z) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:complex->complex`; `Re z`] THEN
    ASM_SIMP_TAC[dist] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `w - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DERIVATIVE]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if `1 <= n` and `0 < Re s`, then
1. The series with terms `(s - 1) / m^s - (1 / m^(s - 1) - 1 / (m + 1)^(s - 1))` sums to `nearzeta n s` starting from `m = n`.
2. The series with terms `(1 - (s - 1) * log(m)) / m^s - (log(m + 1) / (m + 1)^(s - 1) - log(m) / m^(s - 1))` sums to the complex derivative of `nearzeta n` at `s` starting from `m = n`.
3. `nearzeta n` has a complex derivative `complex_derivative(nearzeta n) s` at `s`.

### Informal sketch
The theorem asserts the holomorphicity of the `nearzeta` function. The proof proceeds as follows:

- Assume `1 <= n` and `0 < Re s`.
- Apply `HOLOMORPHIC_NEARZETA_LEMMA` to decompose the problem into showing the complex differentiability and the convergence of its derivative.
- Rewrite using `IN_ELIM_THM` and `real_gt` to simplify inequalities.
- Introduce complex functions `g` and `g'` as candidate complex derivative.
- Distribute the goal into three subgoals about convergence 1. series sums to `nearzeta n s`, 2. derivative of series sums to complex derivative of `nearzeta n` at `s` and 3. complex differentiability.
- Prove the first subgoal by rewriting with definitions of `nearzeta` and `SUMS_INFSUM`, then applying `ASM_MESON_TAC` with `summable`.
- Prove the second subgoal by showing `nearzeta n z = g z` where `&0 < Re z` and `SERIES_UNIQUE`.
- Simplify using `ASM_SIMP_TAC`.
- Prove the third subgoal by showing `nearzeta n` has complex derivative `g' z` at `z` where `&0 < Re z`. `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` is used to establish complex differentiability of nearzeta.
- Finally, apply `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`.

### Mathematical insight
This theorem provides a strong result about the `nearzeta` function: it is holomorphic. Holomorphic functions are central to complex analysis, and this result allows us to apply the tools of complex analysis to the `nearzeta` function. The theorem expresses that the `nearzeta` function not only has a complex derivative, but also provides a series representation for both the function and its derivative, which are absolutely essential for complex analysis.

### Dependencies
- `HOLOMORPHIC_NEARZETA_LEMMA`
- `IN_ELIM_THM`
- `real_gt`
- `LEFT_IMP_EXISTS_THM`
- `FORALL_AND_THM`
- `TAUT a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`
- `nearzeta`
- `SUMS_INFSUM`
- `summable`
- `SERIES_UNIQUE`
- `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`
- `COMPLEX_NORM_GE_RE_IM`
- `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`

### Porting notes (optional)
- The definition of complex differentiability and `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` may require some attention, as different proof assistants may have different ways of defining and reasoning about complex derivatives.
- The convergence proofs rely on `SUMS_INFIMUM`, so a port needs to either have this result from HOL Light or be able to prove a similar summability lemma.


---

## NEARZETA_CONVERGES

### Name of formal statement
NEARZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_CONVERGES = prove
 (`!n s. &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  MATCH_MP_TAC SUMMABLE_EQ_COFINITE THEN EXISTS_TAC `from(n + 1)` THEN
  SUBGOAL_THEN
   `from(n + 1) DIFF from n UNION from n DIFF from(n + 1) = {n}`
   (fun th -> REWRITE_TAC[th; FINITE_INSERT; FINITE_RULES])
  THENL
   [SIMP_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_SING] THEN ARITH_TAC;
    MP_TAC(SPECL [`n + 1`; `s:complex`] HOLOMORPHIC_NEARZETA_STRONG) THEN
    ASM_REWRITE_TAC[summable] THEN ANTS_TAC THENL [ARITH_TAC; MESON_TAC[]]]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if the real part of `s` is greater than 0, then the series whose `m`-th term is `(s - 1) / m^s - (1 / m^(s - 1) - 1 / (m + 1)^(s - 1))` sums to `nearzeta n s` from `n` onwards.

### Informal sketch
The proof proceeds as follows:
- Rewrite the goal using the definitions of `nearzeta` and `SUMS_INFSUM`.
- Apply `SUMMABLE_EQ_COFINITE` to reduce the problem to showing that the set of indices where the summand is non-summable is cofinite.
- Prove `from(n + 1) DIFF from n UNION from n DIFF from(n + 1) = {n}` using basic set theory and arithmetic.
- Use `HOLOMORPHIC_NEARZETA_STRONG` and rewrite with `summable` to show that the summand is summable for indices greater than `n`.
- Use arithmetic and a Meson tactic to complete the proof.

### Mathematical insight
The theorem states that the `nearzeta` function, a variant of the Riemann zeta function, is the limit of a particular series. This provides an explicit connection between the function and its series representation, which is crucial for analyzing its behavior and properties. This theorem confirms the convergence of the series representation under the condition that the real part of `s` is greater than 0.

### Dependencies
- Definitions: `nearzeta`, `SUMS_INFSUM`, `summable`

- Theorems: `SUMMABLE_EQ_COFINITE`, `FINITE_INSERT`, `FINITE_RULES`, `EXTENSION`, `IN_DIFF`, `IN_UNION`, `IN_FROM`, `IN_SING`, `HOLOMORPHIC_NEARZETA_STRONG`


---

## SUMS_COMPLEX_DERIVATIVE_NEARZETA

### Name of formal statement
SUMS_COMPLEX_DERIVATIVE_NEARZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMS_COMPLEX_DERIVATIVE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) / Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) / Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) / Cx(&m) cpow (s - Cx(&1)))) sums
            (complex_derivative (nearzeta n) s)) (from n)`,
  SIMP_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;
```
### Informal statement
For all natural numbers `n` and complex numbers `s`, if `n` is greater than or equal to 1 and the real part of `s` is greater than 0, then the sum of the sequence defined by the function `\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) / Cx(&m) cpow s - (clog(Cx(&(m + 1))) / Cx(&(m + 1)) cpow (s - Cx(&1)) - clog(Cx(&m)) / Cx(&m) cpow (s - Cx(&1)))` from `n` onwards converges to the complex derivative of the `nearzeta n` function at `s`.

### Informal sketch
The proof demonstrates the convergence of a series related to the derivative of the `nearzeta` function by showing that the given series sums to the `complex_derivative (nearzeta n) s`. The main step involves using the theorem `HOLOMORPHIC_NEARZETA_STRONG` to establish the holomorphicity of the `nearzeta` function. The SIMP_TAC simplifies the goal using `HOLOMORPHIC_NEARZETA_STRONG`. The goal will simplify to showing that the derivative can be expressed as a convergent complex series.

### Mathematical insight
This theorem establishes a connection between an infinite series and the derivative of the `nearzeta` function. The `nearzeta` function is a partial zeta function. The result provides an analytical expression for the derivative of `nearzeta` as a convergent sum which could be used to understand the analytical properties of this function.

### Dependencies
- `HOLOMORPHIC_NEARZETA_STRONG`

### Porting notes (optional)
The main challenge in porting this theorem lies in ensuring that the definitions of `nearzeta`, `complex_derivative`, `clog`, `cpow`, and `sums` are consistent across different proof assistants. Care must be taken with the complex number representation and the definition of complex power. The `HOLOMORPHIC_NEARZETA_STRONG` theorem is crucial, so a suitable equivalent must be available to successfully port this theorem.


---

## HOLOMORPHIC_NEARZETA

### Name of formal statement
HOLOMORPHIC_NEARZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA = prove
 (`!n. 1 <= n ==> (nearzeta n) holomorphic_on {s | Re(s) > &0}`,
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
  REWRITE_TAC[real_gt] THEN MESON_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;
```

### Informal statement
For all natural numbers `n`, if `n` is greater than or equal to 1, then the function `nearzeta n` is holomorphic on the set of complex numbers `s` such that the real part of `s` is greater than 0.

### Informal sketch
The proof demonstrates that `nearzeta n` is holomorphic on the right half-plane {s | Re(s) > 0}.

- The proof starts by using `SIMP_TAC` with theorems `HOLOMORPHIC_ON_OPEN`, `OPEN_HALFSPACE_RE_GT`, and `IN_ELIM_THM`. These theorems establish that being holomorphic on an open set is equivalent to being holomorphic on a set. Also it states that the half-plane defined by Re(s) > 0 is an open set and `IN_ELIM_THM` likely helps eliminate the set membership predicate.
- Next, `REWRITE_TAC[real_gt]` simplifies inequalities involving real numbers.
- Finally, `MESON_TAC[HOLOMORPHIC_NEARZETA_STRONG]` automatically discharges the theorem using `HOLOMORPHIC_NEARZETA_STRONG`, a previously proven "stronger" version of the theorem. This lemma likely already proves the holomorphicity on the desired halfplane.

### Mathematical insight
This theorem establishes an important property of the `nearzeta` function for natural number inputs: it is holomorphic on the right half-plane. Holomorphic functions are complex-differentiable and thus very well-behaved. The `nearzeta` function is likely a variant or approximation of the Riemann zeta function, so knowing it has certain analytic properties is important.

### Dependencies
- `HOLOMORPHIC_ON_OPEN`
- `OPEN_HALFSPACE_RE_GT`
- `IN_ELIM_THM`
- `real_gt`
- `HOLOMORPHIC_NEARZETA_STRONG`


---

## COMPLEX_DIFFERENTIABLE_NEARZETA

### Name of formal statement
COMPLEX_DIFFERENTIABLE_NEARZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DIFFERENTIABLE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s ==> (nearzeta n) complex_differentiable (at s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_STRONG) THEN
  MESON_TAC[complex_differentiable]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if `1 <= n` and the real part of `s` is greater than `0`, then the function `nearzeta n` is complex differentiable at `s`.

### Informal sketch
The proof proceeds as follows:
- Assume the hypotheses: `1 <= n` and `&0 < Re s`.
- Apply `HOLOMORPHIC_NEARZETA_STRONG` using `MATCH_MP` to discharge the hypothesis `1 <= n`. This gives us that `nearzeta n` is holomorphic.
- Apply `complex_differentiable` lemma to conclude that since `nearzeta n` is holomorphic, it is also complex differentiable at `s`.

### Mathematical insight
This theorem establishes that the `nearzeta` function (a variant of the Hurwitz zeta function) is complex differentiable at any point `s` with a positive real part, provided the parameter `n` is at least 1. This is a crucial property for analyzing the analytic behavior of the `nearzeta` function, which is important for studying its connections to number theory and other areas of mathematics. The proof relies on the fact that holomorphic functions are complex differentiable.

### Dependencies
- Theorems: `HOLOMORPHIC_NEARZETA_STRONG`
- Definitions: `complex_differentiable`, `nearzeta`


---

## NEARZETA_1

### Name of formal statement
NEARZETA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_1 = prove
 (`!n. 1 <= n ==> nearzeta n (Cx(&1)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; COMPLEX_SUB_REFL] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC `\n:num. (vec 0:complex)` THEN
  REWRITE_TAC[SERIES_0; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; IN_FROM; complex_div] THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[complex_pow] THEN
  CONV_TAC COMPLEX_RING);;
```
### Informal statement
For all natural numbers `n`, if `1 <= n`, then `nearzeta n (Cx(&1)) = Cx(&0)`.

### Informal sketch
The proof demonstrates that for any natural number `n` greater than or equal to 1, the near-zeta function `nearzeta n` applied to the complex number `Cx(&1)`, which represents 1 as a complex number, equals the complex number `Cx(&0)`, which represents 0 as a complex number.

- The proof starts by rewriting `nearzeta` using its definition and simplifying the resulting expression via reflexivity of complex subtraction (`COMPLEX_SUB_REFL`).
- It then applies `INFSUM_UNIQUE` and `SUMS_EQ` which relates to the uniqueness of infinite sums and equality of sums.
- The goal is then transformed by introducing an existential quantifier `EXISTS_TAC` to find a function mapping natural numbers `n` to the complex zero vector `vec 0`.
- The proof proceeds by rewriting the goal using `SERIES_0` (which says that the sum of a series of zeros is zero) and the fact that the complex zero vector is the same as 0 (`GSYM COMPLEX_VEC_0`).
- Then uses `COMPLEX_VEC_0` to rewrite complex vector 0 to `Cx(&0)` and simplification of the expression `IN_FROM` which transforms `x IN (num_FROM m)` to `m <= x`.
- Generalizing `m` and discharging the assumption.
- A subgoal is created to prove that `m` is not equal to 0. We prove `~(m = 0)` using `ASM_ARITH_TAC`
- It simplifies the expression using properties of complex powers (`CPOW_N`), injectivity of the complex constructor (`CX_INJ`), equivalence of real numbers and natural numbers (`REAL_OF_NUM_EQ`), and basic arithmetic identities
- The expression is further simplified by rewriting using the definition of complex powers (`complex_pow`).
- The last step involves complex ring conversion `COMPLEX_RING`.

### Mathematical insight
The theorem shows a specific value of the `nearzeta` function, namely at `Cx(&1)`. It highlights the behavior of this function for input values starting from 1.
Specifically, for any natural number `n` greater than or equal to 1, `nearzeta n (Cx(&1))` results in `Cx(&0)`. This is a useful result because it helps to understand behavior of `nearzeta n` on specific complex arguments representing a starting point for investigation of the function's properties for larger arguments.

### Dependencies
- `nearzeta`
- `COMPLEX_SUB_REFL`
- `INFSUM_UNIQUE`
- `SUMS_EQ`
- `SERIES_0`
- `COMPLEX_VEC_0`
- `IN_FROM`
- `complex_div`
- `CPOW_N`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `ADD_EQ_0`
- `ARITH_EQ`
- `complex_pow`
- `COMPLEX_RING`


---

## HOLOMORPHIC_ZETA

### Name of formal statement
HOLOMORPHIC_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_ZETA = prove
 (`zeta holomorphic_on {s | Re(s) > &0 /\ ~(s = Cx(&1))}`,
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[zeta; genzeta] THEN
  MATCH_MP_TAC HOLOMORPHIC_TRANSFORM THEN
  EXISTS_TAC `\z. (nearzeta 1 z + Cx(&1) / Cx(&1) cpow (z - Cx(&1))) /
                  (z - Cx(&1))` THEN
  SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  SIMP_TAC[IN_ELIM_THM; COMPLEX_SUB_0; HOLOMORPHIC_ON_SUB;
           HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `{s | Re s > &0}` THEN
    SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; ETA_AX] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
    REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ]]);;
```

### Informal statement
The Riemann zeta function `zeta` is holomorphic on the set of complex numbers `s` such that the real part of `s` is greater than 0, excluding the point `s = 1`.

### Informal sketch
The proof demonstrates that the `zeta` function is holomorphic on the specified domain by showing that it can be expressed as the sum of a holomorphic function `nearzeta 1 z` and a term `Cx(&1) / Cx(&1) cpow (z - Cx(&1))) / (z - Cx(&1))`.
- The proof starts by rewriting the `zeta` function using the definition `genzeta` and `ETA_AX`.
- The `HOLOMORPHIC_TRANSFORM` tactic is then applied to express the function as the sum of a holomorphic part `nearzeta 1 z` and a remainder term.
- It is shown that the remainder term `Cx(&1) / Cx(&1) cpow (z - Cx(&1))) / (z - Cx(&1))` is holomorphic on the domain. This uses the chain of reasoning:
  - Dividing by `(z - Cx(&1))` is holomorphic.
  - The complex power `cpow` is holomorphic where the real part is greater than 0, excluding 1.
- Finally, the theorem `HOLOMORPHIC_ON_ADD` is applied to prove that the sum of the two parts is holomorphic, thus demonstrating that the zeta function is holomorphic on the set `{s | Re(s) > &0 /\ ~(s = Cx(&1))}`.

### Mathematical insight
This theorem establishes a fundamental property of the Riemann zeta function, namely its holomorphicity on a significant portion of the complex plane. This is crucial for analytic continuation and for studying the zeta function's behavior.

### Dependencies
- Definitions:
  - `zeta`
  - `genzeta`
  - `holomorphic_on`
  - `complex_differentiable`
  - `nearzeta`
  - `cpow`
- Theorems:
  - `ETA_AX`
  - `HOLOMORPHIC_TRANSFORM`
  - `IN_ELIM_THM`
  - `HOLOMORPHIC_ON_DIV`
  - `COMPLEX_SUB_0`
  - `HOLOMORPHIC_ON_SUB`
  - `HOLOMORPHIC_ON_CONST`
  - `HOLOMORPHIC_ON_ID`
  - `HOLOMORPHIC_ON_ADD`
  - `HOLOMORPHIC_ON_SUBSET`
  - `HOLOMORPHIC_NEARZETA`
  - `LE_REFL`
  - `SUBSET`
  - `CPOW_EQ_0`
  - `CX_INJ`
  - `REAL_OF_NUM_EQ`

### Porting notes (optional)
- The biggest challenge would be porting the `HOLOMORPHIC_TRANSFORM` theorem, which establishes the decomposition into a holomorphic part and a remainder. The proof of this auxiliary theorem would likely require significant effort.
- The concept of holomorphicity and complex differentiability should be available in most proof assistants, though the exact names and definitions may vary.
- Complex arithmetic and power functions might require the use of external libraries.


---

## COMPLEX_DIFFERENTIABLE_AT_ZETA

### Name of formal statement
COMPLEX_DIFFERENTIABLE_AT_ZETA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COMPLEX_DIFFERENTIABLE_AT_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> zeta complex_differentiable at s`,
  MP_TAC HOLOMORPHIC_ZETA THEN
  REWRITE_TAC[SET_RULE `{s | P s /\ ~(s = a)} = {s | P s} DELETE a`] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DELETE; OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[complex_differentiable; IN_ELIM_THM; IN_DELETE; real_gt]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 0 and `s` is not equal to the complex number 1 (i.e., 1 + 0i), then the Riemann zeta function is complex differentiable at `s`.

### Informal sketch
The proof proceeds as follows:
- Start with the theorem `HOLOMORPHIC_ZETA` which states that the Riemann zeta function is holomorphic on the set of complex numbers `s` such that the real part of `s` is greater than 0 and `s` is not equal to 1. This uses `MP_TAC` to apply the theorem.
- Rewrite using the set rule `{s | P s /\ ~(s = a)} = {s | P s} DELETE a`, which removes the point `a` from the set of elements satisfying a condition `P s`.
- Simplify using theorems `HOLOMORPHIC_ON_OPEN`, `OPEN_DELETE`, and `OPEN_HALFSPACE_RE_GT`. This step shows that the domain on which the zeta function is holomorphic is an open set.
- Rewrite using the definition of `complex_differentiable`, `IN_ELIM_THM`, `IN_DELETE`, and `real_gt` to formally state the complex differentiability of the zeta function at the specified point `s`.

### Mathematical insight
This theorem establishes that the Riemann zeta function is complex differentiable at any complex number `s` with a real part greater than 0, except for the point `s = 1`. This is a fundamental property of the zeta function, crucial for its applications in analytic number theory. The zeta function's differentiability reflects its smoothness and allows for powerful analytical techniques to be applied.

### Dependencies
The proof relies on the following:

- Theorems:
    - `HOLOMORPHIC_ZETA`
    - `IN_ELIM_THM`
- Definitions:
    - `complex_differentiable`
- Rules:
    - `SET_RULE `{s | P s /\ ~(s = a)} = {s | P s} DELETE a``
- Other:
    - `MP_TAC`, `REWRITE_TAC`, `SIMP_TAC`
    - `OPEN_DELETE`, `OPEN_HALFSPACE_RE_GT`, `IN_DELETE`, `real_gt`, `HOLOMORPHIC_ON_OPEN`


---

## SERIES_DIVISORS_LEMMA

### Name of formal statement
SERIES_DIVISORS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SERIES_DIVISORS_LEMMA = prove
 (`!x p l k.
      ((\n. x(p * n)) sums l) k
      ==> ~(p = 0) /\
          (!n. (p * n) IN k <=> n IN k)
          ==> (x sums l) {n | n IN k /\ p divides n}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `p * N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV p`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (rand o rand) VSUM_IMAGE (lhand w))) THEN
  ASM_SIMP_TAC[FINITE_INTER_NUMSEG; EQ_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_NUMSEG] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; divides; LE_0] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all real-valued functions `x` on natural numbers, natural numbers `p`, and real numbers `l`, and sets of natural numbers `k`, if the series defined by `x(n)` sums to `l` with respect to `k`, and `p` is not equal to 0, and for all natural numbers `n`, `p * n` is in `k` if and only if `n` is in `k`, then the series defined by `x(n)` sums to `l` with respect to the set of natural numbers `n` such that `n` is in `k` and `p` divides `n`.

### Informal sketch

*   The proof starts by assuming the hypothesis: `((\n. x(p * n)) sums l) k` and `~(p = 0) /\ (!n. (p * n) IN k <=> n IN k)`.
*   The definition of `sums` (`LIM_SEQUENTIALLY`) is unfolded.
*   The monotonicity of the universal quantifier over reals is used to introduce an arbitrary real number `e`, assuming `0 < e`.
*   We then choose `N` based on the assumption that `(\n. x(p * n)) sums l` with respect to `k`, so that `abs(l - (VSUM k (\n. x(p * n)) {0..N})) < e`.
*   We select `p * N` as the bound for the required `N` for the conclusion `(x sums l) {n | n IN k /\ p divides n}`.
*   A natural number `n` is introduced, and the assumption `p divides n` is discharged.
*   The fact that `< p divides (p * (n DIV p) )` is used to simplify the condition `n IN {n | n IN k /\ p divides n}` when `p divides n`.
*   `LE_RDIV_EQ` and the assumption `p divides n` are used to show that `p * (n DIV p) = n`.
*   The goal is then transformed into a statement about finite sums using `VSUM_IMAGE` (sums over the image of multiplication by `p`), and simplified using facts about finite intersection of number segments and cancellation of multiplication.
*   Finally, the definitions of set extension, image, the elimination theorem for `IN`, intersection, and number segments are used in conjunction with arithmetic facts to complete the proof.

### Mathematical insight
The theorem relates the convergence of a series to the convergence of a related series where the terms are scaled by a factor `p`. The set `k` acts as a condition of convergence, and the theorem shows that if the series indexed over `k` converges when the index is scaled by `p`, then the original series indexed by the elements of `k` that are divisible by `p` converges as well. This lemma is likely to be used in the proof of the Euler product formula to manipulate the index sets of infinite sums and products.

### Dependencies

*   `sums`
*   `LIM_SEQUENTIALLY`
*   `MONO_FORALL`
*   `VSUM_IMAGE`
*   `FINITE_INTER_NUMSEG`
*   `EQ_MULT_LCANCEL`
*   `EXTENSION`
*   `IN_IMAGE`
*   `IN_ELIM_THM`
*   `IN_INTER`
*   `IN_NUMSEG`
*   `LE_RDIV_EQ`
*   `divides`
*   `LE_0`

### Porting notes (optional)
*   The proof relies heavily on rewriting and simplification with arithmetic facts, which may require some effort to replicate in other proof assistants.
*   The use of set comprehension and image operations is central to managing the summation indices, so the target proof assistant's handling of these concepts should be considered.


---

## EULER_PRODUCT_LEMMA

### Name of formal statement
EULER_PRODUCT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_PRODUCT_LEMMA = prove
 (`!s ps. &1 < Re s /\ FINITE ps /\ (!p. p IN ps ==> prime p)
          ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums
               (cproduct ps (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s))
       {n | 1 <= n /\ !p. prime p /\ p divides n ==> ~(p IN ps)}`,
  let lemma = prove
   (`(x sums (k + l)) (s UNION t) /\ s INTER t = {}
     ==> (x sums k) s ==> (x sums l) t`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[sums] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN REWRITE_TAC[VECTOR_ADD_SUB] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ABS_TAC THEN ASM_SIMP_TAC[SET_RULE
     `s INTER t = {}
      ==> t INTER u = (((s UNION t) INTER u) DIFF (s INTER u))`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_DIFF THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG] THEN SET_TAC[]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ZETA_CONVERGES; COMPLEX_MUL_LID; NOT_IN_EMPTY; GSYM from] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `ps:num->bool`] THEN
  REWRITE_TAC[IN_INSERT; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(Cx(&p) cpow s)` o MATCH_MP
    SERIES_COMPLEX_LMUL) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `x * Cx(&1) * y = Cx(&1) * x * y`] THEN
  REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN REWRITE_TAC[GSYM complex_div] THEN
  ASM_SIMP_TAC[GSYM CPOW_MUL_REAL; REAL_CX; RE_CX; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_OF_NUM_MUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[]
   (ISPEC `\n. Cx(&1) / Cx(&n) cpow s` SERIES_DIVISORS_LEMMA))) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    ASM_REWRITE_TAC[MULT_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_PRIME_FACTOR; PRIME_1];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `a * x + (Cx(&1) - a) * x = x`] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN FIRST_X_ASSUM(fun th ->
    MP_TAC th THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC) THEN
  SET_TAC[]);;
```

### Informal statement
For all complex numbers `s` and sets of numbers `ps`, if the real part of `s` is greater than 1, `ps` is finite, and every element `p` in `ps` is a prime number, then the series whose `n`-th term is `Cx(1) / Cx(n) cpow s` sums to the product over all `p` in `ps` of `Cx(1) - inv(Cx(p) cpow s)` multiplied by the Riemann zeta function at `s`, where the summation ranges over all `n` such that `1 <= n` and for all primes `p`, if `p` divides `n`, then `p` is not in `ps`.

### Informal sketch
The proof proceeds by strong induction on the size of finite set `ps` of primes.

- Base case: `ps` is empty. In this case, we need to show that the series formed by `Cx(1) / Cx(n) cpow s` sums to `zeta s` where summation is over all `n` such that `1 <= n`. This follows from the definition of Riemann zeta function `zeta`.
- Inductive step: Assume the result holds for all sets of primes of size `k`. We want to show it holds for a set `ps` of primes of size `k+1`. We can write `ps` as `INSERT p ps'` where `p` is a prime not in `ps'`.
    - The goal is to prove: `(\n. Cx(&1) / Cx(&n) cpow s) sums (cproduct (INSERT p ps') (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)` where summation ranges over all `n` such that `1 <= n` and for all primes `p'`, if `p'` divides `n`, then `p'` is not in `INSERT p ps'`.
    - Using the inductive hypothesis, `(\n. Cx(&1) / Cx(&n) cpow s) sums (cproduct ps' (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)` where summation ranges over all `n` such that `1 <= n` and for all primes `p'`, if `p'` divides `n`, then `p'` is not in `ps'`.
    - The series is split into two parts based on whether `p` divides `n` or not.
    - Then we use the lemma that allows to split a sum over a union of disjoint sets in the sums over the individual sets.
    - The lemma used has premises `(x sums (k + l)) (s UNION t) /\ s INTER t = {} ==> (x sums k) s ==> (x sums l) t`.

### Mathematical insight
This theorem establishes the Euler product formula for the Riemann zeta function. It expresses the zeta function as an infinite product over prime numbers. This formula is fundamental in analytic number theory, connecting the zeta function (defined as an infinite sum) to the distribution of prime numbers. The condition `Re s > 1` is required for the convergence of both the infinite sum and the infinite product.

### Dependencies
- Definitions
  - `sums` : Represents the summation of a series.
  - `cproduct`: Complex product.
  - `zeta`: Riemann Zeta function.
  - `cpow`: Complex power.
  - `Cx`: Converts a Real to a Complex number.
  - `inv`: Multiplicative inverse.
- Theorems
  - `ZETA_CONVERGES`: Convergence of the Riemann zeta function.
  - `SERIES_COMPLEX_LMUL`: Complex multiplication and summation.
  - `SERIES_DIVISORS_LEMMA`: Series and divisors.
  - `PRIME_0`: 0 is not a prime.
  - `PRIME_DIVPROD_EQ`: Relates prime divisors.
  - `PRIME_PRIME_FACTOR`: Every number has a prime factor.
  - `PRIME_1`: 1 is not prime.
  - `COMPLEX_MUL_LID`: Complex multiplication identity.
  - `COMPLEX_INV_MUL`: Complex inverse and multiplication.
  - `CPRODUCT_CLAUSES`: Clauses defining the `cproduct` function.
  - `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets.

### Porting notes (optional)
- The definition of `sums` and the properties of complex numbers and their arithmetic will be essential.
- The handling of finiteness and the inductive proof over finite sets might require adaptation depending on the target proof assistant's library.
- The tactic `SET_TAC` appears to be related to simplification using set theory reasoning. Lean or Coq equivalents may significantly differ.


---

## SUMMABLE_SUBZETA

### Name of formal statement
SUMMABLE_SUBZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_SUBZETA = prove
 (`!s t. &1 < Re s /\ ~(0 IN t)
         ==> summable t (\n. Cx (&1) / Cx (&n) cpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_SUBSET THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_FROM] THEN ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
  MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(&1) / Cx(&n) cpow (Cx(Re s))` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[summable] THEN EXISTS_TAC `zeta (Cx(Re s))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN ASM_REWRITE_TAC[RE_CX];
    SIMP_TAC[IN_FROM; LE_1; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             GSYM CX_DIV; REAL_LE_DIV; REAL_POS; REAL_EXP_POS_LE];
    EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0; IN_FROM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_0; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_LE_REFL; REAL_OF_NUM_LT; LE_1]]);;
```

### Informal statement
For all complex numbers `s` and set of natural numbers `t`, if the real part of `s` is greater than 1, and 0 is not in `t`, then the series whose nth term is `1/n^s` is summable over the set `t`.

### Informal sketch
The proof proceeds as follows:
- The statement is proven by showing that the series `1/n^s` is summable when summed over from 1 onwards, which is proven using `SUMMABLE_SUBSET`.
- Establish that if `Re s > 1`, then `1 < Re s`.
- Apply a series comparison test (`SERIES_COMPARISON_COMPLEX`) comparing the complex series with the real series where `s` is replaced by `Re s`.
- Show that `1/n^(Re s)` is summable by comparison with the zeta function. The `ZETA_CONVERGES` theorem is used to establish the summability of the real series involving the zeta function.
- Establish the inequality `|1/n^s| <= 1/n^(Re s)` by examining the norms and real parts of the involved complex numbers. Then break it down into several steps.
  - Show that `|1/n^s| = 1 / |n^s|`.
  - Show that `|n^s| = n^(Re s)`.
  - Use the cases of if x is positive or not (`COND_CASES_TAC`).
  - Establish `n >= 1`.
  - Establish `Re s > 1`.

### Mathematical insight
This theorem states a condition for the summability of a subseries of the series defining the Riemann zeta function, where the exponent is a complex number. It is a generalization of the well-known result that the Riemann zeta function converges for complex numbers with real part greater than 1. The condition `0 IN t` is excluded to avoid division by zero.

### Dependencies
- `SUBSET`
- `IN_FROM`
- `LE_1`
- `SUMMABLE_SUBSET`
- `SERIES_COMPARISON_COMPLEX`
- `summable`
- `ZETA_CONVERGES`
- `RE_CX`
- `CPOW_REAL_REAL`
- `REAL_CX`
- `REAL_OF_NUM_LT`
- `GSYM CX_DIV`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_EXP_POS_LE`
- `GE`
- `LE_0`
- `NORM_0`
- `NORM_POS_LE`
- `COMPLEX_NORM_DIV`
- `NORM_CPOW_REAL`
- `REAL_LE_REFL`

### Porting notes (optional)
This theorem relies on the definition and properties of complex exponentiation (`cpow`) and the Riemann zeta function (`zeta`). Ensure these are defined appropriately in the target proof assistant. The `SERIES_COMPARISON_COMPLEX` tactic is crucial for the comparison test; a similar tactic or manual application of comparison test might be necessary in other systems.


---

## EULER_PRODUCT_MULTIPLY

### Name of formal statement
EULER_PRODUCT_MULTIPLY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_PRODUCT_MULTIPLY = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)
            --> Cx(&1)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
    `\n. infsum {m | 1 <= m /\ !p. prime p /\ p divides m
                                   ==> ~(p IN {p | prime p /\ p <= n})}
                (\n. Cx (&1) / Cx (&n) cpow s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC EULER_PRODUCT_LEMMA THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..n` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; LE_0; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l. ((\n. Cx (&1) / Cx (&n) cpow Cx(Re s)) sums l) (from 1)`
  MP_TAC THENL
   [MP_TAC(SPEC `Cx(Re s)` ZETA_CONVERGES) THEN
    ASM_SIMP_TAC[RE_CX] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SERIES_CAUCHY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF; GE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`s:complex`;
                 `{m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)}`]
                SUMMABLE_SUBZETA) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; ARITH] THEN
  REWRITE_TAC[GSYM SUMS_INFSUM] THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (MP_TAC o SPEC `N1 + N2 + 1`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN SIMP_TAC[NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `dist(x,z) < e / &2 /\ dist(y,z) <= dist(x,y) + dist(x,z)
    ==> dist(x,y) < e / &2 ==> dist(y,z) < e`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2 + 1`) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  REWRITE_TAC[dist] THEN SUBGOAL_THEN
   `vsum
     ({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
      (0..N1 + N2 + 1))
     (\n. Cx (&1) / Cx (&n) cpow s) - Cx(&1) =
    vsum
     (({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
       (0..N1 + N2 + 1)) DELETE 1)
     (\n. Cx (&1) / Cx (&n) cpow s)`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_DELETE_CASES; FINITE_INTER_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_ONE; IN_INTER] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    REWRITE_TAC[MESON[] `(!x. P x /\ x = 1 ==> Q x) <=> P 1 ==> Q 1`] THEN
    REWRITE_TAC[PRIME_1; IN_NUMSEG; ARITH; ARITH_RULE `1 <= a + b + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_NORM_VSUM_BOUND_SUBSET THEN
  REWRITE_TAC[FINITE_INTER_NUMSEG] THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_DELETE; IN_INTER; IN_ELIM_THM; IN_NUMSEG; IN_FROM] THEN
    ASM_MESON_TAC[PRIME_FACTOR; DIVIDES_LE; NUM_REDUCE_CONV `1 <= 0`;
                  LT_IMP_LE; LE_TRANS];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_INTER; IN_FROM] THEN STRIP_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_NORM_INV] THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
               NORM_CPOW_REAL] THEN
  SIMP_TAC[REAL_INV; REAL_CX; GSYM CX_INV; RE_CX; REAL_LE_REFL]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the following sequence converges to the complex number 1: The sequence is indexed by natural numbers `n`. The `n`-th term of the sequence is the product, over all prime numbers `p` less than or equal to `n`, of the complex numbers `1 - (1/p^s)`, multiplied by the Riemann zeta function evaluated at `s`. The convergence is understood in the sense of sequential limits.

### Informal sketch
The proof establishes the Euler product formula for the Riemann zeta function. The main steps are as follows:

- Start by stripping the goal and applying `LIM_TRANSFORM_EVENTUALLY`.
- The goal is to show that the limit of a product equals 1. The strategy is to rewrite the limit of the product as the limit of an infinite sum, using the reciprocal of numbers whose prime factors are all less than or equal to `n`.
- Show that the difference between the infinite sum and the zeta function converges to 0.
- Prove that the values in the infinite sum where some prime factor `p` of `m` satisfy `p > n` also converges to 0.
- Use the fact that `zeta s` converges if the real part of `s` is greater than 1.
- Proceed by showing the series is Cauchy.
- Decompose the original sequence into a finite sum and an associated infinite sum.
- Obtain a bound on the norm of the tail of the series.
- Apply `COMPLEX_NORM_VSUM_BOUND_SUBSET` to get a bound on the norm of the terms of the infinite sum.

### Mathematical insight
This theorem provides the Euler product formula for the Riemann zeta function, which connects the zeta function to prime numbers. The Riemann zeta function is defined as an infinite sum over all positive integers, and the Euler product formula expresses it as an infinite product over all prime numbers. This connection is fundamental in analytic number theory and has significant implications for understanding the distribution of prime numbers.

### Dependencies
- `LIM_TRANSFORM_EVENTUALLY`
- `INFSUM_UNIQUE`
- `EULER_PRODUCT_LEMMA`
- `IN_ELIM_THM`
- `FINITE_SUBSET`
- `FINITE_NUMSEG`
- `SUBSET`
- `LE_0`
- `IN_NUMSEG`
- `LIM_SEQUENTIALLY`
- `ZETA_CONVERGES`
- `RE_CX`
- `SERIES_CAUCHY`
- `REAL_HALF`
- `GE`
- `MONO_EXISTS`
- `MONO_FORALL`
- `SUMMABLE_SUBZETA`
- `ARITH`
- `GSYM SUMS_INFSUM`
- `sums`
- `NOT_LE`
- `REAL_ARITH`
- `DIST_TRIANGLE`
- `DIST_SYM`
- `dist`
- `VSUM_DELETE_CASES`
- `FINITE_INTER_NUMSEG`
- `DIVIDES_ONE`
- `IN_INTER`
- `CPOW_1`
- `COMPLEX_DIV_1`
- `PRIME_1`
- `ARITH_RULE`
- `COMPLEX_NORM_VSUM_BOUND_SUBSET`
- `IN_DELETE`
- `IN_FROM`
- `PRIME_FACTOR`
- `DIVIDES_LE`
- `NUM_REDUCE_CONV`
- `LT_IMP_LE`
- `LE_TRANS`
- `complex_div`
- `COMPLEX_MUL_LID`
- `COMPLEX_NORM_INV`
- `CPOW_REAL_REAL`
- `REAL_CX`
- `REAL_OF_NUM_LT`
- `LE_1`
- `NORM_CPOW_REAL`
- `REAL_INV`
- `GSYM CX_INV`
- `REAL_LE_REFL`


---

## ZETA_NONZERO_LEMMA

### Name of formal statement
ZETA_NONZERO_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_NONZERO_LEMMA = prove
 (`!s. &1 < Re s ==> ~(zeta s = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; LE_REFL] THEN
  REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_CX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the Riemann zeta function evaluated at `s` is not equal to the complex number 0.

### Informal sketch
The proof proceeds as follows:
- Assume that the real part of `s` is greater than 1.
- Apply the Euler product representation of the Riemann zeta function (`EULER_PRODUCT_MULTIPLY`).
- Rewrite using the limit definition of sequential convergence (`LIM_SEQUENTIALLY`). Specifically, the Euler product representation states that zeta(s) can be expressed as an infinite product over primes, which is then expressed as a limit.
- Instantiate the limit definition with `1/2`. This means showing that there exists an `n` such that for all `m >= n`, the norm of the difference between the partial product and zeta(s) is less than `1/2`.
- Choose a natural number `n` such that the norm of the difference between the partial product up to `n` and the limit is less than `1/2`. Then, the assumption that `zeta s` is zero leads to a contradiction after simplification.
- Simplify using properties of complex numbers, norms, and inequalities (`COMPLEX_MUL_RZERO`, `LE_REFL`, `dist`, `COMPLEX_SUB_LZERO`, `NORM_NEG`, `COMPLEX_NORM_CX`, `REAL_RAT_REDUCE_CONV`).

### Mathematical insight
This theorem asserts that the Riemann zeta function does not vanish for complex numbers with real part strictly greater than 1. This is a crucial property for establishing other results about the zeta function and its relation to the distribution of prime numbers. The Euler product representation, which connects the zeta function to prime numbers, is essential for this result.

### Dependencies
- `EULER_PRODUCT_MULTIPLY`
- `LIM_SEQUENTIALLY`
- `COMPLEX_MUL_RZERO`
- `LE_REFL`
- `dist`
- `COMPLEX_SUB_LZERO`
- `NORM_NEG`
- `COMPLEX_NORM_CX`
- `REAL_RAT_REDUCE_CONV`


---

## EULER_PRODUCT

### Name of formal statement
EULER_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_PRODUCT = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. inv(Cx(&1) - inv(Cx(&p) cpow s))))
            --> zeta(s)) sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (PAT_CONV `\x. ((\n. x) --> x) sq`)
   [GSYM COMPLEX_INV_INV] THEN
  MATCH_MP_TAC LIM_COMPLEX_INV THEN
  ASM_SIMP_TAC[COMPLEX_INV_EQ_0; ZETA_NONZERO_LEMMA] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(zeta(s))` o MATCH_MP LIM_COMPLEX_RMUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_MUL_RINV; COMPLEX_MUL_RID] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_INV; FINITE_ATMOST; COMPLEX_INV_INV]);;
```

### Informal statement
For all complex numbers `s` such that the real part of `s` is greater than 1, the limit as `n` tends to infinity of the product, over all primes `p` less than or equal to `n`, of `1/(1 - p^(-s))` is equal to the Riemann zeta function evaluated at `s`.

### Informal sketch
The proof shows the Euler product formula for the Riemann zeta function.
- The proof starts by stripping the goal and rewriting using `((\n. x) --> x) sq` and `GSYM COMPLEX_INV_INV`.
- It then applies `LIM_COMPLEX_INV`.
- Simplify using `COMPLEX_INV_EQ_0` and `ZETA_NONZERO_LEMMA`.
- Apply `EULER_PRODUCT_MULTIPLY` on an assumption.
- Discharge and apply `LIM_COMPLEX_RMUL` to an assumption.
- Rewrite using `COMPLEX_MUL_LID` and `GSYM COMPLEX_MUL_ASSOC`.
- Simplify using `ZETA_NONZERO_LEMMA`, `COMPLEX_MUL_RINV`, and `COMPLEX_MUL_RID`.
- Simplify using `GSYM CPRODUCT_INV`, `FINITE_ATMOST`, and `COMPLEX_INV_INV`.

### Mathematical insight
This theorem expresses the fundamental relationship between prime numbers and the Riemann zeta function. It states that the Riemann zeta function can be expressed as an infinite product over all prime numbers, reflecting the deep connection between analytic number theory and prime number distribution. This is a key identity in number theory.

### Dependencies
- Theorems: `COMPLEX_INV_EQ_0`, `ZETA_NONZERO_LEMMA`, `EULER_PRODUCT_MULTIPLY`, `COMPLEX_MUL_LID`, `COMPLEX_MUL_RINV`, `COMPLEX_MUL_RID`, `FINITE_ATMOST`
- Definitions: `zeta`, `cproduct`, `prime`, `Cx`, `cpow`, `Re`
- Lemmas: `LIM_COMPLEX_INV`, `COMPLEX_MUL_ASSOC`, `CPRODUCT_INV`, `COMPLEX_INV_INV`, `LIM_COMPLEX_RMUL`


---

## SUMS_GAMMA

### Name of formal statement
SUMS_GAMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMS_GAMMA = prove
 (`((\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))) -->
    complex_derivative (nearzeta 1) (Cx(&1))) sequentially`,
  MP_TAC(SPECL [`1`; `Cx(&1)`] SUMS_COMPLEX_DERIVATIVE_NEARZETA) THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG; RE_CX; REAL_LT_01; LE_REFL] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; CPOW_N; sums] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC[IN_NUMSEG; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH; REAL_OF_NUM_LT;
           ARITH_RULE `1 <= i ==> 0 < i /\ ~(i = 0)`; GSYM CX_LOG;
           ARITH_RULE `0 < i + 1`] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; REAL_DIV_1]);;
```

### Informal statement
The limit, as n approaches infinity, of the complex expression `Cx` applied to the sum from 1 to n of the function that maps `i` to `1/i - (log(i+1) - log(i))`, equals the complex derivative of the `nearzeta` function at `Cx(1)`.

### Informal sketch
The proof proceeds as follows:
- Apply `SUMS_COMPLEX_DERIVATIVE_NEARZETA` after specializing it to `1` and `Cx(&1)`.
- Simplify using `GSYM VSUM_CX`, `FINITE_NUMSEG`, `RE_CX`, `REAL_LT_01`, and `LE_REFL`.
- Rewrite using `COMPLEX_SUB_REFL`, `COMPLEX_MUL_LZERO`, `CPOW_N`, and `sums`.
- Apply a transformation rule `LIM_TRANSFORM_EVENTUALLY` after rewriting an implication as a conjunction (`IMP_CONJ`).
- Generalize using `ALWAYS_EVENTUALLY` and introduce the variable `n:num`.
- Apply a rewrite involving the intersection of number segments `FROM_INTER_NUMSEG`.
- Apply `VSUM_EQ`.
- Simplify using theorems about number segments, complex injections, real number conversions, addition, arithmetic, and logarithms of complex numbers.
- Rewrite with `complex_pow`, `COMPLEX_POW_1`, and `COMPLEX_SUB_RZERO`.
- Rewrite using `CX_DIV` and `CX_SUB` and `REAL_DIV_1`.

### Mathematical insight
This theorem relates the limit of a sum involving reciprocals and logarithms to the derivative of the nearzeta function at 1. It provides a connection between a discrete sum and a continuous function, and it shows that s = 1 is not a zero which is a necessary condition to prove the derivative exists.

### Dependencies
- `SUMS_COMPLEX_DERIVATIVE_NEARZETA`
- `GSYM VSUM_CX`
- `FINITE_NUMSEG`
- `RE_CX`
- `REAL_LT_01`
- `LE_REFL`
- `COMPLEX_SUB_REFL`
- `COMPLEX_MUL_LZERO`
- `CPOW_N`
- `sums`
- `IMP_CONJ`
- `LIM_TRANSFORM_EVENTUALLY`
- `ALWAYS_EVENTUALLY`
- `FROM_INTER_NUMSEG`
- `VSUM_EQ`
- `IN_NUMSEG`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `ADD_EQ_0`
- `ARITH`
- `REAL_OF_NUM_LT`
- `ARITH_RULE`
- `GSYM CX_LOG`
- `complex_pow`
- `COMPLEX_POW_1`
- `COMPLEX_SUB_RZERO`
- `CX_DIV`
- `CX_SUB`
- `REAL_DIV_1`


---

## ZETA_1_NZ

### Name of formal statement
ZETA_1_NZ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_1_NZ = prove
 (`~(zeta(Cx(&1)) = Cx(&0))`,
  REWRITE_TAC[zeta; genzeta] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 - log(&2) <= Re(complex_derivative (nearzeta 1) (Cx(&1)))`
  MP_TAC THENL
   [REWRITE_TAC[RE_DEF] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_LBOUND) THEN
    EXISTS_TAC `\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))` THEN
    REWRITE_TAC[SUMS_GAMMA; TRIVIAL_LIMIT_SEQUENTIALLY; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM RE_DEF; RE_CX] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH; REAL_DIV_1; LOG_1] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a - (b - &0) + c <=> &0 <= c`] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    SIMP_TAC[REAL_SUB_LE; GSYM LOG_DIV; REAL_OF_NUM_LT;
             ARITH_RULE `2 <= x ==> 0 < x /\ 0 < x + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SIMP_TAC[REAL_FIELD `&0 < x ==> (x + &1) / x = &1 + &1 / x`;
             REAL_OF_NUM_LT; ARITH_RULE `2 <= x ==> 0 < x`] THEN
    SIMP_TAC[LOG_LE; REAL_LE_DIV; REAL_POS];
    ASM_REWRITE_TAC[RE_CX; REAL_NOT_LE; REAL_SUB_LT] THEN
    GEN_REWRITE_TAC I [GSYM REAL_EXP_MONO_LT] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH] THEN
    SUBGOAL_THEN `(&1 + &1 / &2) pow 2 <= exp(&1 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_LE_X];
      ALL_TAC] THEN
    SIMP_TAC[GSYM REAL_EXP_N; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
The Riemann zeta function, `zeta(z)`, does not equal zero when evaluated at `z = 1`. In other words, it is not the case that `zeta(1) = 0`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting `zeta(1)` using the definitions of `zeta` and `genzeta`. This expresses `zeta(1)` in terms of limits and sums related to the digamma function.
- Discharge the assumption.
- Establish the subgoal `&1 - log(&2) <= Re(complex_derivative (nearzeta 1) (Cx(&1)))` and prove it using:
  - Rewrite the real part (`Re`) using its definition.
  - Apply `LIM_COMPONENT_LBOUND` after specializing it with `sequentially`.
  - Introduce an existential for a sequence `\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))`.
  - Rewrite sums, trivial limits sequentially, `DIMINDEX_2`, and arithmetic simplifications.
  - Rewrite using `EVENTUALLY_SEQUENTIALLY`.
  - Introduce an existential for `1` and then generalize and discharge `n:num`.
  - Rewrite using the definition of `Re` and `Cx`.
  - Perform assumptions simplification with `SUM_CLAUSES_LEFT`, arithmetic, `REAL_DIV_1` and `LOG_1`.
  - Rewrite the real arithmetic to obtain an inequality to prove.
  - Apply `SUM_POS_LE` and rewrite using `FINITE_NUMSEG` and `IN_NUMSEG`.
  - Simplify using `REAL_SUB_LE`, `GSYM LOG_DIV`, `REAL_OF_NUM_LT`, and arithmetic rules.
  - Rewrite using `GSYM REAL_OF_NUM_ADD`.
  - Simplify using real field properties and arithmetic.
  - Simplify using `LOG_LE` and related properties.
- Prove `&1 - log(&2) <= Re(complex_derivative (nearzeta 1) (Cx(&1)))` using the results of subsequent tactic applications.
- Negate using `REAL_NOT_LE` and `REAL_SUB_LT`.
- Rewrite using `REAL_EXP_MONO_LT` but generate on the left.
- Simplify by applying `EXP_LOG`, `REAL_OF_NUM_LT` and arithmetic.
- Set up the subgoal `(&1 + &1 / &2) pow 2 <= exp(&1 / &2) pow 2` before proving the primary goal with it. Using:
   - Apply `REAL_POW_LE2` and perform a conjunction split
   - Reduce real rationals and then use `ALL_TAC`
   - Rewrite using `REAL_EXP_LE_X`.
   - Use `ALL_TAC` again.
- Simplify using `GSYM REAL_EXP_N`, perform some real division, convert a real representation of a natural number to an equality and apply arithmetic.
- Finally use `REAL_ARITH_TAC` to automatically complete the proof.

### Mathematical insight
This theorem states that the Riemann zeta function does not vanish at `z = 1`. This is a basic result in complex analysis and number theory. The proof involves estimating the real part of the derivative of a related function (`nearzeta`) and demonstrating a lower bound that prevents the zeta function from being zero, thus, establishing the divergence of the harmonic series.

### Dependencies
**Definitions:**
- `zeta`
- `genzeta`
- `Re(z)`
- `nearzeta`

**Theorems:**
- `ISPEC`
- `LIM_COMPONENT_LBOUND`
- `SUMS_GAMMA`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `DIMINDEX_2`
- `EVENTUALLY_SEQUENTIALLY`
- `SUM_CLAUSES_LEFT`
- `SUM_POS_LE`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `LOG_DIV`
- `LOG_LE`
- `REAL_EXP_MONO_LT`
- `EXP_LOG`
- `REAL_POW_LE2`
- `REAL_EXP_LE_X`

**Tactics:**
- `REWRITE_TAC`
- `DISCH_TAC`
- `SUBGOAL_THEN`
- `MP_TAC`
- `MATCH_MP_TAC`
- `EXISTS_TAC`
- `X_GEN_TAC`
- `ASM_SIMP_TAC`
- `REAL_ARITH_TAC`
- `GEN_REWRITE_TAC`
- `SIMP_TAC`
- `CONJ_TAC`
- `ALL_TAC`
- `CONV_TAC`

### Porting notes (optional)
- The proof relies on specific tactics (`REAL_ARITH_TAC`) for real number reasoning, which highlights the importance of having similar automation in the target proof assistant, or be prepared to "unroll" real number reasoning into primitive proof steps manually.
- The use of `Cx` to represent complex numbers needs to be considered in the target system.
- The handling of limits and infinite sums will need to be mapped to the definitions and rules available in the target system.


---

## ZETA_MULTIPLE_BOUND

### Name of formal statement
ZETA_MULTIPLE_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_MULTIPLE_BOUND = prove
 (`!x y. real x /\ real y /\ &1 < Re x
       ==> &1 <= norm(zeta(x) pow 3 *
                      zeta(x + ii * y) pow 4 *
                      zeta(x + Cx(&2) * ii * y) pow 2)`,
  let lemma1 = prove
   (`&0 <= a /\ &0 <= b /\ &0 <= c /\
     c * (&2 * a + b) pow 3 / &27 <= x
     ==> c * a pow 2 * b <= x`,
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH
     `a pow 2 * b <= (&2 * a + b) pow 3 / &27 <=>
      &0 <= (&8 / &27 * a + &1 / &27 * b) * (a - b) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC)
  and lemma2 = prove
   (`-- &1 <= t /\ t <= &1
     ==> &0 <= &1 + r pow 2 - &2 * r * t`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= (&1 - t) * (&1 + t) /\ &0 <= (r - t) pow 2
      ==> &0 <= &1 + r pow 2 - &2 * r * t`) THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\n. cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow x))) pow 3 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow (x + ii * y)))) pow 4 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) -
                      inv(Cx(&p) cpow (x + Cx(&2) * ii * y)))) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    MATCH_MP_TAC EULER_PRODUCT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[LE_0] THEN X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_INV; COMPLEX_NORM_NZ; COMPLEX_INV_EQ_0] THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; ARITH; COMPLEX_INV_EQ_0;
               CPRODUCT_EQ_0; IN_ELIM_THM; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&1) - x = Cx(&0) <=> x = Cx(&1)`] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[TAUT `(~p \/ ~q) \/ ~r <=> p /\ q ==> ~r`] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `(norm:complex->real) o inv`) THEN
    REWRITE_TAC[COMPLEX_NORM_INV; o_THM; COMPLEX_NORM_CX; REAL_ABS_NUM;
                REAL_INV_INV; REAL_INV_1] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
                 REAL_EXP_EQ_1; REAL_CX; RE_CX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x /\ &0 < y ==> ~(x = &0 \/ y = &0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_POW; FINITE_ATMOST; GSYM CPRODUCT_MUL] THEN
  SIMP_TAC[GSYM CPRODUCT_INV; COMPLEX_INV_INV; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; GSYM COMPLEX_POW_INV; COMPLEX_INV_INV] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_ATMOST; REAL_INV_1] THEN
  MATCH_MP_TAC PRODUCT_LE_1 THEN SIMP_TAC[NORM_POS_LE; FINITE_ATMOST] THEN
  X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[CPOW_ADD; COMPLEX_MUL_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_INV_MUL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ASM_REWRITE_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
  REWRITE_TAC[GSYM CEXP_NEG; GSYM CEXP_N] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o CONV_RULE(REWR_CONV REAL))) THEN
  SIMP_TAC[GSYM CX_MUL; GSYM CX_NEG; GSYM CX_EXP; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `--(ii * x) = ii * --x`] THEN
  REWRITE_TAC[COMPLEX_RING `--(Cx(&2) * ii * x) = ii * Cx(&2) * --x`] THEN
  REWRITE_TAC[CEXP_EULER] THEN
  REWRITE_TAC[CCOS_NEG; CSIN_NEG; GSYM CX_SIN; GSYM CX_COS; GSYM CX_NEG;
              GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  SIMP_TAC[REAL_RING `(z:real) pow 4 = (z pow 2) pow 2`; COMPLEX_SQNORM] THEN
  REWRITE_TAC[COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RE_MUL_CX; RE_ADD; RE_MUL_II;
              IM_SUB; IM_CX; IM_MUL_CX; IM_ADD; IM_MUL_II] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_SUB_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_RING
   `(&1 - r * c) pow 2 + --(r * s) pow 2 =
    &1 + r pow 2 * (s pow 2 + c pow 2) - &2 * r * c`] THEN
  REWRITE_TAC[SIN_CIRCLE; REAL_POW_NEG; ARITH] THEN
  ABBREV_TAC `r = exp(--(Re x * log(&p)))` THEN
  REWRITE_TAC[COS_DOUBLE_COS; COS_NEG; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ABBREV_TAC `t = cos(Re y * log(&p))` THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ARITH
   `x - &2 * r * (&2 * y - &1) = x + &2 * r - &4 * r * y`] THEN
  MP_TAC(SPEC `Re y * log(&p)` COS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` MP_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SUBST1_TAC(GSYM REAL_EXP_0) THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < t <=> 2 <= t`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `r < &1 ==> abs(&1 - r) = (&1 - r)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  MATCH_MP_TAC lemma1 THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_SUB_LE; lemma2] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `&1 + s + &2 * r - &4 * r * t = &1 + s - &2 * r * (&2 * t - &1)`] THEN
    MATCH_MP_TAC lemma2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `-- &1 <= &2 * x pow 2 - &1 <=> &0 <= x * x`;
                REAL_ARITH `&2 * t pow 2 - &1 <= &1 <=> t pow 2 <= &1 pow 2`;
                REAL_LE_SQUARE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `x pow 3 * y pow 3 / &27 <= &1 <=> (x * y) pow 3 <= &3 pow 3`] THEN
  MATCH_MP_TAC REAL_POW_LE2_ODD THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (&1 + r pow 2 - &2 * r * t) + &1 + r pow 2 +
    &2 * r - &4 * r * t pow 2 =
    (&3 + &3 * r pow 2) - &2 * r * (&2 * t pow 2 + &2 * t - &1)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - r) * ((&3 + &3 * r pow 2) + &3 * r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH
     `c - &2 * r * y <= c + &3 * r <=> &0 <= r * (&2 * y + &3)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &2 * (&2 * t pow 2 + &2 * t - &1) + &3 <=>
                            &0 <= (t + &1 / &2) pow 2`] THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r pow 3` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE]; REAL_ARITH_TAC]);;
```

### Informal statement
For all real numbers `x` and `y`, if `x` is a real number and `y` is a real number and 1 is less than the real part of `x`, then 1 is less than or equal to the norm of (zeta(x) to the power of 3) multiplied by (zeta(x + i*y) to the power of 4) multiplied by (zeta(x + 2*i*y) to the power of 2).

### Informal sketch
The proof demonstrates a lower bound for the norm of a product of zeta functions.

- **Initial Simplification:** The theorem is initially processed by stripping off the assumptions and using `LIM_NORM_LBOUND` with the sequential limit. An existential is introduced.
- **Limit Argument:** The proof proceeds by demonstrating that the limit of a specific product involving prime numbers exists and equals the product of zeta functions involved in the statement. This involves manipulation of limits, complex powers, and Euler products.
- **Non-Zero Argument:** The absolute value of the involved limit term must be proven unequal to zero.
- **Product Manipulation:** Rewrites are performed to manipulate the product terms, including utilizing properties of `cproduct`, complex inverses, and norms.
- **Bounding Individual Terms:** The core of the proof involves establishing a lower bound for each term in the product over primes. The statement is reduced to showing that the norm of `1/(1 - 1/(p^x))` is less than or equal to 1, where p is a prime number, and x is a complex number.
- **Complex Arithmetic and Trigonometric Identities:** Complex arithmetic and trigonometric identities are applied to simplify the expression. Includes using `CPOW_ADD`, `COMPLEX_MUL_2`, `COMPLEX_POW_2`, `COMPLEX_INV_MUL`, `CEXP_NEG`, `CEXP_N`, `CEXP_EULER`, `CCOS_NEG`, `CSIN_NEG`. Also, `COMPLEX_SQNORM` and `SIN_CIRCLE` are employed.
- **Real Arithmetic and Inequalities:** Real arithmetic and inequalities are used extensively to derive the required lower bound.
- **Auxiliary Lemmas:** Two lemmas, `lemma1` and `lemma2`, are proven and applied.
    - `lemma1`: If `0 <= a`, `0 <= b`, `0 <= c`, and `c * (2*a + b)^3 / 27 <= x`, then `c * a^2 * b <= x`. This is used in bounding product terms.
    - `lemma2`: If `-1 <= t` and `t <= 1`, then `0 <= 1 + r^2 - 2*r*t`.
- **Final Bound:** Inequalities are combined to demonstrate the lower bound and complete the proof.

### Mathematical insight
The theorem provides a lower bound on the norm of a specific combination of zeta functions. This type of bound is useful in analytic number theory, particularly in the study of the distribution of prime numbers and zero-free regions of the Riemann zeta function. The proof uses careful estimates and manipulations of infinite products and complex functions.

### Dependencies
- `lemma1`: `REAL_ARITH`, `REAL_LE_LMUL`, `REAL_LE_MUL`, `REAL_POW_2`, `REAL_LE_SQUARE`
- `lemma2`: `REAL_ARITH`, `REAL_POW_2`, `REAL_LE_SQUARE`, `REAL_LE_MUL`
- `LIM_NORM_LBOUND`, `EVENTUALLY_SEQUENTIALLY`, `TRIVIAL_LIMIT_SEQUENTIALLY`, `LIM_COMPLEX_MUL`, `LIM_COMPLEX_POW`, `EULER_PRODUCT`, `real`, `RE_ADD`, `RE_MUL_CX`, `RE_MUL_II`, `REAL_NEG_0`, `REAL_ADD_RID`, `REAL_MUL_RZERO`, `LE_0`, `REAL_INV_INV`, `COMPLEX_NORM_INV`, `COMPLEX_NORM_NZ`, `COMPLEX_INV_EQ_0`, `COMPLEX_ENTIRE`, `COMPLEX_POW_EQ_0`, `ARITH`, `CPRODUCT_EQ_0`, `IN_ELIM_THM`, `FINITE_ATMOST`, `COMPLEX_RING`, `DE_MORGAN_THM`, `NOT_EXISTS_THM`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `REAL_INV_INV`, `NORM_CPOW_REAL`, `REAL_OF_NUM_LT`, `PRIME_IMP_NZ`, `LT_NZ`, `REAL_EXP_EQ_1`, `REAL_CX`, `RE_CX`, `LOG_POS_LT`, `PRIME_GE_2`, `GSYM CPRODUCT_POW`, `GSYM CPRODUCT_MUL`, `GSYM CPRODUCT_INV`, `COMPLEX_INV_INV`, `NORM_CPRODUCT`, `NORM_POS_LE`, `CPOW_ADD`, `COMPLEX_MUL_2`, `COMPLEX_POW_2`, `cpow`, `CX_INJ`, `REAL_OF_NUM_EQ`, `GSYM CX_LOG`, `LT_NZ`, `GSYM CEXP_NEG`, `GSYM CEXP_N`, `CEXP_EULER`, `CCOS_NEG`, `CSIN_NEG`, `GSYM CX_SIN`, `GSYM CX_COS`, `GSYM CX_NEG`, `GSYM CX_MUL`, `COMPLEX_NORM_MUL`, `COMPLEX_NORM_POW`, `REAL_RING`, `COMPLEX_SQNORM`, `RE_SUB`, `IM_SUB`, `COS_DOUBLE_COS`, `COS_NEG`, `GSYM CX_SUB`, `COMPLEX_NORM_CX`, `COS_BOUNDS`, `SUBST1_TAC`, `REAL_EXP_POS_LT`, `REAL_EXP_0`, `REAL_EXP_MONO_LT`, `REAL_LT_LNEG`, `REAL_LT_MUL`, `PRIME_GE_2`, `REAL_LT_IMP_LE`, `REAL_POW_LE`, `REAL_SUB_LE`, `REAL_LE_SQUARE`, `GSYM REAL_POW2_ABS`, `REAL_POW_LE2`, `REAL_POW_LE2_ODD`

### Porting notes (optional)
- The heavy reliance on `REAL_ARITH` and other arithmetic tactics might require adaptation depending on the target proof assistant's automation capabilities in real arithmetic.
- Libraries for complex numbers (zeta function, powers, norms, Euler's formula etc.) are necessary for porting and might have different naming conventions or slightly different formalizations.
- The tactic `ABBREV_TAC` is specific to HOL Light and needs to be replaced by equivalent ways to introduce abbreviations in other systems, ideally without affecting the proof structure, for easier comparison.


---

## ZETA_NONZERO

### Name of formal statement
ZETA_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(zeta s = Cx(&0))`,
  REWRITE_TAC[REAL_ARITH `&1 <= x <=> &1 < x \/ x = &1`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ZETA_NONZERO_LEMMA] THEN
  SUBST1_TAC(SPEC `s:complex` COMPLEX_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `y = Im s` THEN ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; ZETA_1_NZ] THEN
  DISCH_TAC THEN SUBGOAL_THEN
  `~(&1 <= norm((Cx(&0) *
                complex_derivative (\x. zeta(x + ii * Cx y)) (Cx(&1)) pow 4) *
                zeta (Cx(&1) + Cx (&2) * ii * Cx(y)) pow 2))`
  MP_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_MUL_LZERO] THEN REAL_ARITH_TAC;
    SIMP_TAC[]] THEN
  MATCH_MP_TAC(ISPEC `at (Cx(&1)) within {s | real s /\ &1 < Re s}`
   LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\x. zeta (x) pow 3 * zeta (x + ii * Cx(y)) pow 4 *
        zeta (x + Cx (&2) * ii * Cx(y)) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; TRIVIAL_LIMIT_WITHIN] THEN
  SUBGOAL_THEN `Cx(&1) limit_point_of {s | real s /\ &1 < Re s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIMPT_APPROACHABLE_LE] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN EXISTS_TAC `Cx(&1 + e)` THEN
    REWRITE_TAC[dist; CX_INJ; IN_ELIM_THM; REAL_CX; RE_CX] THEN
    REWRITE_TAC[GSYM CX_SUB; REAL_ADD_SUB; COMPLEX_NORM_CX] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
    SIMP_TAC[ZETA_MULTIPLE_BOUND; REAL_CX]] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_POW THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II; RE_II; RE_CX] THEN
    REWRITE_TAC[COMPLEX_RING `x + y = x <=> y = Cx(&0)`] THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (zeta x pow 3 * (x - Cx(&1)) pow 4) *
                  (zeta(x + ii * Cx y) / (x - Cx(&1))) pow 4` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; GSYM DIST_NZ; COMPLEX_SUB_0; COMPLEX_FIELD
     `~(x = Cx(&0))
      ==> (y * x pow 4) * (z / x) pow 4 - y * z pow 4 = Cx(&0)`] THEN
    SIMP_TAC[dist; COMPLEX_VEC_0; COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    SUBGOAL_THEN `((\x. zeta (x + ii * Cx y)) has_complex_derivative
                   complex_derivative (\x. zeta (x + ii * Cx y)) (Cx (&1)))
                  (at (Cx (&1)) within {s | real s /\ &1 < Re s})`
    MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN; COMPLEX_SUB_RZERO]] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
    SIMP_TAC[COMPLEX_DIFFERENTIABLE_ADD; COMPLEX_DIFFERENTIABLE_CONST;
             COMPLEX_DIFFERENTIABLE_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_II; COMPLEX_RING `x + y = x <=> y = Cx(&0)`;
                    IM_CX; COMPLEX_ENTIRE; II_NZ; RE_CX; CX_INJ] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (nearzeta 1 (x) + Cx(&1)) pow 3 * (x - Cx(&1))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; CPOW_1; GSYM DIST_NZ; zeta; genzeta; COMPLEX_DIV_1;
    COMPLEX_FIELD
    `~(x:complex = a)
     ==> b * (x - a) - (c / (x - a)) pow 3 * (x - a) pow 4 =
         (b - c pow 3) * (x - a)`] THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
    SIMP_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_AT_WITHIN THEN SUBST1_TAC(COMPLEX_RING
   `Cx(&0) = (nearzeta 1 (Cx(&1)) + Cx(&1)) pow 3 * (Cx(&1) - Cx(&1))`) THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  SIMP_TAC[LIM_SUB; LIM_CONST; LIM_AT_ID] THEN
  MATCH_MP_TAC LIM_COMPLEX_POW THEN MATCH_MP_TAC LIM_ADD THEN
  REWRITE_TAC[LIM_CONST] THEN REWRITE_TAC[GSYM CONTINUOUS_AT] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_NEARZETA;
               RE_CX; REAL_OF_NUM_LT; ARITH]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than or equal to 1, then the Riemann zeta function evaluated at `s` is not equal to the complex number 0.

### Informal sketch
The proof demonstrates that the Riemann zeta function is non-zero for complex numbers with real part greater than or equal to 1.

- First, the proof rewrites `&1 <= Re s` to `&1 < Re s \/ Re s = &1` and introduces the assumption `Re s >= 1`.
- It's shown that `zeta s` is non-zero when `Re s = 1`.
- The proof proceeds by contradiction, assuming `zeta s = 0` for some `s` with `Re s >= 1`.
- The proof uses the inequality `0 < norm((Cx(&0) * complex_derivative (\x. zeta(x + ii * Cx y)) (Cx(&1)) pow 4) * zeta(Cx(&1) + Cx (&2) * ii * Cx(y)) pow 2)`.
- The existence of a lower bound for the norm of the derivative of the zeta function near 1 (`LIM_NORM_LBOUND`) is established, showing the existence of such a norm, and is applied to a point approaching 1 along the real axis.
- The theorem `LIM_COMPLEX_MUL` on the limit of a product of complex functions is used.
- The proof uses the fact that the composed function is continuous to establish that the limit of `zeta x` as `x` approaches 1 exists and is equal to `zeta 1`.
- The theorem `LIM_TRANSFORM` is applied to rewrite the limit in a more usable form.
- Through a series of transformations involving derivatives and limits, contradictions are derived, ultimately proving that `zeta s` cannot be zero when `Re s >= 1`.
- Several properties of the Riemann zeta function, complex numbers, derivatives, and limits are used.

### Mathematical insight
This theorem is a fundamental result in analytic number theory. It is a necessary ingredient in proving the prime number theorem and other important results about the distribution of prime numbers. The non-vanishing of the zeta function in the region `Re(s) >= 1` is crucial for many analytic arguments.

### Dependencies
- `REAL_ARITH`
- `ZETA_NONZERO_LEMMA`
- `COMPLEX_EXPAND`
- `COMPLEX_MUL_RZERO`
- `COMPLEX_ADD_RID`
- `ZETA_1_NZ`
- `LIM_NORM_LBOUND`
- `EVENTUALLY_WITHIN`
- `TRIVIAL_LIMIT_WITHIN`
- `LIMPT_APPROACHABLE_LE`
- `dist`
- `CX_INJ`
- `IN_ELIM_THM`
- `REAL_CX`
- `RE_CX`
- `CX_SUB`
- `REAL_ADD_SUB`
- `COMPLEX_NORM_CX`
- `REAL_LT_01`
- `ZETA_MULTIPLE_BOUND`
- `COMPLEX_MUL_ASSOC`
- `LIM_COMPLEX_MUL`
- `CONTINUOUS_WITHIN`
- `CONTINUOUS_AT_WITHIN`
- `CONTINUOUS_COMPLEX_POW`
- `o_DEF`
- `CONTINUOUS_AT_COMPOSE`
- `CONTINUOUS_ADD`
- `CONTINUOUS_CONST`
- `CONTINUOUS_AT_ID`
- `COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT`
- `COMPLEX_DIFFERENTIABLE_AT_ZETA`
- `RE_ADD`
- `RE_MUL_CX`
- `RE_MUL_II`
- `RE_II`
- `COMPLEX_RING`
- `COMPLEX_ENTIRE`
- `II_NZ`
- `REAL_OF_NUM_EQ`
- `ARITH`
- `LIM_TRANSFORM`
- `LIM_WITHIN`
- `DIST_NZ`
- `COMPLEX_SUB_0`
- `COMPLEX_FIELD`
- `COMPLEX_VEC_0`
- `COMPLEX_SUB_REFL`
- `COMPLEX_NORM_0`
- `REAL_LT_01`
- `HAS_COMPLEX_DERIVATIVE_WITHIN`
- `COMPLEX_SUB_RZERO`
- `HAS_COMPLEX_DERIVATIVE_AT_WITHIN`
- `HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE`
- `COMPLEX_DIFFERENTIABLE_COMPOSE_AT`
- `COMPLEX_DIFFERENTIABLE_ADD`
- `COMPLEX_DIFFERENTIABLE_CONST`
- `COMPLEX_DIFFERENTIABLE_ID`
- `CPOW_1`
- `zeta`
- `genzeta`
- `COMPLEX_DIV_1`
- `LIM_AT_WITHIN`
- `LIM_SUB`
- `LIM_CONST`
- `LIM_AT_ID`
- `LIM_COMPLEX_POW`
- `LIM_ADD`
- `CONTINUOUS_AT`
- `ETA_AX`
- `COMPLEX_DIFFERENTIABLE_NEARZETA`
- `REAL_OF_NUM_LT`

### Porting notes (optional)
- Proving this theorem in other provers might be challenging as it involves complex analysis and reasoning about limits and derivatives. Ensure that the target prover has adequate libraries for complex analysis.
- The tactics used in HOL Light can be used as a guideline to reconstruct the proof strategy in other provers.


---

## NEARZETA_NONZERO

### Name of formal statement
NEARZETA_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(nearzeta 1 s + Cx (&1) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_NONZERO) THEN
  REWRITE_TAC[zeta; genzeta] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NEARZETA_1; ARITH; CPOW_1] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than or equal to 1, then `nearzeta 1 s + Cx (&1)` is not equal to `Cx(&0)`.

### Informal sketch
The proof proceeds as follows:
- Assume `&1 <= Re s`.
- Apply the theorem `ZETA_NONZERO` to show that `zeta s` is not equal to `Cx(&0)`.`ZETA_NONZERO` states that the zeta function is nonzero when the real part of `s` is greater than 1.
- Rewrite using the definitions of `zeta` and `genzeta` (generalized zeta function).
- Perform case analysis using `COND_CASES_TAC`.
- Simplify using `NEARZETA_1`, `ARITH`, and `CPOW_1`. `NEARZETA_1` likely provides a definition or simplification rule for `nearzeta 1 s`. `CPOW_1` likely simplifies complex powers with exponent 1.
- Repeatedly apply modus ponens to discharge assumptions.
- Apply the `COMPLEX_FIELD` conversion to prove the inequality in the field of complex numbers.

### Mathematical insight
This theorem establishes that the `nearzeta` function, when its first argument is 1, does not take the value `-1` for complex numbers `s` with a real part greater than or equal to 1. This is a step towards showing the non-vanishing of a modified zeta function, which is often crucial in analytic number theory. Specifically, the `nearzeta` function appears related to the standard Riemann zeta function, and this non-vanishing result may contribute to proving properties of the Riemann zeta function or related L-functions.

### Dependencies
- `ZETA_NONZERO`
- `zeta`
- `genzeta`
- `NEARZETA_1`
- `ARITH`
- `CPOW_1`
- `COMPLEX_FIELD`


---

## NORM_CLOG_BOUND

### Name of formal statement
NORM_CLOG_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_CLOG_BOUND = prove
 (`norm(z) <= &1 / &2 ==> norm(clog(Cx(&1) - z)) <= &2 * norm(z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog(Cx(&1) - z)`; `\z. inv(z - Cx(&1))`;
   `cball(Cx(&0),&1 / &2)`; `&2`] COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO; CLOG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REWRITE_TAC[IN_CBALL] THEN
    ASM_REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
   [COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_RING `(Cx(&0) - Cx(&1)) * x = --x`] THEN
    REWRITE_TAC[COMPLEX_NEG_INV; COMPLEX_NEG_SUB] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MP_TAC(SPEC `w:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&1 / &2)`)) THEN
  REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  MP_TAC(SPEC `1` COMPLEX_NORM_NUM) THEN ASM_NORM_ARITH_TAC);;
```
### Informal statement
For all complex numbers `z`, if the norm of `z` is less than or equal to 1/2, then the norm of `clog(Cx(1) - z)` is less than or equal to 2 times the norm of `z`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal and then applying `COMPLEX_DIFFERENTIABLE_BOUND` with appropriate specializations for the complex function `clog(Cx(1) - z)`, its derivative `inv(z - Cx(1))`, the ball `cball(Cx(0), 1/2)`, and the constant `2`.
- Then, address the antecedents of the implication.
  - The first antecedent requires no special handling.
  - For the second antecedent, discharge the assumption, specialize it with `z:complex` and `Cx(0)`, apply rewrite rules like `COMPLEX_SUB_RZERO` and `CLOG_1`. Then use rewriting with assumptions and rules such as `CENTRE_IN_CBALL`, `IN_CBALL`, `dist`, `COMPLEX_SUB_LZERO` to simplify until only `norm(z)` remains. Finally, use a conversion tactic to reduce the real rational expression.
- Rewrite using lemmas about `CONVEX_CBALL`, `IN_CBALL`, `dist`, `COMPLEX_SUB_LZERO`, and `NORM_NEG`.
- Introduce a new variable `w:complex`, discharge it, and proceed by proving two conjuncts.
  - For the first conjunct which concerns differentiation, apply `COMPLEX_DIFF_TAC`, rewrite using complex ring properties and lemmas regarding `COMPLEX_NEG_INV` and `COMPLEX_NEG_SUB`. Introduce the discharged assumption universally. Rewrite using `RE_SUB` and `REAL_SUB_LT`, then apply `COMPLEX_NORM_GE_RE_IM` specialized to `w:complex`, rewrite using `RE_SUB` and `RE_CX`, finally solve with `ASM_REAL_ARITH_TAC`.
  - The second conjunct requires no special handling.
- Finally, substitute the symmetric reduction of `inv(1 / 2)`, rewrite using `COMPLEX_NORM_INV`, apply `REAL_LE_INV2`, apply `COMPLEX_NORM_NUM` specialized to `1` and then finish by calling `ASM_NORM_ARITH_TAC`.

### Mathematical insight
The theorem provides an upper bound on the norm of the complex logarithm of `Cx(1) - z`, where `z` is a complex number whose norm is bounded by 1/2. This type of bound is useful in complex analysis when dealing with analytic functions and their singularities. The constant `Cx(1)` likely represents the complex number 1 + 0i. This result is likely a component in a larger calculation related to functions of complex variables.

### Dependencies
- `COMPLEX_DIFFERENTIABLE_BOUND`
- `COMPLEX_SUB_RZERO`
- `CLOG_1`
- `CENTRE_IN_CBALL`
- `IN_CBALL`
- `dist`
- `COMPLEX_SUB_LZERO`
- `NORM_NEG`
- `CONVEX_CBALL`
- `RE_SUB`
- `REAL_SUB_LT`
- `COMPLEX_NORM_GE_RE_IM`
- `RE_CX`
- `REAL_RAT_REDUCE_CONV`
- `COMPLEX_NORM_INV`
- `REAL_LE_INV2`
- `COMPLEX_NORM_NUM`
- `COMPLEX_RING \`(Cx(&0) - Cx(&1)) * x = --x\``
- `COMPLEX_NEG_INV`
- `COMPLEX_NEG_SUB`


---

## LOGZETA_EXISTS

### Name of formal statement
LOGZETA_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LOGZETA_EXISTS = prove
 (`?logzeta logzeta'.
        !s. s IN {s | Re s > &1}
            ==> ((\p. clog(Cx(&1) - inv(Cx(&p) cpow s)))
                 sums logzeta(s))
                {p | prime p} /\
                ((\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1)))
                 sums logzeta'(s))
                {p | prime p} /\
                (logzeta has_complex_derivative logzeta'(s)) (at s)`,
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
      COMPLEX_SUB_LZERO; COMPLEX_MUL_LID; COMPLEX_FIELD
       `~(x = Cx(&0)) ==> --(a * x) / x pow 2 = --(a / x)`] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_INV_MUL] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ; COMPLEX_FIELD
     `~(y = Cx(&0)) ==> y * (Cx(&1) - inv(y)) = y - Cx(&1)`] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `!y. abs x <= y /\ y < w ==> x < w`) THEN
    EXISTS_TAC `norm(inv (Cx (&p) cpow s))` THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN REWRITE_TAC[RE_CX] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < p <=> 2 <= p`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `s:complex` THEN
  DISCH_TAC THEN EXISTS_TAC `(Re(s) - &1) / &2` THEN
  EXISTS_TAC `\p. Cx(&2) / Cx(&p) cpow (Cx(&1 + (Re(s) - &1) / &2))` THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT; RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             ARITH_RULE `0 < n <=> 1 <= n`; GSYM CX_INV; REAL_LE_INV_EQ;
             REAL_EXP_POS_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_FROM; PRIME_GE_2;
             ARITH_RULE `2 <= p ==> 1 <= p`] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `inv(x) = Cx(&1) * inv x`] THEN
    REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ;
             PRIME_IMP_NZ; GSYM CX_DIV; REAL_CX; REAL_LE_DIV; REAL_POS;
             REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `summable (from 1) (\n. Cx (&1) / Cx (&n) cpow (Cx(&1 + (Re s - &1) / &2)))`
  MP_TAC THENL
   [REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2` o MATCH_MP SERIES_GOESTOZERO) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[IN_FROM; PRIME_IMP_NZ; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(inv(Cx(&p) cpow y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NORM_CLOG_BOUND THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> y <= x ==> y <= a`)) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID];
    SIMP_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]] THEN
  REWRITE_TAC[GSYM CPOW_NEG] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL_MONO; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN REAL_ARITH_TAC);;
```

### Informal statement
There exist complex functions `logzeta` and `logzeta'` such that for all complex numbers `s` in the open half-plane where the real part of `s` is greater than 1, it holds that:
1. The sum of `clog(Cx(&1) - inv(Cx(&p) cpow s))` over all prime numbers `p` sums to `logzeta(s)`.
2. The sum of `clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1))` over all prime numbers `p` sums to `logzeta'(s)`.
3. `logzeta` has a complex derivative `logzeta'(s)` at `s`.

### Informal sketch
The proof demonstrates the existence of the complex logarithm of the zeta function and its derivative, defined as sums over prime numbers.

- First, it is shown that `logzeta(s)` is the sum of `clog(Cx(&1) - inv(Cx(&p) cpow s))` over all prime numbers `p`.
    - `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` and `OPEN_HALFSPACE_RE_GT` are used to start proving the result, simplifying the goal to showing the sums converge, and that the complex derivative exists.
    - The real part of `s` being greater than 1 is used to establish the convergence of the series by comparisons to geometric series.
    - The complex derivative of `clog(Cx(&1) - inv(Cx(&p) cpow s))` with respect to `s` is computed, resulting in an expression involving the complex power and logarithm functions.
    - By bounding the norm of `inv (Cx (&p) cpow s)`, and comparisons to geometric series, convergence of the sum is obtained.
- Then, it is shown that `logzeta'(s)` is the sum of `clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1))` over all prime numbers `p`.
    - The real part of `s` being greater than 1 is used to establish the convergence of the series by comparison to the convergent `zeta` function.
    - A value `(Re(s) - &1) / &2` is introduced to construct the `zeta` function.
    - Uses `SUMMABLE_COMPLEX_LMUL` and `SUMMABLE_SUBSET_COMPLEX` to show a series is summable.
    - ZETA_CONVERGES is used to show some of the sums converge for the `zeta` function.

- Lastly, using `SERIES_GOESTOZERO`, prove that series goes to zero sequentially, and that the derivatives exist, and converge to allow logzeta to have a complex derivative logzeta'(s).

### Mathematical insight
This theorem establishes the existence and a series representation of the complex logarithm of the Riemann zeta function and its derivative in the region where Re(s) > 1. This representation is fundamental in analytic number theory and connects the zeta function to prime numbers. It provides a way to study the zeta function's behavior using tools from complex analysis, with direct connections to sums of primes.

### Dependencies
- Definitions: `prime`, `sums`, `has_complex_derivative`, `at`
- Theorems: `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`, `OPEN_HALFSPACE_RE_GT`, `IN_ELIM_THM`, `REAL_GT`, `CPOW_EQ_0`, `CX_INJ`, `REAL_OF_NUM_EQ`, `PRIME_IMP_NZ`, `COMPLEX_SUB_LZERO`, `COMPLEX_MUL_LID`, `COMPLEX_FIELD`, `COMPLEX_DIV`, `COMPLEX_MUL_LNEG`, `COMPLEX_NEG_NEG`, `COMPLEX_MUL_ASSOC`, `COMPLEX_INV_MUL`, `REAL_SUB_LT`, `REAL_ARITH`, `COMPLEX_NORM_GE_RE_IM`, `COMPLEX_NORM_INV`, `NORM_CPOW_REAL`, `REAL_CX`, `REAL_OF_NUM_LT`, `LT_NZ`, `REAL_EXP_NEG`, `REAL_EXP_0`, `REAL_EXP_MONO_LT`, `REAL_LT_LNEG`, `REAL_ADD_RID`, `REAL_LT_MUL`, `LOG_POS_LT`, `ARITH_RULE`, `REAL_HALF`, `RIGHT_EXISTS_AND_THM`, `SUMMABLE_COMPLEX_LMUL`, `SUMMABLE_SUBSET_COMPLEX`, `IN_FROM`, `CPOW_REAL_REAL`, `REAL_LE_INV_EQ`, `REAL_EXP_POS_LE`, `SUBSET`, `PRIME_GE_2`, `ZETA_CONVERGES`, `COMPLEX_RING`, `COMPLEX_DIV`, `CX_DIV`, `REAL_LE_DIV`, `REAL_POS`, `SERIES_GOESTOZERO`, `EVENTUALLY_SEQUENTIALLY`, `MONO_EXISTS`, `MONO_FORALL`, `IN_BALL_RE`, `NORM_CLOG_BOUND`, `COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `CPOW_NEG`, `NORM_CPOW_REAL_MONO`

### Porting notes (optional)
- This theorem relies heavily on complex analysis and real analysis results, especially regarding the convergence of infinite series and the properties of complex functions.
- The proof uses specific tactics such as `MATCH_MP_TAC` with arithmetic rules and theorems. In other proof assistants, it might require explicit rewriting and application of these rules.
- The handling of complex numbers and their properties (`CPOW`, `CX`, `clog`, `complex_div`, etc.) must be carefully considered when porting to another system. Ensure the target system provides adequate support for complex numbers and related operations.


---

## LOGZETA_PROPERTIES

### Name of formal statement
LOGZETA_PROPERTIES

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let LOGZETA_PROPERTIES =
  new_specification ["logzeta"; "logzeta'"] LOGZETA_EXISTS;;
```
### Informal statement
This specification introduces the constants `logzeta` and `logzeta'`, constrained by the axiom `LOGZETA_EXISTS`. The axiom `LOGZETA_EXISTS` asserts the existence of functions satisfying the properties specified in the definition of `logzeta` and its derivative `logzeta'`.

### Informal sketch
- The specification introduces two functions, `logzeta` and `logzeta'`, without providing explicit definitions.
- The axiom `LOGZETA_EXISTS` (which is not given here but referenced) guarantees the existence of these functions, along with certain properties that were presumably proven in defining `LOGZETA_EXISTS.` This axiom must be examined separately to understand which properties are being assumed.

### Mathematical insight
This statement is part of the formalization of the Riemann zeta function in HOL Light. The `logzeta` function likely refers to a variant of the zeta function, perhaps a logarithmic representation or a similar function related to prime numbers. The introduction of `logzeta'` suggests that its derivative is also of interest, possibly for analytical purposes or for formulating relationships between the function and its rate of change. Existence, but not uniqueness, is being introduced at this specification.

### Dependencies
- Axioms: `LOGZETA_EXISTS`

### Porting notes (optional)
The main challenge in porting this specification lies in understanding and recreating the `LOGZETA_EXISTS` axiom. The porter needs to retrieve the precise logical statement of `LOGZETA_EXISTS` from its definition and then prove or assume a corresponding axiom in the target proof assistant guaranteeing existence of `logzeta` and `logzeta'` functions with the stated properties. The properties associated determine what needs to be proved in the target assistant.


---

## [LOGZETA_CONVERGES;

### Name of formal statement
`LOGZETA_CONVERGES`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let [LOGZETA_CONVERGES; LOGZETA'_CONVERGES; HAS_COMPLEX_DERIVATIVE_LOGZETA] =
    CONJUNCTS(REWRITE_RULE[IN_ELIM_THM; FORALL_AND_THM; real_gt; TAUT
                             `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                          LOGZETA_PROPERTIES);;
```
### Informal statement
The theorem `LOGZETA_CONVERGES` is given by the conjunction of three theorems derived from `LOGZETA_PROPERTIES`. Specifically:
1. `LOGZETA_CONVERGES`: For all real numbers `x`, if `x` is greater than 1, then the infinite sum from `n = 1` to infinity of `1 / (n ** x)` is in the set of real numbers.
2. `LOGZETA'_CONVERGES`: For all real numbers `x`, if `x` is greater than 1, then the infinite sum from `n = 2` to infinity of `log(n) / (n ** x)` is in the set of real numbers.
3. `HAS_COMPLEX_DERIVATIVE_LOGZETA`: For all complex numbers `s`, if the real part of `s` is greater than 1, then `logzeta` has a complex derivative at `s`.

### Informal sketch
The proof of `LOGZETA_CONVERGES` involves extracting three conjuncts from a larger theorem `LOGZETA_PROPERTIES`.
- The first extraction uses `IN_ELIM_THM` and `FORALL_AND_THM` to separate the conjuncts related to the convergence of the given infinite sums and the existence of the complex derivative.
- The theorem `real_gt` is used to represent the condition "greater than".
- A tautology of the form `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)` is used to distribute the implication over conjunction.

### Mathematical insight
The theorem `LOGZETA_CONVERGES` establishes fundamental properties about the convergence of certain infinite sums and the derivative of the `logzeta` function which are important in complex analysis and number theory. Specifically, it states that the Dirichlet series converges for real numbers greater than 1, the weighted series with `log(n)` also converges under the same condition, and the logzeta function has a complex derivative when the real part of the argument is greater than 1.

### Dependencies
- `LOGZETA_PROPERTIES`
- `IN_ELIM_THM`
- `FORALL_AND_THM`
- `real_gt`
- TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`


---

## CEXP_LOGZETA

### Name of formal statement
CEXP_LOGZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CEXP_LOGZETA = prove
 (`!s. &1 < Re s ==> cexp(--(logzeta s)) = zeta s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. cexp(vsum({p | prime p} INTER (0..n))
                 (\p. --clog(Cx(&1) - inv(Cx(&p) cpow s))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`cexp`; `--logzeta s`] CONTINUOUS_AT_SEQUENTIALLY) THEN
    REWRITE_TAC[CONTINUOUS_AT_CEXP; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM sums] THEN
    MATCH_MP_TAC SERIES_NEG THEN ASM_SIMP_TAC[LOGZETA_CONVERGES];
    SIMP_TAC[CEXP_VSUM; FINITE_INTER_NUMSEG] THEN
    MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\n. cproduct {p | prime p /\ p <= n}
                             (\p. inv(Cx(&1) - inv(Cx(&p) cpow s)))` THEN
    ASM_SIMP_TAC[EULER_PRODUCT] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[VECTOR_SUB_EQ; numseg; LE_0] THEN
    REWRITE_TAC[SET_RULE `{x | P x} INTER {x | Q x} = {x | P x /\ Q x}`] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_ELIM_THM; CEXP_NEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CEXP_CLOG THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; REAL_OF_NUM_LT; RE_CX; REAL_ABS_NUM;
     COMPLEX_NORM_INV; PRIME_IMP_NZ; LT_NZ; COMPLEX_NORM_CX; REAL_EXP_EQ_1] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_EXP_0; GSYM REAL_EXP_NEG; REAL_EXP_INJ] THEN
    REWRITE_TAC[REAL_NEG_EQ_0; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 < s ==> ~(s = &0)`] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```

### Informal statement
For all complex numbers `s`, if 1 is strictly less than the real part of `s`, then `cexp` applied to the negation of `logzeta s` is equal to `zeta s`.

### Informal sketch
The proof demonstrates that `cexp(--(logzeta s)) = zeta s` for `Re s > 1`.

- First, the uniqueness of the limit (`LIM_UNIQUE`) is used to reduce the goal to demonstrating that the expression `cexp(--(logzeta s))` has a limit equal to `zeta s`.
- An existential is introduced to represent the partial sum of the `logzeta` function where the sum is only over primes from 0 to `n`.
- The proof relies on showing that the limit of the partial sum of the complex exponential of the log of zeta (`cexp(vsum({p | prime p} INTER (0..n)) (\p. --clog(Cx(&1) - inv(Cx(&p) cpow s))))`) equals the limit of `cexp(--(logzeta s))`.
- Then, it is shown that this is equal to the limit of the partial product of the Euler product formula.
- The limit of the complex exponential of `logzeta` is proven using the sequential continuity of the complex exponential function (`CONTINUOUS_AT_CEXP`).
- The series converges absolutely (`LOGZETA_CONVERGES`), justifying switching the continuous function (cexp) with the limit.
- The partial sums are converted to a product by using `EULER_PRODUCT`.
- The limit of the partial product is converted to the intended form using the definition of `CPRODUCT_EQ`, `CEXP_CLOG` and properties of `norm`.

### Mathematical insight
This theorem establishes a fundamental relationship between the exponential of the negative logarithm of the Riemann zeta function and the Riemann zeta function itself, specifically for complex numbers `s` whose real part is greater than 1. This relationship is derived using the Euler product representation of the Riemann zeta function and properties of complex exponentials and logarithms.

### Dependencies
- `cexp`
- `logzeta`
- `zeta`
- `SEQUENTIALLY`
- `LIM_UNIQUE`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `CONTINUOUS_AT_SEQUENTIALLY`
- `CONTINUOUS_AT_CEXP`
- `o_DEF`
- `sums`
- `SERIES_NEG`
- `LOGZETA_CONVERGES`
- `CEXP_VSUM`
- `FINITE_INTER_NUMSEG`
- `LIM_TRANSFORM`
- `EULER_PRODUCT`
- `LIM_EVENTUALLY`
- `ALWAYS_EVENTUALLY`
- `VECTOR_SUB_EQ`
- `numseg`
- `LE_0`
- `SET_RULE`
- `CPRODUCT_EQ`
- `IN_ELIM_THM`
- `CEXP_NEG`
- `CEXP_CLOG`
- `COMPLEX_SUB_0`
- `NORM_CPOW_REAL`
- `REAL_CX`
- `REAL_OF_NUM_LT`
- `RE_CX`
- `REAL_ABS_NUM`
- `COMPLEX_NORM_INV`
- `PRIME_IMP_NZ`
- `LT_NZ`
- `COMPLEX_NORM_CX`
- `REAL_EXP_EQ_1`
- `REAL_EXP_0`
- `REAL_EXP_NEG`
- `REAL_EXP_INJ`
- `REAL_NEG_EQ_0`
- `REAL_ENTIRE`
- `REAL_LT_IMP_NZ`
- `LOG_POS_LT`
- `PRIME_GE_2`
- `REAL_OF_NUM_LT`


---

## HAS_COMPLEX_DERIVATIVE_ZETA

### Name of formal statement
HAS_COMPLEX_DERIVATIVE_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s ==> (zeta has_complex_derivative
                      (--(logzeta'(s)) * zeta(s))) (at s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. cexp(--(logzeta s))` THEN EXISTS_TAC `Re s - &1` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_BALL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CEXP_LOGZETA THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
  ASM_SIMP_TAC[GSYM CEXP_LOGZETA; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_LOGZETA]);;
```
### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the Riemann zeta function `zeta` has a complex derivative equal to `(-(logzeta'(s)) * zeta(s))` at `s`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifier and assumption.
- Apply `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` to transform the goal using the identity function (i.e., `f(z) = z`). This reduces the problem to proving that `zeta` can be expressed as `cexp(--(logzeta s))` in a small neighborhood of the point `s`.
- Show that such exponential representation is possible and find the radius such that the exponential representation holds. This involves rewriting with `GSYM IN_BALL` to convert the metric ball definition.
- Apply `CEXP_LOGZETA` which states zeta is locally representable as the exponential of the negative of `logzeta` (the complex logarithm of the zeta function).
- Verify the condition `&1 < Re s` to ensure the radius is positive using `REAL_ARITH_TAC`.
- Apply `COMPLEX_DIFF_CHAIN_AT` to compute the derivative of `cexp(--(logzeta s))` using chain rule, which requires `HAS_COMPLEX_DERIVATIVE_CEXP` and `HAS_COMPLEX_DERIVATIVE_LOGZETA`.
- Use `HAS_COMPLEX_DERIVATIVE_NEG` to handle the negation inside the exponential.

### Mathematical insight
This theorem provides an explicit formula for the complex derivative of the Riemann zeta function. The representation of `zeta` as the exponential of `logzeta` is crucial. The condition `&1 < Re s` ensures both the convergence of the zeta function and the validity of using `logzeta`, which is defined only when `zeta` is nonzero.

### Dependencies
- `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`
- `CEXP_LOGZETA`
- `IN_BALL_RE`
- `COMPLEX_DIFF_CHAIN_AT`
- `HAS_COMPLEX_DERIVATIVE_CEXP`
- `HAS_COMPLEX_DERIVATIVE_NEG`
- `HAS_COMPLEX_DERIVATIVE_LOGZETA`
- `REAL_SUB_LT`
- `DIST_SYM`
- `IN_BALL`
- `o_DEF`

### Porting notes (optional)
- The concept of "having a complex derivative at a point" needs to be defined or available in the target proof assistant.
- The handling of complex analysis concepts, such as complex exponentials and logarithms, may differ between systems.
- The `logzeta` term refers to the complex logarithm of the zeta function. Ensure that the corresponding function and its properties are available, or define them.


---

## COMPLEX_DERIVATIVE_ZETA

### Name of formal statement
COMPLEX_DERIVATIVE_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s
       ==> complex_derivative zeta s = --(logzeta'(s)) * zeta(s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_ZETA]);;
```
### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the complex derivative of the zeta function at `s` is equal to the negation of the derivative of the logarithm of the zeta function at `s`, multiplied by the zeta function at `s`.

### Informal sketch
The proof proceeds as follows:
- Begin by stripping the quantifier and the implication.
- Apply the theorem `HAS_COMPLEX_DERIVATIVE_DERIVATIVE` using `MATCH_MP_TAC` to relate derivative of `logzeta` to `zeta'` and `zeta`. This handles the derivative of a product.
- Simplify using the assumption `HAS_COMPLEX_DERIVATIVE_ZETA`.

### Mathematical insight
The theorem relates the derivative of the Riemann zeta function to the logarithmic derivative of the Riemann zeta function. This is a standard result in analytic number theory and is useful for studying the behavior of the zeta function.

### Dependencies
- Theorems: `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`, `HAS_COMPLEX_DERIVATIVE_ZETA`


---

## CONVERGES_LOGZETA''

### Name of formal statement
CONVERGES_LOGZETA''

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERGES_LOGZETA'' = prove
 (`!s. &1 < Re s
       ==> ((\p. Cx(log(&p)) / (Cx(&p) cpow s - Cx(&1))) sums
            (--(complex_derivative zeta s / zeta s))) {p | prime p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(complex_derivative zeta s / zeta s) = logzeta'(s)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_DERIVATIVE_ZETA; COMPLEX_FIELD
     `~(b = Cx(&0)) ==> (--(a / b) = c <=> a = --c * b)`];
    MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC `\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1))` THEN
    ASM_SIMP_TAC[LOGZETA'_CONVERGES; IN_ELIM_THM] THEN
    SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ]]);;
```
### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the infinite sum over all primes `p` of `log(p) / (p^s - 1)` converges to the negation of the complex derivative of the Riemann zeta function at `s` divided by the Riemann zeta function at `s`.

### Informal sketch
The proof proceeds by:
- Showing that `--(complex_derivative zeta s / zeta s)` is equal to `logzeta'(s)`. This step uses simplification with the lemmas `ZETA_NONZERO_LEMMA`, `COMPLEX_DERIVATIVE_ZETA`, and the complex field laws to rewrite the expression in terms of `logzeta'(s)`.
- Applying the `SUMS_EQ` theorem via `MATCH_MP_TAC` to show that the target expression converges to `logzeta'(s)`.
- Using the convergence definition of `logzeta'(s)` (`LOGZETA'_CONVERGES`) after proving `IN_ELIM_THM`.
- Simplifying complex logarithms with `CX_LOG`, using `REAL_OF_NUM_LT` to show numerical comparison, and confirming that prime numbers are nonzero using `PRIME_IMP_NZ`.

### Mathematical insight
This theorem establishes the convergence of an infinite series involving prime numbers and complex exponentiation to the logarithmic derivative of the Riemann zeta function. This relationship is fundamental in analytic number theory, linking the distribution of prime numbers to the analytic properties of the Riemann zeta function. `logzeta'(s)` is the derivative of the logarithm of the zeta function.

### Dependencies
- Theorems: `ZETA_NONZERO_LEMMA`, `COMPLEX_DERIVATIVE_ZETA`, `SUMS_EQ`, `IN_ELIM_THM`
- Definitions: `complex_derivative`, `zeta`, `logzeta'`, `PRIME_IMP_NZ`
- Tactics: `REPEAT STRIP_TAC`, `SUBGOAL_THEN`, `SUBST1_TAC`, `ASM_SIMP_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, `SIMP_TAC`
- Other: `COMPLEX_FIELD`

### Porting notes (optional)
- In proof assistants like Lean or Coq, care must be taken to ensure that the definitions of complex exponentiation and the Riemann zeta function are compatible with HOL Light's definitions.
- The handling of convergence proofs may require explicit use of convergence criteria.
- HOL Light's `ASM_SIMP_TAC` handles rewriting with assumptions, which may need to be emulated with appropriate tactics.


---

## VALID_PATH_NEGATEPATH

### Name of formal statement
VALID_PATH_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_PATH_NEGATEPATH = prove
 (`!g. valid_path g ==> valid_path ((--) o g)`,
  REWRITE_TAC[valid_path; o_DEF] THEN
  ASM_SIMP_TAC[PIECEWISE_DIFFERENTIABLE_NEG]);;
```

### Informal statement
For all paths `g`, if `g` is a valid path, then the negation of `g` (i.e., the path obtained by composing the negation function `--` with `g`) is also a valid path.

### Informal sketch
- The proof begins by rewriting using the definition of `valid_path` and `o_DEF` (definition of function composition).
- Then, the goal is simplified using the theorem `PIECEWISE_DIFFERENTIABLE_NEG`.

### Mathematical insight
This theorem establishes that the validity of a path is preserved under negation. It extends the notion of valid paths by demonstrating closure under a natural geometric operation, which is crucial for reasoning about path integrals or line integrals in reverse directions.

### Dependencies
- Definitions: `valid_path`, `o_DEF`
- Theorems: `PIECEWISE_DIFFERENTIABLE_NEG`


---

## PATHSTART_NEGATEPATH

### Name of formal statement
PATHSTART_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATHSTART_NEGATEPATH = prove
 (`!g. pathstart((--) o g) = --(pathstart g)`,
  REWRITE_TAC[pathstart; o_THM]);;
```
### Informal statement
For all `g`, the path start of the negation of `g` is equal to the negation of the path start of `g`. Here, the negation is represented by `(--)`, and composition by `o`.
Formally, for any graph `g`, `pathstart((--) o g) = --(pathstart g)`.

### Informal sketch
The proof proceeds by rewriting the left-hand side of the equation `pathstart((--) o g) = --(pathstart g)` using the definitions of `pathstart` and `o`.

- First, the tactic `REWRITE_TAC[pathstart; o_THM]` is applied.
 - `pathstart` rewrites `pathstart(g) = (g EMPTY)` where `EMPTY` is the empty set.
 - `o_THM` is a theorem that defines function composition: `(f o g) x = f (g x)`.
- Applying these rewrites simplifies the equation to `(--)(g EMPTY) = --(g EMPTY)`, establishing the theorem.

### Mathematical insight
This theorem describes how `pathstart` interacts with graph negation. It shows that taking the paths starting from a state in the negated graph is equivalent to negating the set of paths starting from that state in the original graph. This highlights a symmetry between the `pathstart` function and the negation operation.

### Dependencies
- Definitions: `pathstart`
- Theorems: `o_THM`


---

## PATHFINISH_NEGATEPATH

### Name of formal statement
PATHFINISH_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATHFINISH_NEGATEPATH = prove
 (`!g. pathfinish((--) o g) = --(pathfinish g)`,
  REWRITE_TAC[pathfinish; o_THM]);;
```
### Informal statement
For all functions `g`, the path-finish of the path obtained by negating all edges in `g` (i.e., `(--) o g`) is equal to the path obtained by negating all edges in the path-finish of `g` (i.e., `--(pathfinish g)`).

### Informal sketch
The proof is a direct application of rewriting using the definition of `pathfinish` and `o_THM` which likely pertain to function composition.

- The goal is `pathfinish((--) o g) = --(pathfinish g)`.
- Rewrite using the theorem `pathfinish`. This likely expands `pathfinish` in terms of the input graph.
- Simplify using `o_THM` relating to function composition.
- The equation should then simplify to reflexivity or a trivially true statement.

### Mathematical insight
This theorem demonstrates how the `pathfinish` operation interacts with edge negation. It states that negating the edges of a graph before computing its `pathfinish` is equivalent to negating the edges of the `pathfinish` of the original graph. This is important for understanding the algebraic properties of graph operations and path computations.

### Dependencies
- Definitions: `pathfinish`
- Theorems: `o_THM`


---

## PATH_IMAGE_NEGATEPATH

### Name of formal statement
PATH_IMAGE_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATH_IMAGE_NEGATEPATH = prove
 (`!g. path_image((--) o g) = IMAGE (--) (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;
```
### Informal statement
For any function `g` from natural numbers to `real^N`, the image of the negated path of `g` under `path_image` is equal to the image of the negated path under `IMAGE` applied to the image of `g` under `path_image`. More explicitly:
`path_image( (--).g ) = IMAGE (--) (path_image g)`

### Informal sketch
- The theorem states an equality between the `path_image` of a negated path and the `IMAGE` of the negation of the `path_image`.
- The proof relies on rewriting with the definitions of `path_image` and `IMAGE_o`.
- `path_image` likely maps a function `g` to a set of points representing the path, and `IMAGE` applies a function to each element of a set. The '(--)' is the negation operation.

### Mathematical insight
This theorem relates the process of negating a path with the operation of applying a function to the image of a path. It's important for reasoning about path transformations.

### Dependencies
- Definitions: `path_image`
- Theorems: `IMAGE_o`


---

## HAS_PATH_INTEGRAL_NEGATEPATH

### Name of formal statement
HAS_PATH_INTEGRAL_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_PATH_INTEGRAL_NEGATEPATH = prove
 (`!g z. valid_path g /\ ((\z. f(--z)) has_path_integral (--i)) g
         ==> (f has_path_integral i) ((--) o g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_path_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[valid_path; piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[NEGLIGIBLE_FINITE] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[o_DEF; GSYM COMPLEX_MUL_RNEG] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS; DIFFERENTIABLE_AT_WITHIN]);;
```

### Informal statement
For all paths `g` and complex functions `f`, if `g` is a valid path and the path integral of `(λz. f(--z))` along `g` exists and is equal to `--i`, then the path integral of `f` along the path `λt. --(g t)` exists and is equal to `i`.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption that `g` is a valid path and that `(\z. f(--z))` has a path integral along `g` equal to `--i`.
- Expand the definition of `has_path_integral`.
- Apply `HAS_INTEGRAL_NEG` which states that the integral of the negation of a function is the negation of the integral.
- Simplify using `VECTOR_NEG_NEG` which states that the negation of the negation of a vector is the vector itself.
- Use `HAS_INTEGRAL_SPIKE_EQ` to equate the path integral with a Riemann integral along a piecewise differentiable path.
- Decompose the assumption that `g` is a valid path into `valid_path` and `piecewise_differentiable_on`.
- Eliminate negligible sets using `NEGLIGIBLE_FINITE`.
- Introduce a real variable `t` and rewrite `IN_DIFF` to reason about differentiability.
- Rewrite using the definition of function composition `o_DEF` and the fact that `-(a * b) = (-a) * b`, expressed as `GSYM COMPLEX_MUL_RNEG`.
- Apply the theorem `VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL` to relate function values and derivatives.
- Simplify using `DROP_VEC` and `REAL_LT_01`.
- Use `HAS_VECTOR_DERIVATIVE_NEG` to express the derivative of the negated path.
- Simplify using `GSYM VECTOR_DERIVATIVE_WORKS` and `DIFFERENTIABLE_AT_WITHIN`.

### Mathematical insight
The theorem `HAS_PATH_INTEGRAL_NEGATEPATH` establishes how path integrals behave under negation of both the function and the path. Taking the path integral of `f(-z)` using `g(t)` is the negation of the path integral of `f(z)` using `-g(t)`. This highlights the symmetry of path integrals and is useful when manipulating integrals along different paths.

### Dependencies
- `has_path_integral`
- `HAS_INTEGRAL_NEG`
- `VECTOR_NEG_NEG`
- `HAS_INTEGRAL_SPIKE_EQ`
- `valid_path`
- `piecewise_differentiable_on`
- `NEGLIGIBLE_FINITE`
- `IN_DIFF`
- `o_DEF`
- `COMPLEX_MUL_RNEG`
- `VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL`
- `DROP_VEC`
- `REAL_LT_01`
- `HAS_VECTOR_DERIVATIVE_NEG`
- `VECTOR_DERIVATIVE_WORKS`
- `DIFFERENTIABLE_AT_WITHIN`

### Porting notes (optional)
- Other proof assistants may have different ways of handling analytic function differentiability, vector derivatives, or path integrals.
- Pay attention to how the various definitions used in the proof (e.g., `has_path_integral`, `valid_path`) are defined in the target proof assistant and ensure that the analogous transformations hold.


---

## WINDING_NUMBER_NEGATEPATH

### Name of formal statement
WINDING_NUMBER_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WINDING_NUMBER_NEGATEPATH = prove
 (`!g z. valid_path g /\ ~(Cx(&0) IN path_image g)
         ==> winding_number((--) o g,Cx(&0)) = winding_number(g,Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; VALID_PATH_NEGATEPATH;
               PATH_IMAGE_NEGATEPATH; IN_IMAGE; UNWIND_THM2;
               COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN
  ASM_REWRITE_TAC[COMPLEX_RING `--z - Cx(&0) = --(z - Cx(&0))`] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_RNEG] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  ASM_SIMP_TAC[GSYM complex_div; PATH_INTEGRABLE_INVERSEDIFF]);;
```

### Informal statement
For any path `g` and any complex number `z` such that `g` is a valid path and `z` (represented as `Cx(&0)`) is not in the image of the path `g`, the winding number of the negated path `-- o g` around `z` is equal to the winding number of `g` around `z`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and assumptions.
- Simplify using theorems like `WINDING_NUMBER_VALID_PATH`, `VALID_PATH_NEGATEPATH`, `PATH_IMAGE_NEGATEPATH`, `IN_IMAGE`, `UNWIND_THM2`, and `COMPLEX_RING Cx(&0) = --x <=> x = Cx(&0)`.
- Apply `PATH_INTEGRAL_UNIQUE`.
- Apply `HAS_PATH_INTEGRAL_NEGATEPATH`.
- Rewrite using `COMPLEX_RING --z - Cx(&0) = --(z - Cx(&0))`.
- Rewrite using properties of complex arithmetic like `complex_div`, `COMPLEX_INV_NEG`, and `COMPLEX_MUL_RNEG`.
- Apply `HAS_PATH_INTEGRAL_NEG`.
- Apply `HAS_PATH_INTEGRAL_INTEGRAL`.
- Simplify using `GSYM complex_div` and `PATH_INTEGRABLE_INVERSEDIFF`.

### Mathematical insight
This theorem states that negating a path does not change its winding number around a point, provided the point is not in the path's image and the path is valid. Intuitively, traversing a path in the opposite direction does not alter how many times the path "winds" around a given point.

### Dependencies
- `WINDING_NUMBER_VALID_PATH`
- `VALID_PATH_NEGATEPATH`
- `PATH_IMAGE_NEGATEPATH`
- `IN_IMAGE`
- `UNWIND_THM2`
- `COMPLEX_RING Cx(&0) = --x <=> x = Cx(&0)`
- `PATH_INTEGRAL_UNIQUE`
- `HAS_PATH_INTEGRAL_NEGATEPATH`
- `COMPLEX_RING --z - Cx(&0) = --(z - Cx(&0))`
- `complex_div`
- `COMPLEX_INV_NEG`
- `COMPLEX_MUL_RNEG`
- `HAS_PATH_INTEGRAL_NEG`
- `HAS_PATH_INTEGRAL_INTEGRAL`
- `GSYM complex_div`
- `PATH_INTEGRABLE_INVERSEDIFF`


---

## PATH_INTEGRABLE_NEGATEPATH

### Name of formal statement
PATH_INTEGRABLE_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATH_INTEGRABLE_NEGATEPATH = prove
 (`!g z. valid_path g /\ (\z. f(--z)) path_integrable_on g
         ==> f path_integrable_on ((--) o g)`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_NEGATEPATH; COMPLEX_NEG_NEG]);;
```
### Informal statement
For any function `g` and any complex number `z`, if `g` is a valid path and the function `f(--z)` is path integrable on `g`, then the function `f` is path integrable on the path formed by negating `g` (i.e., `-- o g`).

### Informal sketch
The proof proceeds as follows:

- First, rewrite using the definition of `path_integrable_on`.
- Then, use the theorem `HAS_PATH_INTEGRAL_NEGATEPATH`, which relates the path integral of a function along a path to the path integral of the function along the negated path. Also, use `COMPLEX_NEG_NEG`, which states that the negation of the negation of a complex number gives the complex number back.
- Finally, close the goal using the MESON tactic.

### Mathematical insight
This theorem states that if a function of the form `f(-z)` is path integrable along a given path `g`, then the original function `f(z)` is path integrable along the negated of path `g`. This is a fundamental result within complex analysis. Namely, it concerns how path integrals are affected by path orientation and functional transformations.

### Dependencies
- Definitions:
  - `path_integrable_on`
- Theorems:
  - `HAS_PATH_INTEGRAL_NEGATEPATH`
  - `COMPLEX_NEG_NEG`


---

## BOUND_LEMMA_0

### Name of formal statement
BOUND_LEMMA_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_0 = prove
 (`!z R. norm(z) = R
         ==> Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  ASM_REWRITE_TAC[complex_div; GSYM COMPLEX_ADD_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_CNJ; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_INV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[CX_MUL; CX_DIV; CX_POW; complex_div; GSYM COMPLEX_MUL_ASSOC]);;
```
### Informal statement
For any complex number `z` and real number `R`, if the norm (or modulus) of `z` is equal to `R`, then `Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)`. Where `Cx` represents the embedding of a real number into the complex numbers, `Re z` denotes the real part of `z`, and `pow` represents exponentiation.

### Informal sketch
The proof proceeds by:
- Assuming that `norm(z) = R`.
- Simplifying the left-hand side of the equation `Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)` using rewriting steps.
- The strategy involves rewriting the complex division using `complex_div` and `COMPLEX_MUL_LID`. Then using `GSYM complex_div` and `COMPLEX_INV_CNJ` transforms the expression. Further simplifications performed exploiting the distributive property of complex numbers `GSYM COMPLEX_ADD_RDISTRIB`.
- Then rewriting the complex addition of conjugates `COMPLEX_ADD_CNJ` and the norm `COMPLEX_NORM_MUL` will simplify the expression.
- Applying rules for complex norms `COMPLEX_NORM_CX`, `COMPLEX_NORM_INV`, `COMPLEX_NORM_POW`, `CX_MUL`, `CX_DIV`, `CX_POW` as well as `complex_div` and `GSYM COMPLEX_MUL_ASSOC` will complete the demonstration.

### Mathematical insight
This lemma provides a crucial simplification in complex analysis, particularly when dealing with complex numbers whose norm is known. The lemma transforms a potentially complicated expression involving division and exponentiation of complex numbers into a simpler form that depends only on the real part of `z` and the value of the norm `R`. This type of simplification is frequently used in bounding arguments and contour integration.

### Dependencies
- `complex_div`
- `COMPLEX_MUL_LID`
- `COMPLEX_INV_CNJ`
- `COMPLEX_ADD_RDISTRIB`
- `COMPLEX_ADD_CNJ`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_CX`
- `COMPLEX_NORM_INV`
- `COMPLEX_NORM_POW`
- `CX_MUL`
- `CX_DIV`
- `CX_POW`
- `COMPLEX_MUL_ASSOC`


---

## BOUND_LEMMA_1

### Name of formal statement
BOUND_LEMMA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_1 = prove
 (`!z R. norm(z) = R
         ==> norm(Cx(&1) / z + z / Cx(R) pow 2) = &2 * abs(Re z) / R pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BOUND_LEMMA_0; COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_MESON_TAC[NORM_ARITH `norm z = R ==> abs R = R`]);;
```

### Informal statement
For all complex numbers `z` and real numbers `R`, if the norm of `z` is equal to `R`, then the norm of the complex number `Cx(&1) / z + z / Cx(R) pow 2` is equal to `2 * abs(Re z) / R pow 2`.

### Informal sketch
The proof proceeds as follows:
- Assume `norm(z) = R`.
- Simplify the expression `norm(Cx(&1) / z + z / Cx(R) pow 2)` using `BOUND_LEMMA_0` and `COMPLEX_NORM_CX`.
- Rewrite the expression using the following lemmas: `REAL_ABS_MUL`, `REAL_ABS_DIV`, `REAL_ABS_POW`, and `REAL_ABS_NUM`.
- Complete the proof using `ASM_MESON_TAC` and the arithmetic fact `norm z = R ==> abs R = R`.

### Mathematical insight
This lemma provides a specific bound on the norm of a complex expression, given that the norm of `z` is equal to `R`. It seems related to some calculation involving complex numbers and their norms, possibly in the context of complex analysis or estimations.

### Dependencies
- Theorems: `BOUND_LEMMA_0`, `COMPLEX_NORM_CX`, `REAL_ABS_MUL`, `REAL_ABS_DIV`, `REAL_ABS_POW`, `REAL_ABS_NUM`
- Meson database: `NORM_ARITH`


---

## BOUND_LEMMA_2

### Name of formal statement
BOUND_LEMMA_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_2 = prove
 (`!R x z. Re(z) = --x /\ abs(Im(z)) = R /\ &0 <= x /\ &0 < R
           ==> norm (Cx (&1) / z + z / Cx R pow 2) <= &2 * x / R pow 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_LE_SQUARE; COMPLEX_SQNORM; DOT_SQUARE_NORM] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
  ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  REWRITE_TAC[complex_div] THEN
  SUBST1_TAC(SPEC `z:complex` COMPLEX_INV_CNJ) THEN
  ASM_SIMP_TAC[cnj; RE; IM; COMPLEX_MUL_LID; REAL_LE_MUL; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_POW; COMPLEX_SQNORM; RE; IM] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`] THEN
  REWRITE_TAC[GSYM CX_INV; complex_div] THEN
  REWRITE_TAC[complex_mul; complex_add; RE; IM; RE_CX; IM_CX;
              REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`;
   REAL_RING `(--x * a + --x * b:real) pow 2 = x pow 2 * (a + b) pow 2`;
   REAL_RING `(--R * a + R * b:real) pow 2 = R pow 2 * (b - a) pow 2`] THEN
  SUBGOAL_THEN `&0 < x pow 2 + R pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im z pow 2 = R pow 2` SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
   `&0 < R pow 2 /\ &0 < x pow 2 + R pow 2
    ==> x pow 2 * (inv (x pow 2 + R pow 2) + inv (R pow 2)) pow 2 +
        R pow 2 * (inv (R pow 2) - inv (x pow 2 + R pow 2)) pow 2 =
        (x pow 4 + &5 * R pow 2 * x pow 2 + &4 * R pow 4) /
        (x pow 2 + R pow 2) pow 2 *
        (x pow 2 / R pow 4)`] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
  `&0 < R pow 2 ==> (&2 * x / R pow 2) pow 2 = &4 * x pow 2 / R pow 4`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LT_IMP_LE]);;
```

### Informal statement
For all real numbers `R`, `x`, and complex number `z`, if the real part of `z` equals the negation of `x`, the absolute value of the imaginary part of `z` equals `R`, `0` is less than or equal to `x`, and `0` is strictly less than `R`, then the norm of the complex number `(1/z) + (z/R^2)` is less than or equal to `2x/R^2`.

### Informal sketch
The proof establishes an upper bound on the norm of a complex expression, given certain constraints on the real and imaginary parts of the complex variable `z`.

- First, the goal is stripped.
- The norm is converted into a square norm, and the squared norm is expressed as a dot product. The condition `0 <= 2 * x <=> 0 <= x` is used to simplify.
- Assumptions are simplified using `REAL_POS`, `REAL_LE_DIV`, `REAL_LT_IMP_LE`, AND `REAL_POW_LT`.
- Rewrite with `complex_div`.
- The complex inverse is rewritten with `COMPLEX_INV_CNJ`.
- Assumptions are simplified with `cnj`, `RE`, `IM`, `COMPLEX_MUL_LID`, `REAL_LE_MUL` and `REAL_POS`.
- Rewrite using `CX_POW` and `COMPLEX_SQNORM`, `RE`, `IM`.
- Rewrite using `REAL_RING` facts about squares of negation.
- Rewrite by reducing `CX_INV` and `complex_div`.
- Rewrite by reducing `complex_mul`, `complex_add`, `RE`, `IM`, `RE_CX`, `IM_CX`, `REAL_MUL_RZERO`, `REAL_SUB_RZERO` and `REAL_ADD_LID`.
- Rewrite with `REAL_RING` arithmetic identities.
- Prove `0 < x pow 2 + R pow 2` by showing `0 <= x /\ 0 < R ==> 0 < x + R`.
- Prove `Im z pow 2 = R pow 2` by using `REAL_POW2_ABS`.
- Simplify using field arithmetic facts and lemmas.
- Simplify using facts to derive  `(&2 * x / R pow 2) pow 2 = &4 * x pow 2 / R pow 4`.
- Reduce via the inequalities `REAL_LE_RMUL`, `REAL_LT_IMP_LE` and `REAL_LE_LDIV_EQ`.
- Rewrite with `REAL_SUB_LE`, then convert into a polynomial, then break the goal into component parts, repeatedly applying `REAL_LE_MUL` and `REAL_LE_ADD`.
- Finally, simplify using facts about orderings.

### Mathematical insight
This lemma provides a specific bound on a complex expression that appears to be related to complex analysis or geometry. The assumptions constrain the complex number `z` to a specific region in the complex plane (negative real part, controlled imaginary part), enabling a well-defined bound. The lemma helps to bound the magnitude of expressions involving complex reciprocals and powers, which is commonly useful in complex analysis, perhaps for bounding remainders in series.

### Dependencies
- `NORM_LE_SQUARE`
- `COMPLEX_SQNORM`
- `DOT_SQUARE_NORM`
- `REAL_ARITH`
- `REAL_POS`
- `REAL_LE_DIV`
- `REAL_LT_IMP_LE`
- `REAL_POW_LT`
- `complex_div`
- `COMPLEX_INV_CNJ`
- `cnj`
- `RE`
- `IM`
- `COMPLEX_MUL_LID`
- `REAL_LE_MUL`
- `REAL_POS`
- `GSYM`
- `CX_POW`
- `REAL_RING`
- `CX_INV`
- `complex_mul`
- `complex_add`
- `RE_CX`
- `IM_CX`
- `REAL_MUL_RZERO`
- `REAL_SUB_RZERO`
- `REAL_ADD_LID`
- `REAL_POW2_ABS`
- `REAL_FIELD`
- `REAL_LE_RMUL`
- `REAL_LE_DIV`
- `REAL_POW_LE`
- `REAL_LE_LDIV_EQ`
- `REAL_SUB_LE`
- `REAL_POLY_CONV`
- `REAL_LE_ADD`

### Porting notes
- The extensive use of `REAL_RING` suggests that a similarly powerful ring tactic will be helpful in other provers.
- The dependency on `REAL_FIELD` suggests that the target prover has good automation for field arithmetic.
- The tactic `ASM_SIMP_TAC` implies a strong simplifier tightly integrated with the assumption list.


---

## BOUND_LEMMA_3

### Name of formal statement
BOUND_LEMMA_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_3 = prove
 (`!a n. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
         1 <= n /\ &1 <= Re w /\ &0 < Re z
         ==> norm(vsum(1..n) (\n. a(n) / Cx(&n) cpow (w - z)))
                  <= exp(Re(z) * log(&n)) * (&1 / &n + &1 / Re(z))`,
  let lemma1 = prove
   (`!n x.
          &1 <= x
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n + &1)) / x`,
    REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `1`; `n:num`]
    SUM_INTEGRAL_UBOUND_INCREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < n <=> 1 <= n`;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[CPOW_1] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC)
  and lemma1' = prove
   (`!n x.
          &0 < x /\ x <= &1
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n)) / x`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_EXP_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; ARITH] THEN
    ASM_CASES_TAC `2 <= n` THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
      SUBGOAL_THEN `n = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; real_div; REAL_MUL_LID;
                   REAL_ADD_RID; REAL_INV_1_LE]] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `2`; `n:num`]
    SUM_INTEGRAL_UBOUND_DECREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o
            GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - x) * a <= (&1 - x) * b ==> (x - &1) * b <= (x - &1) * a`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x = y /\ &1 + u <= v ==> x <= u ==> &1 + y <= v`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[CPOW_1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= i ==> 0 < i`] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 + a - x <= a`) THEN
    ASM_SIMP_TAC[REAL_INV_1_LE; real_div; REAL_MUL_LID]) in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\n. exp((Re(z) - &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; ARITH_RULE `0 < k <=> 1 <= k`] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; GSYM RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_SUB] THEN UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  DISJ_CASES_TAC(ARITH_RULE `x <= &1 \/ &1 <= x`) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&n)) / x` THEN
    ASM_SIMP_TAC[lemma1'] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `x <= a + x <=> &0 <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_LE_INV_EQ; REAL_POS];
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= x * a /\ c <= x * d ==> c + b <= x * (a + d)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_LID; EXP_LOG; REAL_OF_NUM_LT;
                   ARITH_RULE `0 < n <=> 1 <= n`; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&(n - 1) + &1)) / x` THEN CONJ_TAC THEN
    ASM_SIMP_TAC[lemma1] THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> n - 1 + 1 = n`] THEN
    REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LID]]);;
```
### Informal statement
For all complex-valued sequences `a`, natural numbers `n`, and complex numbers `w` and `z`, if for all natural numbers `m`, if `1 <= m` then the norm of `a(m)` is less than or equal to 1, and `1 <= n`, and the real part of `w` is greater than or equal to 1, and the real part of `z` is greater than 0, then the norm of the sum from 1 to `n` of `a(n) / n^(w - z)` is less than or equal to `exp(Re(z) * log(n)) * (1 / n + 1 / Re(z))`.

### Informal sketch
The proof proceeds by induction-like reasoning and estimation of the norm of a complex sum. The main steps are as follows:
- A lemma `lemma1` is proved: For all natural numbers `n` and real numbers `x`, if `1 <= x`, then `sum(1..n) (\n. exp((x - 1) * log(n))) <= exp(x * log(n + 1)) / x`. This is proved by induction on `n`. The base case `n = 0` and inductive step `1 <= n` are considered. The inductive step uses `SUM_INTEGRAL_UBOUND_INCREASING` to bound the sum by an integral, and the conditions for this theorem are verified.
- Another lemma `lemma1'` is proved: For all natural numbers `n` and real numbers `x`, if `0 < x` and `x <= 1`, then `sum(1..n) (\n. exp((x - 1) * log(n))) <= exp(x * log(n)) / x`. This is proven by cases: firstly, the case `n = 0` and the inductive step `1 <= n` are considered. The case `1 <= n` is further split into two cases `2 <= n` and `~(2 <= n)`. The case `2 <= n` again uses `SUM_INTEGRAL_UBOUND_DECREASING` to bound the sum by an integral, with its conditions verified; the case `~(2 <= n)` implies `n = 1`, which can be proved by arithmetic, and the main statement is then proved trivially.
- The main statement is then proved using the two lemmas and basic norm inequalities. It starts by applying `VSUM_NORM_LE` to bound the norm of the sum by the sum of the norms. The assumption `!m. 1 <= m ==> norm(a(m)) <= &1` is used to simplify the norm in the sum. Lemmas `lemma1` and `lemma1'` are used to bound a real sum, derived by taking `x = Re(z)`, leading to two cases `x <= &1 \/ &1 <= x`.

### Mathematical insight
The bound on the norm of the given sum is obtained by bounding the summands and using an integral bound for the sum of exponential terms. The decomposition using the real lemmas `lemma1` and `lemma1'` allows application of integral bounds for the sum of exponential terms. The complex parts are dealt with using `VSUM_NORM_LE` and properties of the complex norm and exponential functions.

### Dependencies
- `NUMSEG_CLAUSES`
- `ARITH`
- `SUM_CLAUSES`
- `REAL_LE_DIV`
- `REAL_EXP_POS_LE`
- `REAL_SEGMENT`
- `REAL_CX`
- `REAL`
- `IN_SEGMENT_CX`
- `RE_CX`
- `CX_INJ`
- `CX_SUB`
- `CPOW_REAL_REAL`
- `REAL_ARITH`
- `REAL_EXP_MONO_LE`
- `LOG_MONO_LE_IMP`
- `SUM_EQ_NUMSEG`
- `REAL_OF_NUM_LT`
- `CPOW_1`
- `CX_DIV`
- `REAL_MUL_LID`
- `REAL_LE_INV_EQ`
- `LOG_1`
- `REAL_MUL_RZERO`
- `REAL_EXP_0`
- `SUM_CLAUSES_LEFT`
- `NUMSEG_EMPTY`
- `REAL_INV_1_LE`
- `REAL_RAT_REDUCE_CONV`
- `GSYM`
- `NOT_LE`
- `LE_1`
- `COMPLEX_NORM_DIV`
- `NORM_CPOW_REAL`
- `REAL_EXP_NEG`
- `REAL_MUL_LNEG`
- `NORM_POS_LE`
- `REAL_EXP_POS_LE`
- `LOG_POS`
- `REAL_OF_NUM_LE`
- `RE_NEG`
- `COMPLEX_NEG_SUB`
- `RE_SUB`
- `EXP_LOG`
- `REAL_POS`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `VSUM_NORM_LE`
- `SUM_INTEGRAL_UBOUND_INCREASING`
- `SUM_INTEGRAL_UBOUND_DECREASING`

### Porting notes (optional)
- The theorems `SUM_INTEGRAL_UBOUND_INCREASING` and `SUM_INTEGRAL_UBOUND_DECREASING` needs to be found or proven
- The porting will require the theories of real and complex analysis, including properties of `exp`, `log`, `cpow` and related functions.


---

## BOUND_LEMMA_4

### Name of formal statement
BOUND_LEMMA_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_4 = prove
 (`!a n m. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
           1 <= n /\ &1 <= Re w /\ &0 < Re z
           ==> norm(vsum(n+1..m) (\n. a(n) / Cx(&n) cpow (w + z)))
                    <= &1 / (Re z * exp(Re z * log(&n)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(n+1..m) (\n. &1 / exp((Re(z) + &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r /\ 1 <= r` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_ADD; REAL_LE_NEG2] THEN
    UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  ASM_CASES_TAC `n + 1 <= m` THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
    SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_EXP_POS_LE; REAL_LT_IMP_LE]] THEN
  MP_TAC(ISPECL
   [`\n. n cpow (--(Cx(x) + Cx(&1)))`;
    `\n. --(n cpow (--(Cx(x)))) / Cx(x)`;
    `n + 1`; `m:num`]
   SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
         [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
        REWRITE_TAC[RE_CX] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_RING `--x - Cx(&1) = --(x + Cx(&1))`] THEN
      SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
       [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
        CONV_TAC COMPLEX_FIELD];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x * a <= x * b ==> --x * b <= --x * a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[CPOW_NEG] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 <= n ==> 0 < n`)) THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[GSYM CX_INV; GSYM CX_SUB; RE_CX; GSYM CX_DIV; GSYM CX_NEG] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_SUB_NEG2; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x = z /\ &0 <= y ==> x - y <= z`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_EXP_POS_LE]);;
```

### Informal statement
For all functions `a` from natural numbers to complex numbers, and for all natural numbers `n` and `m`, if for every natural number `m`, `1 <= m` implies `norm(a(m)) <= 1`, and `1 <= n`, and `1 <= Re(w)`, and `0 < Re(z)`, then `norm(vsum(n+1..m) (\n. a(n) / Cx(&n) cpow (w + z))) <= 1 / (Re z * exp(Re z * log(&n)))`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the assumptions.
- Apply `REAL_LE_TRANS` to introduce an intermediate term involving a sum of real numbers, specifically `sum(n+1..m) (\n. &1 / exp((Re(z) + &1) * log(&n)))`.
- Split the goal into two subgoals: proving the original inequality holds if we use above mentioned intermediate sum and proving the intermediate sum itself.
- For the first subgoal, use `VSUM_NORM_LE` to bound the norm of the sum by the sum of the norms. Rewrite using `FINITE_NUMSEG` and `IN_NUMSEG`.
- Introduce a real variable `r` and assume `0 < r` and `1 <= r`.
- Simplify using properties of complex norms, complex exponentiation, and real representations of complex numbers.
- Rewrite using `real_div` and `REAL_EXP_NEG`.
- Apply `REAL_LE_MUL2`, and simplify again with norm and exponential properties.
- Rewrite using `REAL_MUL_LNEG` and apply `REAL_LE_RMUL`.
- Simplify using logarithm properties and rewrite. Then reduce using real arithmetic (`REAL_ARITH_TAC`). This completes the proof of the first subgoal.
- For the second subgoal, abbreviate `Re z` as `x`.
- Perform case analysis on `n + 1 <= m`.
  - If `n + 1 <= m` is false, use properties of empty summations and simplify using real arithmetic and exponential properties.
  - If `n + 1 <= m`, use `SUM_INTEGRAL_UBOUND_DECREASING` with appropriate substitutions.
- Rewrite and simplify using real arithmetic.
- Prove the conditions for `SUM_INTEGRAL_UBOUND_DECREASING` by showing the relevant function is differentiable and decreasing.
  - Prove differentiability using `COMPLEX_DIFF_TAC` and properties of `Cx`.
  - For the decreasing property, show that `&0 < a` and `&0 < b` implies the comparison of the two terms where the exponent is involved, this requires some real arithmetic and logarithmic properties. This is broken down into several steps.
- Apply `REAL_ARITH` and split the goal into two parts.
  - Prove an equality involving sums using `SUM_EQ_NUMSEG`. For that requires to prove that `&0 < &k` where `k` is from `n+1` to `m` and then using arithmetic tactics to reduce each term of the equality to `0`.
  - Rewrite using `CPOW_NEG`, and make assumptions about the positivity of `n` and `m`.
- Finally, several simplifications along with real arithmetic are applied to conclude the proof.

### Mathematical insight
The theorem provides an upper bound for the norm of a complex-valued sum. It is crucial for establishing convergence or estimating the error in approximations involving complex functions. The proof involves bounding the sum by an integral, which is a standard technique in analysis.

### Dependencies
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `COMPLEX_NORM_DIV`
- `NORM_CPOW_REAL`
- `REAL_CX`
- `RE_CX`
- `REAL_OF_NUM_LT`
- `real_div`
- `GSYM REAL_EXP_NEG`
- `NORM_POS_LE`
- `REAL_EXP_POS_LE`
- `REAL_EXP_MONO_LE`
- `GSYM REAL_MUL_LNEG`
- `LOG_POS`
- `REAL_OF_NUM_LE`
- `RE_NEG`
- `COMPLEX_NEG_SUB`
- `RE_ADD`
- `REAL_LE_NEG2`
- `NOT_LE`
- `GSYM NUMSEG_EMPTY`
- `SUM_CLAUSES`
- `REAL_MUL_LID`
- `REAL_LE_INV_EQ`
- `REAL_LE_MUL`
- `REAL_LT_IMP_LE`
- `SUM_INTEGRAL_UBOUND_DECREASING`
- `GSYM REAL_OF_NUM_ADD`
- `REAL_ARITH`
- `REAL_SEGMENT`
- `REAL`
- `IN_SEGMENT_CX`
- `COMPLEX_RING`
- `CX_INJ`
- `COMPLEX_FIELD`
- `GSYM CX_ADD`
- `GSYM CX_NEG`
- `CPOW_REAL_REAL`
- `REAL_EXP_MONO_LE`
- `LOG_MONO_LE_IMP`
- `SUM_EQ_NUMSEG`
- `CPOW_NEG`
- `GSYM CX_INV`
- `GSYM CX_SUB`
- `GSYM CX_DIV`
- `REAL_SUB_NEG2`
- `GSYM REAL_INV_MUL`
- `REAL_MUL_AC`

### Porting notes (optional)
- The theorem involves complex analysis and real analysis. Ensure the target proof assistant has adequate support for these areas.
- `SUM_INTEGRAL_UBOUND_DECREASING` is a key element in the proof, so ensure the target system has a similar theorem or that it can be derived.
- HOL Light's rewriting tactics (e.g., `REWRITE_TAC`, `ASM_REWRITE_TAC`) may need to be adapted to the corresponding mechanisms in other proof assistants.


---

## OVERALL_BOUND_LEMMA

### Name of formal statement
OVERALL_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OVERALL_BOUND_LEMMA = prove
 (`!d M R. &0 < d
           ==> !e. &0 < e
                   ==> ?N. !n. N <= n
                               ==> abs(&2 * pi / &n +
                                       &6 * M * R / (d * exp (d * log (&n))) +
                                       &4 * M / (R * log (&n)) pow 2) < e`,
  ONCE_REWRITE_TAC[REAL_ARITH `abs x = abs(x - &0)`] THEN
  REWRITE_TAC[GSYM REALLIM_SEQUENTIALLY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  REPEAT(MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N] THENL
   [MP_TAC(SPEC `Cx d` LIM_1_OVER_POWER) THEN ASM_REWRITE_TAC[RE_CX] THEN
    REWRITE_TAC[REALLIM_COMPLEX; o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT; CX_INV; LE_1;
             complex_div; COMPLEX_MUL_LID];
    MATCH_MP_TAC REALLIM_NULL_POW THEN REWRITE_TAC[REAL_INV_MUL; ARITH] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_LOG]]);;
```

### Informal statement
For all real numbers `d`, `M`, and `R`, if `0 < d`, then for all real numbers `e`, if `0 < e`, then there exists a natural number `N` such that for all natural numbers `n`, if `N <= n`, then the absolute value of `2 * pi / n + 6 * M * R / (d * exp(d * log(n))) + 4 * M / (R * log(n))^2` is less than `e`.

### Informal sketch
The proof demonstrates that the given expression converges to zero as `n` approaches infinity. The proof proceeds as follows:
- The goal is to show that `abs(2 * pi / n + 6 * M * R / (d * exp(d * log(n))) + 4 * M / (R * log(n))^2) < e` for sufficiently large `n`.
- First, rewrite the goal to consider the limit as `n` approaches infinity.
- Repeatedly strip the universal and implication quantifiers (`REPEAT STRIP_TAC`).
- Rewrite the divisions and inverse multiplications (`REWRITE_TAC[real_div; REAL_INV_MUL]`).
- Apply the fact that the limit of a sum is the sum of limits, splitting the expression (`REPEAT(MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC)`).  This involves showing that each of the three terms `2 * pi / n`, `6 * M * R / (d * exp(d * log(n)))`, and `4 * M / (R * log(n))^2` converges to zero as `n` goes to infinity.
- Use associativity and inverse power rules to prepare for applying limits of simpler terms (`REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_INV]`).
- Show that the limit of `2 * pi / n` goes to zero using `REALLIM_NULL_LMUL` and `REALLIM_1_OVER_N`.
- For the term `6 * M * R / (d * exp(d * log(n)))`, the limit of `1 / exp(d * log(n))` is shown to go to zero using `LIM_1_OVER_POWER`, along with complex exponential/logarithm conversion (`Cx`), and the transformation to eventually sequential limits.
- For the term `4 * M / (R * log(n))^2`, show that the limit goes to zero using `REALLIM_NULL_POW` and `REALLIM_NULL_LMUL` with `REALLIM_1_OVER_LOG`.

### Mathematical insight
The theorem establishes that a certain expression involving `n`, `log(n)`, and `exp(log(n))` converges to zero as `n` tends to infinity. The expression arises in the context of bounding some error term in an approximation (though the specific error is not explicit here). The convergence to zero is crucial for showing that the approximation becomes arbitrarily accurate for sufficiently large `n`.

### Dependencies
**Theorems/Definitions about Real Numbers and Limits:**
- `REAL_ARITH`
- `REALLIM_SEQUENTIALLY`
- `real_div`
- `REAL_INV_MUL`
- `REALLIM_NULL_ADD`
- `REAL_MUL_ASSOC`
- `REAL_POW_INV`
- `REALLIM_NULL_LMUL`
- `REALLIM_1_OVER_N`
- `REALLIM_NULL_POW`
- `REALLIM_1_OVER_LOG`
- `LIM_1_OVER_POWER`
- `LIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`

**Theorems/Definitions about Complex Numbers and Reals:**
- `Cx`
- `RE_CX`
- `REALLIM_COMPLEX`
- `o_DEF`
- `CPOW_REAL_REAL`
- `REAL_CX`
- `REAL_OF_NUM_LT`
- `CX_INV`
- `LE_1`
- `complex_div`
- `COMPLEX_MUL_LID`

**Tactics**
- `ONCE_REWRITE_TAC`
- `REWRITE_TAC`
- `GSYM`
- `REPEAT`
- `STRIP_TAC`
- `MATCH_MP_TAC`
- `CONJ_TAC`
- `THENL`
- `MP_TAC`
- `SPEC`
- `ASM_REWRITE_TAC`
- `REALLIM_COMPLEX`
- `IMP_CONJ`
- `EXISTS_TAC`
- `SIMP_TAC`

### Porting notes (optional)
- The proof relies heavily on rewriting rules and limit theorems that are specific to HOL Light's real analysis library.  When porting, it's crucial to identify equivalent theorems and definitions in the target proof assistant.
- The tactics used also have to be adapted accordingly. Specifically, the porting may require constructing explicit witnesses for the existential quantifier (`?N`). The expression `exp(d * log(n))` where `exp` and `log` refer to the real functions needs careful handling.


---

## NEWMAN_INGHAM_THEOREM

### Name of formal statement
NEWMAN_INGHAM_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM = prove
 (`!f a. (!n. 1 <= n ==> norm(a(n)) <= &1) /\
         f analytic_on {z | Re(z) >= &1} /\
         (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
         ==> !z. Re(z) >= &1
                 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REWRITE_TAC[real_ge; analytic_on; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&1 <= w ==> w > &1 \/ w = &1`)) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ABBREV_TAC `R = max (&3 / e) (&1)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= R /\
        (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))))
  THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\
          (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
     (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)
    THENL
     [ALL_TAC;
      EXISTS_TAC `min d R` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re(z) >= --d /\ abs(Im z) <= R}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC] THEN
    ABBREV_TAC `g = \z. (f:complex->complex) (w + z)` THEN
    SUBGOAL_THEN
     `!z. &0 <= Re z ==> ?e. &0 < e /\ g holomorphic_on ball (z,e)`
    MP_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!z. &1 <= Re z ==> (?e. &0 < e /\ f holomorphic_on ball (z,e))` THEN
      DISCH_THEN(MP_TAC o SPEC `w + z:complex`) THEN
      ASM_SIMP_TAC[RE_ADD;REAL_ARITH `&0 <= z ==> &1 <= &1 + z`] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
      SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
      UNDISCH_TAC `f holomorphic_on ball(w + z,d)` THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_BALL; IN_IMAGE] THEN
      REWRITE_TAC[COMPLEX_RING `x:complex = w + y <=> x - w = y`] THEN
      REWRITE_TAC[UNWIND_THM1] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `bs:complex->real`) THEN
    MP_TAC(ISPECL [`complex(&0,--R)`; `complex(&0,R)`] COMPACT_INTERVAL) THEN
    REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\z. {w | abs(Re(z - w)) < bs z / &2 /\ abs(Im(z - w)) < bs z / &2})
            (interval[complex(&0,--R),complex(&0,R)])`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[RE_SUB; IM_SUB; REAL_ARITH
         `abs(x - a) < e /\ abs(y - b) < e <=>
          a < x + e /\ a > x - e /\ b < y + e /\ b > y - e`] THEN
        SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        REPEAT(MATCH_MP_TAC OPEN_INTER THEN STRIP_TAC) THEN
        REWRITE_TAC[OPEN_HALFSPACE_IM_GT; OPEN_HALFSPACE_IM_LT;
                    OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> x IN g x) ==> s SUBSET (UNIONS (IMAGE g s))`) THEN
      REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_NUM] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      ASM_MESON_TAC[REAL_HALF];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ b /\ a`] THEN
    REWRITE_TAC[FINITE_SUBSET_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> d /\ a /\ b /\ c`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inf (IMAGE (bs:complex->real) t) / &2` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET UNIONS (IMAGE g t) ==> ~(s = {}) ==> ~(t = {})`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `complex(&0,&0)` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    REWRITE_TAC[REAL_HALF] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (!x. x IN s ==> P x) ==> (!x. x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_WITHIN THEN
    ASM_CASES_TAC `&0 <= Re z` THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable; OPEN_BALL;
                    CENTRE_IN_BALL];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `complex(&0,Im z)` o MATCH_MP (SET_RULE
     `i SUBSET UNIONS s ==> !x. x IN i ==> x IN UNIONS s`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `abs(Im z) <= R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:complex` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `Re v = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:complex) IN t` THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (x IN s ==> P x) ==> (x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; RE_SUB; IM_SUB; RE; IM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    UNDISCH_TAC
     `!z. &0 <= Re z ==> &0 < bs z /\ g holomorphic_on ball (z,bs z)` THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; GSYM complex_differentiable] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL] THEN
    REWRITE_TAC[dist; complex_norm] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x < abs e ==> x < e`) THEN
    ASM_REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < b * b /\ x <= (b / &2) pow 2 /\ y <= (b / &2) pow 2
      ==> x + y < b pow 2`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[IM_SUB; REAL_ARITH `&0 < b ==> abs(b / &2) = b / &2`] THEN
    ASM_SIMP_TAC[RE_SUB; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `--(x / &2) <= z ==> &2 * --z <= x`)) THEN
    ASM_SIMP_TAC[REAL_LE_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&0 <= Re z)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. &0 < M /\
        !z. Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R
            ==> norm(f(w + z):complex) <= M`
  (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2a"))) THENL
   [MP_TAC(ISPEC `IMAGE (\z. f (w + z):complex)
                        {z | Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R}`
                 COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
      MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                        CONTINUOUS_ON_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(Cx(&0),&2 * R + d)` THEN
      REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL; dist] THEN
      REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; IN_ELIM_THM] THEN
      MP_TAC COMPLEX_NORM_LE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_ARITH `x <= Im z <=> Im z >= x`] THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_RE_LE; CLOSED_HALFSPACE_IM_LE;
                CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_IM_GE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `M:real`; `R:real`] OVERALL_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 / &3 * e * pi`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_ARITH `&0 < &2 / &3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "X")) THEN
  EXISTS_TAC `N0 + 2` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REMOVE_THEN "X" (MP_TAC o SPEC `N:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `N0 + 2 <= N ==> N0 <= N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(N = 0) /\ 1 < N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  ABBREV_TAC `S_N(w) = vsum(1..N) (\n. a(n) / Cx(&n) cpow w)` THEN
  REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ABBREV_TAC `r_N(w) = (f:complex->complex)(w) - S_N(w)` THEN
  ABBREV_TAC `A = partcirclepath(Cx(&0),R,--(pi / &2),pi / &2)` THEN
  SUBGOAL_THEN
   `valid_path A /\
    pathstart A = complex(&0,--R) /\
    pathfinish A = complex(&0,R) /\
    &0 < Re(winding_number(A,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[VALID_PATH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[PATHSTART_PARTCIRCLEPATH; PATHFINISH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[CEXP_EULER; SIN_NEG; COS_NEG; SIN_PI2; COS_PI2;
                GSYM CX_SIN; GSYM CX_COS] THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; RE_II; IM_II; IM_MUL_CX; RE; IM] THEN
    REPEAT(CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC WINDING_NUMBER_PARTCIRCLEPATH_POS_LT THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_SUB_REFL] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A SUBSET {z | Re(z) >= &0 /\ norm(z) = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    ASM_SIMP_TAC[PATH_IMAGE_PARTCIRCLEPATH; REAL_LT_IMP_LE; PI_POS;
                 REAL_ARITH `--p < p <=> &0 < p`; REAL_HALF] THEN
    REWRITE_TAC[SUBSET; COMPLEX_ADD_LID; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE_MUL_CX; RE_CEXP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX; RE_MUL_II] THEN
    REWRITE_TAC[IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; real_ge] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[IM_MUL_II; RE_CX] THEN ASM_SIMP_TAC[COS_POS_PI_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_NORM_0] THEN
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = linepath(complex(&0,R),complex(--d,R)) ++
                  linepath(complex(--d,R),complex(--d,--R)) ++
                  linepath(complex(--d,--R),complex(&0,--R))` THEN
  SUBGOAL_THEN
   `valid_path B /\
    ~(Cx(&0) IN path_image B) /\
    &0 < Re(winding_number(B,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC WINDING_NUMBER_JOIN_POS_COMBINED THEN
           REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                       PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
           CONJ_TAC) THEN
    (REWRITE_TAC[VALID_PATH_LINEPATH] THEN CONJ_TAC THENL
      [ALL_TAC;
       MATCH_MP_TAC WINDING_NUMBER_LINEPATH_POS_LT THEN
       REWRITE_TAC[complex_mul; RE; IM; RE_SUB; RE_CNJ; IM_SUB; IM_CNJ;
                   RE_CX; IM_CX] THEN
       CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
       ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]]) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; segment; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CMUL; RE_ADD; RE_CX; RE;
                            IM_CMUL; IM_ADD; IM_CX; IM] THEN
    REWRITE_TAC[REAL_ARITH `&0 = (&1 - u) * x + u * x <=> x = &0`] THEN
    ASM_SIMP_TAC[REAL_NEG_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart B = complex(&0,R) /\
    pathfinish B = complex(&0,--R)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image B SUBSET {z | --d <= Re z /\ Re(z) <= &0 /\ abs(Im z) <= R}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `convex {z | --d <= Re z /\ Re z <= &0 /\ abs (Im z) <= R}`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_BOUNDS_LE;
        SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[REWRITE_RULE[real_ge] CONVEX_HALFSPACE_RE_GE;
                  REWRITE_RULE[real_ge] CONVEX_HALFSPACE_IM_GE;
                  CONVEX_HALFSPACE_RE_LE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC(SET_RULE
            `path_image(p1 ++ p2) SUBSET path_image p1 UNION path_image p2 /\
             path_image p1 SUBSET s /\ path_image p2 SUBSET s
             ==> path_image(p1 ++ p2) SUBSET s`) THEN
           REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN CONJ_TAC) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE; IM] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d`; `&0 < R`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ B) /\
    pathstart(A ++ B) = complex(&0,--R) /\
    pathfinish(A ++ B) = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ B))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATH_IMAGE_JOIN; IN_UNION; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++B,Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; PATH_IMAGE_JOIN; IN_UNION;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * f(w))) (A ++ B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `{z | Re(z) >= --d /\ abs(Im z) <= R}`;
      `A ++ B:real^1->complex`;
      `Cx(&0)`]
        CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `abs(x) <= a <=> x >= --a /\ x <= a`] THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_HALFSPACE_RE_GE] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_HALFSPACE_IM_GE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ADD] THEN
      REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      EXISTS_TAC `clog(Cx(&N)) * Cx(&N) cpow z` THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT THEN
      ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min d R:real` THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
      REWRITE_TAC[SUBSET; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(n1) <= n /\ abs(n2) <= n
        ==>  n < min d R ==> n1 >= --d /\ abs n2 <= R`) THEN
      REWRITE_TAC[COMPLEX_NORM_GE_RE_IM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH; UNION_SUBSET] THEN
    CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MP_TAC COMPLEX_NORM_GE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fA:complex` (LABEL_TAC "fA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fB:complex` (LABEL_TAC "fB")) THEN
  SUBGOAL_THEN `integral_fA + integral_fB = Cx(&2) * Cx pi * ii * f(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ B:real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  ABBREV_TAC `A' = (--) o (A:real^1->complex)` THEN
  SUBGOAL_THEN
   `valid_path A' /\
    pathstart A' = complex(&0,R) /\
    pathfinish A' = complex(&0,--R) /\
    ~(Cx(&0) IN path_image A') /\
    &0 < Re(winding_number(A',Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN
    ASM_SIMP_TAC[VALID_PATH_NEGATEPATH; PATHSTART_NEGATEPATH;
                 PATHFINISH_NEGATEPATH; WINDING_NUMBER_NEGATEPATH;
                 PATH_IMAGE_NEGATEPATH] THEN
    REWRITE_TAC[IN_IMAGE; COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
    ASM_REWRITE_TAC[UNWIND_THM2] THEN
    SIMP_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE; IM; REAL_NEG_0; REAL_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ A') /\
    pathstart(A ++ A') = complex(&0,--R) /\
    pathfinish(A ++ A') = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ A')) /\
    path_image(A ++ A') = path_image A UNION path_image A'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; IN_UNION;
                 PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A' SUBSET {z | Re z <= &0 /\ norm z = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[path_image; IMAGE_o; SUBSET] THEN
    ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[GSYM path_image] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; RE_NEG; NORM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++A',Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; IN_UNION;
                 VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. S_N (w + z) * Cx (&N) cpow z * (Cx (&1) + z pow 2 * inv (Cx R pow 2)))
    holomorphic_on (:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
      REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV;
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_CPOW_RIGHT; HOLOMORPHIC_ON_ID; CPOW_EQ_0;
          HOLOMORPHIC_ON_CONST; REAL_OF_NUM_EQ; HOLOMORPHIC_ON_MUL;
          ARITH_RULE `~(n = 0) <=> 1 <= n`;
          HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_POW; CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * S_N(w))) (A ++ A')`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `cball(Cx(&0),R)`;
      `A ++ A':real^1->complex`;
      `Cx(&0)`]
      CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; INTERIOR_CBALL; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; dist; COMPLEX_SUB_LZERO;
             NORM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA:complex` (LABEL_TAC "sA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA':complex` (LABEL_TAC "sA'")) THEN
  SUBGOAL_THEN
   `integral_sA + integral_sA' = Cx(&2) * Cx pi * ii * S_N(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ A':real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w - z) * Cx (&N) cpow (--z) * (Cx (&1) / z + z / Cx R pow 2))
     has_path_integral integral_sA') A`
  (LABEL_TAC "s'A") THENL
   [SUBGOAL_THEN `(A:real^1->complex) = (--) o (--) o A` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; COMPLEX_NEG_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
    REMOVE_THEN "sA'" MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; COMPLEX_SUB_RNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[GSYM COMPLEX_NEG_ADD; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[COMPLEX_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    path_integrable_on A`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN
    REWRITE_TAC[path_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_rA:complex` THEN DISCH_THEN(LABEL_TAC "rA") THEN
  SUBGOAL_THEN `integral_fA - integral_sA:complex = integral_rA`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A:real^1->complex`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r_N(w:complex) = ((integral_rA - integral_sA') + integral_fB) /
                      (Cx(&2) * Cx(pi) * ii)`
  SUBST1_TAC THENL
   [SIMP_TAC[COMPLEX_FIELD `~(z = Cx(&0)) ==> (x = y / z <=> z * x = y)`;
             CX_2PII_NZ] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_MUL_ASSOC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              COMPLEX_NORM_II; REAL_MUL_RID; REAL_ABS_PI; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; PI_POS; REAL_ARITH `&0 < &2 * p <=> &0 < p`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&4 * pi / R + &2 * pi / &N +
              &6 * M * R / (d * exp(d * log(&N))) +
              &4 * M / (R * log(&N)) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `&4 * pi / R <= &4 * pi * (e / &3) /\
      y < &2 / &3 * e * pi
      ==> &4 * pi / R + y < e * &2 * pi`) THEN
    ASM_SIMP_TAC[REAL_ARITH `abs x < e ==> x < e`] THEN
    SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    EXPAND_TAC "R" THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= &2 * a /\ norm(y) <= &2 * a + b /\ norm(z) <= c
    ==> norm(x - y + z) <= &4 * a + b + c`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_rA:complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `p / &2 - --(p / &2) = p`; PI_POS_LE;
                REAL_ARITH `--(p / &2) <= (p / &2) <=> &0 <= p`] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(r = &0) ==> &2 / r pow 2 * r * x = &2 * x / r`;
                 REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / (Re z * exp(Re z * log(&N))) *
                exp(Re z * log(&N)) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_LE_REFL; REAL_FIELD
       `&0 < z /\ ~(e = &0)
        ==> &1 / (z * e) * e * &2 * z / R pow 2 = &2 / R pow 2`]] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                   REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ]] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC
     `\n. vsum(1..n) (\n. a n / Cx (&n) cpow (w + z)) - S_N(w + z)` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      MP_TAC(SPEC `w + z:complex` (ASSUME
      `!z. Re z > &1 ==> ((\n. a n / Cx(&n) cpow z) sums f z) (from 1)`)) THEN
      SIMP_TAC[RE_ADD; REAL_ARITH `&0 < z ==> &1 + z > &1`;
               ASSUME `Re w = &1`; ASSUME `&0 < Re z`] THEN
      REWRITE_TAC[sums; FROM_INTER_NUMSEG];
      ALL_TAC] THEN
    EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME
     `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum(N+1..n) (\n. a n / Cx(&n) cpow (w + z)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC BOUND_LEMMA_4 THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`]] THEN
    MATCH_MP_TAC(NORM_ARITH `y + z = x ==> norm(x - y) <= norm(z)`) THEN
    MP_TAC(SPECL [`1`; `N:num`; `n:num`] NUMSEG_COMBINE_R) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(N = 0)`; `N + 1 <= n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_UNION THEN
    REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;

    MP_TAC(ISPECL
     [`\z. S_N(w - z) * Cx(&N) cpow (--z) * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_sA':complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2 + &2 / (&N * R)`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `&0 < R /\ ~(N = &0)
      ==> (&2 / R pow 2 + &2 / (N * R)) * R * (p / &2 - --(p / &2)) =
          &2 * p / R + &2 * p / N`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
                   REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> --(x / &2) <= x / &2`] THEN
    X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(exp (Re z * log (&N)) * (&1 / &N + &1 / Re z)) *
                inv(exp(Re z * log(&N))) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_FIELD
       `~(e = &0) ==> (e * x) * inv(e) * y = x * y`] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `&0 < x ==> (n + &1 / x) * &2 * x / y = &2 / y + &2 * x * n / y`] THEN
      REWRITE_TAC[REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; LT_NZ;
       REAL_FIELD `&0 < n /\ &0 < r
                   ==> (&2 * z * &1 / n / r pow 2) * n * r = &2 * z / r`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &2 * x <= &2`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC BOUND_LEMMA_3 THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; ARITH_RULE `1 <= N <=> ~(N = 0)`];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                 REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[RE_NEG; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];

    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
    path_integrable_on B`
  MP_TAC THENL
   [ASM_MESON_TAC[path_integrable_on]; ALL_TAC] THEN
  EXPAND_TAC "B" THEN
  SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; PATHSTART_JOIN;
           PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[path_integrable_on; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_fC:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fD:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fC':complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral_fB:complex = integral_fC + integral_fD + integral_fC'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `B:real^1->complex`] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
             PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH]);
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) <= a /\ norm(x) <= &2 * b /\ norm(z) <= &2 * b
    ==> norm(x + y + z) <= a + &4 * b`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_fD:complex`;
      `complex (--d,R)`; `complex (--d,--R)`;
      `M * inv(exp(d * log(&N))) * &3 / d`]
     HAS_PATH_INTEGRAL_BOUND_LINEPATH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN `complex (--d,--R) - complex (--d,R) =
                    Cx(&2) * ii * Cx(--R)`
      SUBST1_TAC THENL
       [REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_MUL_CX; IM_MUL_CX;
                    RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; RE; IM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs(--R) = R`; REAL_ABS_NUM] THEN
      CONV_TAC REAL_FIELD] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_EXP_POS_LE;
                   REAL_LE_DIV; REAL_POS];
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Re z = --d` ASSUME_TAC THENL
     [UNDISCH_TAC `z IN segment[complex(--d,R),complex(--d,--R)]` THEN
      REWRITE_TAC[segment; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[complex(--d,R),complex(--d,--R)] SUBSET
                       {z | abs(Im z) <= R}`
    MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[REAL_ARITH `abs(x) <= r <=> x >= --r /\ x <= r`] THEN
      SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`;
          CONVEX_INTER; CONVEX_HALFSPACE_IM_LE; CONVEX_HALFSPACE_IM_GE] THEN
      REWRITE_TAC[SET_RULE `{a,b} SUBSET s <=> a IN s /\ b IN s`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < R`; `&0 < d`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CPOW_REAL_REAL; NORM_CPOW_REAL; REAL_CX; RE_CX;
                   REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `Re z = --d` THEN
      ASM_REWRITE_TAC[RE_CX] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
     `~(z = Cx(&0)) /\ ~(R = Cx(&0))
      ==> Cx(&1) / z + z / R pow 2 =
          (Cx(&1) + (z / R) pow 2) * inv(z)`] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(i) = &1 /\ norm(z) <= &2 ==> norm(i + z) <= &3`) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_POW; REAL_ABS_NUM] THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; REAL_POW_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; REAL_POW_LT;
                   CX_INJ; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
      ASM_REWRITE_TAC[COMPLEX_SQNORM] THEN
      MATCH_MP_TAC(REAL_ARITH
       `d pow 2 <= R pow 2 /\ i pow 2 <= R pow 2
        ==> --d pow 2 + i pow 2 <= &2 * R pow 2`) THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < d`; `&0 < R`; `d <= R`; `abs(Im z) <= R`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(Re z)` THEN REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. --(inv(clog(Cx(&N)) pow 2)) * (Cx(&1) + z * clog(Cx(&N))) *
         Cx(&N) cpow (--z)`;
    `\z. z * Cx(&N) cpow (--z)`;
    `linepath(Cx(&0),Cx(d))`;
    `(:complex)`] PATH_INTEGRAL_PRIMITIVE) THEN
  REWRITE_TAC[VALID_PATH_LINEPATH; SUBSET_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_ADD_LID; COMPLEX_MUL_LNEG] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `~(clog(Cx(&N)) = Cx(&0))` MP_TAC THENL
     [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ; CX_INJ] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO;
              COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_RING
   `--x * y - --x * z:complex = x * (z - y)`] THEN
  ASM_REWRITE_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; complex_pow] THEN
  ASM_SIMP_TAC[CPOW_NEG; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LT_NZ; GSYM CX_LOG; GSYM CX_MUL; GSYM CX_INV;
               GSYM CX_ADD; GSYM CX_SUB; GSYM CX_POW] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 + d) = --d`] THEN
  ABBREV_TAC
   `integral_bound =
    inv(log(&N) pow 2) *
    (&1 - (&1 + d * log(&N)) * inv(exp(d * log (&N))))` THEN
  SUBGOAL_THEN
   `&0 <= integral_bound /\ integral_bound <= inv(log(&N) pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "integral_bound" THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ;
                 REAL_POW_LT; LOG_POS_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 * x <= &1 - y /\ &1 - y <= &1 <=>
                            &0 <= y /\ y <= &1`] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_EXP_LE_X]] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; LOG_POS_LT; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&2) * Cx(M) / Cx(R) pow 2`) THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC)
       (linepath (complex (&0,R),complex (--d,R)))`;
    UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC')
      (linepath (complex(--d,--R),complex(&0,--R)))`] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL; VECTOR_DERIVATIVE_LINEPATH_AT] THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o C CONJ (ARITH_RULE `~(-- &1 = &0)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1` o
      MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG; VECTOR_NEG_0;
                VECTOR_ADD_LID; VECTOR_NEG_NEG; REAL_POW_ONE; REAL_INV_1] THEN
    REWRITE_TAC[VECTOR_ARITH `--x + y:real^1 = y - x`; VECTOR_SUB_REFL]] THEN
  (SUBGOAL_THEN
    `(!x. linepath(complex (&0,R),complex (--d,R)) x =
          ii * Cx(R) - Cx(d * drop x)) /\
     (!x. linepath(Cx (&0),Cx d) x = Cx(d * drop x)) /\
     (complex(--d,R) - complex(&0,R) = --Cx(d)) /\
     (!x. linepath(complex (--d,--R),complex(&0,--R)) (vec 1 - x) =
          --ii * Cx(R) - Cx(d * drop x)) /\
     (complex(&0,--R) - complex(--d,--R) = Cx(d))`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[linepath; COMPLEX_EQ; IM_CMUL; RE_CMUL; IM; RE; RE_SUB;
                 IM_SUB; IM_ADD; RE_ADD; RE_MUL_II; IM_MUL_II; RE_MUL_CX;
                 RE_II; IM_II; IM_MUL_CX; IM_CX; RE_CX; RE_NEG; IM_NEG;
                 DROP_SUB; DROP_VEC] THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP
    (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c /\ d /\ e ==> f <=>
                             c /\ d ==> a /\ b /\ e ==> f`]
       HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT)) THEN
   DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[GSYM RE_DEF] THEN
   ANTS_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
     REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
     REWRITE_TAC[real_div; GSYM REAL_POW_INV; REAL_POW_MUL; REAL_INV_MUL] THEN
     MATCH_MP_TAC(REAL_ARITH
      `&0 <= (M * R) * (b - i) ==> (&2 * M * R) * i <= &2 * M * R * b`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_POW_LE; REAL_LE_INV_EQ;
                  REAL_LT_IMP_LE] THEN
     ASM_REWRITE_TAC[REAL_POW_INV]] THEN
   REWRITE_TAC[DIMINDEX_2; ARITH] THEN
   REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   REWRITE_TAC[COMPLEX_NORM_MUL] THEN
   ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                CPOW_REAL_REAL; LT_NZ] THEN
   REWRITE_TAC[RE_MUL_II; RE_NEG; RE_II; RE_MUL_CX; RE_SUB; RE_CX; IM_CX] THEN
   REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; COMPLEX_SUB_RZERO;
               REAL_ARITH `&0 - d * x = --(d * x)`] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
    [GSYM CX_MUL; GSYM CX_INV; GSYM CX_POW; GSYM CX_DIV; RE_CX] THEN
   REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_RMUL_EQ;
                REAL_MUL_ASSOC] THEN
   GEN_REWRITE_TAC LAND_CONV
    [REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
   REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_MUL_LNEG] THEN
   ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_EXP_POS_LT] THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC[REAL_ARITH
    `&2 * M * r * d * x = M * (&2 * (d * x) * r)`] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; GSYM real_div] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
                 COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
     SUBGOAL_THEN `&0 <= d * x /\ d * x <= d * &1` MP_TAC THENL
      [ALL_TAC;
       MAP_EVERY UNDISCH_TAC [`&0 < d`; `d <= R`] THEN REAL_ARITH_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_LMUL_EQ];
     ALL_TAC] THEN
   MATCH_MP_TAC BOUND_LEMMA_2 THEN
   ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL] THEN
   REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
               COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
   UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC));;
```

### Informal statement
For any complex function `f` and complex sequence `a`, if the norm of each term `a(n)` in the sequence is less than or equal to 1 for all `n` greater than or equal to 1, if `f` is analytic on the set of complex numbers `z` whose real part is greater than or equal to 1, and if the series `sum_{n=1}^infty a(n) / n^z` converges to `f(z)` for all complex numbers `z` whose real part is strictly greater than 1, then the series `sum_{n=1}^infty a(n) / n^z` converges to `f(z)` for all complex numbers `z` whose real part is greater than or equal to 1. The convergence is understood in the sense of `sums` from 1.

### Informal sketch
The proof proceeds as follows:
- Start with rewriting using `real_ge`, `analytic_on`, and `IN_ELIM_THM`.
- Introduce a complex number `w` with `Re(w) >= 1`.
- Split into cases where `Re(w) > 1` or `Re(w) = 1`. If `Re(w) > 1`, the result follows directly.
- Assume `Re(w) = 1`. Let `e` be a real number greater than 0. Define `R = max(3/e, 1)`.
- Show that `0 < R`.
- Find a `d > 0` such that the function `g(z) = f(w + z)` is holomorphic on `{z | Re(z) >= -d /\ abs(Im(z)) <= R}`.  This is achieved by exploiting the fact that `f` is holomorphic on a ball around `w + z`, hence `f(w+z)` is holomorphic around `{z | Re(z) >= -d /\ abs(Im(z)) <= R}` for some `d > 0`. `min d R` is chosen.
- Use `COMPACT_INTERVAL` to derive compactness of the interval from `complex(0, --R)` to `complex(0, R)`.
- Use Heine-Borel theorem. Derive the existence of a `t` such that the `{w | abs(Re(z - w)) < bs z / 2 /\ abs(Im(z - w)) < bs z / 2}` cover `(interval[complex(0,--R),complex(0,R)])`, where the `bs` are radii of balls around each z.
- Define `g(z) = f(w + z)`. It is shown that `g` is complex differentiable within a certain radius using `COMPLEX_DIFFERENTIABLE_AT_WITHIN`.
- Find `M > 0` that bounds `norm(f(w + z))` when `Re(z) >= -d`, `abs(Im(z)) <= R`, and `Re(z) <= R` using `COMPACT_IMP_BOUNDED`.
- Apply an overall bound lemma (`OVERALL_BOUND_LEMMA`).
- Apply Newman's contour integral argument. Let `N` be a natural number such that `N0 <= N`.
- Define `S_N(w) = sum_{n=1}^N a(n) / n^w` and `r_N(w) = f(w) - S_N(w)`.
- Define a `partcirclepath` `A` with radius `R`. Verify `valid_path A`, and check starting/finishing point, and the real part of the winding number.
- Show that the image of `A` is a subset of `{z | Re(z) >= 0 /\ norm(z) = R}` and that the origin is not in the image of `A`.
- Define a path `B` composed of three line segments. Verify `valid_path B`, that the origin is not in the image of B, and that the real part of the winding number is positive. Compute starting/finishing points.
- Show that the image of `B` is a subset of `{z | -d <= Re(z) /\ Re(z) <= 0 /\ abs(Im(z)) <= R}`.
- Verify `valid_path(A ++ B)`, starting/finishing points. Show the origin is not in the image of `(A ++ B)`.
- Show that the winding number of `(A ++ B)` around the origin is 1.
- Apply Cauchy's integral formula to the function `f(w + z) * N^z * (1/z + z/R^2)` along the path `A ++ B`, obtaining an expression for `f(w)`.
- Let `A'` be the negation of `A`.
- Construct `valid_path(A ++ A')`, check the starting/finishing points. Show that the origin is not in the image of `(A ++ A')`.
- Show that the image of `A'` is a subset of `{z | Re(z) <= 0 /\ norm(z) = R}`.
- Show that the winding number of `(A ++ A')` around the origin is 1.
- Show that the function `S_N(w + z) * N^z * (1/z + z/R^2)` is holomorphic.
- Apply Cauchy's integral formula to the sum `S_N(w + z) * N^z * (1/z + z/R^2)` along the path `A ++ A'`, obtaining an expression for `S_N(w)`.
- Transform one of the path integrals along the path `A` and express it in terms of `S_N(w - z)`.
- Combine the above results to express `r_N(w)` (the error term) using path integrals.
- Bound the error term `r_N(w)` using appropriate integral bounds and lemmas (`HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG`, `HAS_PATH_INTEGRAL_BOUND_LINEPATH`, `PATH_INTEGRAL_PRIMITIVE`) using `OVERALL_BOUND_LEMMA` and other complex analysis inequalities.

### Mathematical insight
This theorem is a classical result in analytic number theory, extending the region of convergence of a Dirichlet series. The core idea of the proof involves using contour integration and careful estimates to bound the error term in the series approximation of the analytic function.

### Dependencies
**Definitions/Axioms:**
- `real_ge`
- `analytic_on`
- `IN_ELIM_THM`
- `sums`
- `LIM_SEQUENTIALLY`
- `HOLOMORPHIC_ON_SUBSET`
- `o_DEF`
- `HOLOMORPHIC_ON_COMPOSE`
- `HOLOMORPHIC_ON_ADD`
- `HOLOMORPHIC_ON_ID`
- `HOLOMORPHIC_ON_CONST`
- `EQ_IMP`
- `EXTENSION`
- `IN_BALL`
- `IN_IMAGE`
- `COMPLEX_RING`
- `UNWIND_THM1`
- `RIGHT_IMP_EXISTS_THM`
- `SKOLEM_THM`
- `COMPACT_INTERVAL`
- `COMPACT_EQ_HEINE_BOREL`
- `FORALL_IN_IMAGE`
- `OPEN_INTER`
- `OPEN_HALFSPACE_IM_GT`
- `OPEN_HALFSPACE_IM_LT`
- `OPEN_HALFSPACE_RE_GT`
- `OPEN_HALFSPACE_RE_LT`
- `COMPLEX_SUB_REFL`
- `COMPLEX_NORM_0`
- `IN_ELIM_THM`
- `RE_CX`
- `IM_CX`
- `REAL_ABS_NUM`
- `IN_INTERVAL`
- `DIMINDEX_2`
- `FORALL_2`
- `RE_DEF`
- `IM_DEF`
- `RE`
- `IM`
- `REAL_HALF`
- `FINITE_SUBSET_IMAGE`
- `RIGHT_AND_EXISTS_THM`
- `SWAP_EXISTS_THM`
- `UNWIND_THM2`
- `MEMBER_NOT_EMPTY`
- `IMAGE_EQ_EMPTY`
- `HOLOMORPHIC_ON_DIFFERENTIABLE`
- `COMPLEX_DIFFERENTIABLE_AT_WITHIN`
- `HOLOMORPHIC_ON_OPEN`
- `complex_differentiable`
- `OPEN_BALL`
- `CENTRE_IN_BALL`
- `IN_UNIONS`
- `EXISTS_IN_IMAGE`
- `dist`
- `complex_norm`
- `POW_2_SQRT_ABS`
- `SQRT_MONO_LT`
- `REAL_LE_SQUARE_ABS`
- `REAL_LT_MUL`
- `NORM_NEG`
- `COMPACT_IMP_BOUNDED`
- `BOUNDED_POS`
- `CONTINUOUS_ON_SUBSET`
- `COMPACT_EQ_BOUNDED_CLOSED`
- `BOUNDED_SUBSET`
- `BOUNDED_CBALL`
- `SUBSET`
- `IN_CBALL`
- `COMPLEX_SUB_LZERO`
- `REAL_BOUNDS_LE`
- `CLOSED_INTER`
- `CLOSED_HALFSPACE_RE_LE`
- `CLOSED_HALFSPACE_IM_LE`
- `CLOSED_HALFSPACE_RE_GE`
- `CLOSED_HALFSPACE_IM_GE`
- `OVERALL_BOUND_LEMMA`
- `PI_POS`
- `FROM_INTER_NUMSEG`
- `dist`
- `NORM_SUB`
- `partcirclepath`
- `VALID_PATH_PARTCIRCLEPATH`
- `PATHSTART_PARTCIRCLEPATH`
- `PATHFINISH_PARTCIRCLEPATH`
- `CEXP_EULER`
- `SIN_NEG`
- `COS_NEG`
- `SIN_PI2`
- `COS_PI2`
- `CX_SIN`
- `CX_COS`
- `COMPLEX_ADD_LID`
- `COMPLEX_MUL_RID`
- `COMPLEX_EQ`
- `RE_MUL_CX`
- `RE_II`
- `IM_II`
- `IM_MUL_CX`
- `WINDING_NUMBER_PARTCIRCLEPATH_POS_LT`
- `COMPLEX_NORM_0`
- `COMPLEX_SUB_REFL`
- `linepath`
- `WINDING_NUMBER_JOIN_POS_COMBINED`
- `PATHSTART_JOIN`
- `PATHFINISH_JOIN`
- `PATHSTART_LINEPATH`
- `PATHFINISH_LINEPATH`
- `VALID_PATH_LINEPATH`
- `WINDING_NUMBER_LINEPATH_POS_LT`
- `complex_mul`
- `RE_SUB`
- `RE_CNJ`
- `IM_SUB`
- `IM_CNJ`
- `PATH_IMAGE_LINEPATH`
- `segment`
- `REAL_NEG_EQ_0`
- `REAL_LT_IMP_NZ`
- `CONVEX_INTER`
- `CONVEX_HALFSPACE_RE_GE`
- `CONVEX_HALFSPACE_IM_GE`
- `CONVEX_HALFSPACE_RE_LE`
- `CONVEX_HALFSPACE_IM_LE`
- `SEGMENT_CONVEX_HULL`
- `HULL_MINIMAL`
- `NOT_IN_EMPTY`
- `VALID_PATH_JOIN`
- `PATH_IMAGE_JOIN`
- `winding_number`
- `WINDING_NUMBER_EQ_1`
- `WINDING_NUMBER_LT_1`
- `HAS_PATH_INTEGRAL_CONVEX_SIMPLE`
- `CPOW_N`
- `complex_div`
- `complex_pow`
- `HAS_PATH_INTEGRAL_EQ`
- `IN_POW`
- `HAS_PATH_INTEGRAL`
- `pathToIntegral`
- `COMPLEX_ADD_SYM`
- `HAS_PATH_INTEGRAL_UNIQUE`
- `HAS_PATH_INTEGRAL_NEGATEPATH`
- `HAS_PATH_INTEGRAL_NEG`
- `path_integrable_on`
- `PATH_INTEGRABLE_SUB`
- `NUM_GT_O`
- `PATH_INTEGRABLE_UNIQUE`
- `HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG`
- `HAS_PATH_INTEGRAL_BOUND_LINEPATH`
- `PATH_INTEGRAL_PRIMITIVE`
- `NORM_EQ_SQUARE`
- `DOT_SQUARE_NORM`
- `COMPLEX_SQNORM`
- `HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT`
- `ONTO`
- `VECTOR_DERIVATIVE_LINEPATH_AT`
- `HAS_INTEGRAL_AFFINITY`
- `pathToIntegral`

**Theorems:**
- `REAL_ARITH`
- `MONO_EXISTS`
- `REWRITE_RULE`
- `MESON`
- `SET_RULE`
- `TAUT`
- `COMPLEX_DIFFERENTIABLE_AT_WITHIN`
- `HOLOMORPHIC_ON_IMP_CONTINUOUS_ON`
-  `CONTINUOUS_ON_SUBSET`
- `COMPLEX_NORM_GE_RE_IM`
- `LOG_POS_LT`
- `REAL_LT_ADD`
- `WINDING_NUMBER_LT_1`
- `HOLOMORPHIC_ON_MUL`
- `HOLOMORPHIC_ON_POW`
- `NORM_ARITH`
- `BOUND_LEMMA_1`
- `LIM_NORM_UBOUND`
- `LIM_SUB`
- `LIM_CONST`
- `BOUND_LEMMA_4`
- `NUMSEG_COMBINE_R`
- `VSUM_UNION`
- `FINITE_NUMSEG`
- `BOUND_LEMMA_3`
- `FUN_EQ_THM`

### Porting notes (optional)
- The frequent use of `REAL_ARITH_TAC` and `ASM_ARITH_TAC` suggests reliance on a powerful linear arithmetic solver.
- This proof makes heavy use of complex analysis and calculus theorems. Ensure that the target proof assistant has suitable libraries and automation for dealing with holomorphic functions, path integrals, and complex arithmetic.
- The use of `MESON` indicates a significant amount of first-order reasoning. The target proof assistant should have a robust first-order tactic.
-  The many calls to `GSYM` and other rewriting tactics (`REWRITE_TAC`) indicate that the user employs a 'calculational' style of proving, where expressions are transformed step-by-step. A similar rewriting engine and tactic support would be useful to implement this in another system.
- Several custom lemmas (`OVERALL_BOUND_LEMMA`, `BOUND_LEMMA_*`) are used throughout the proof. If these are not available, they will need to be ported first.


---

## NEWMAN_INGHAM_THEOREM_BOUND

### Name of formal statement
NEWMAN_INGHAM_THEOREM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM_BOUND = prove
 (`!f a b. &0 < b /\
           (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:complex. inv(Cx(b)) * f z`;
                 `\n:num. inv(Cx(b)) * a n`]
                NEWMAN_INGHAM_THEOREM) THEN
  ASM_SIMP_TAC[ANALYTIC_ON_MUL; ANALYTIC_ON_CONST] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_SIMP_TAC[SERIES_COMPLEX_LMUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH `&0 < b ==> abs b = b`;
               REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `z:complex` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx b` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_RINV;
               CX_INJ; REAL_LT_IMP_NZ; COMPLEX_MUL_LID]);;
```

### Informal statement
For all complex functions `f`, number sequences `a`, and real numbers `b`, if `0 < b`, and for all natural numbers `n`, if `1 <= n` then the complex norm of `a(n)` is less than or equal to `b`, and `f` is analytic on the set of complex numbers `z` such that the real part of `z` is greater than or equal to `1`, and for all complex numbers `z`, if the real part of `z` is greater than `1`, then the series defined by `a(n) / (n^z)` sums to `f(z)` starting from `n = 1`, then for all complex numbers `z`, if the real part of `z` is greater than or equal to `1`, then the the series defined by `a(n) / (n^z)` sums to `f(z)` starting from `n = 1`.

### Informal sketch
The proof proceeds as follows:
- Generalize the variables `f`, `a`, and `b`.
- Assume the antecedent of the implication and aim to prove the consequent.
- Apply the `NEWMAN_INGHAM_THEOREM` with specialized arguments `inv(Cx(b)) * f z` and `inv(Cx(b)) * a n`.
- Simplify the goal and assumptions using properties of analytic functions (`ANALYTIC_ON_MUL`, `ANALYTIC_ON_CONST`).
- Rewrite using properties of complex division and multiplication (`complex_div`, `COMPLEX_MUL_ASSOC`).
- Simplify using properties of series and scalar multiplication (`SERIES_COMPLEX_LMUL`).
- Rewrite using properties of complex norm, multiplication, and inverse (`COMPLEX_NORM_MUL`, `COMPLEX_NORM_INV`).
- Rewrite using properties of real division and symmetry of real multiplication (`REAL_MUL_SYM`, `real_div`).
- Simplify using properties of complex norm, coercion from real to complex (`COMPLEX_NORM_CX`, `REAL_ARITH`), real arithmetic (`REAL_LE_LDIV_EQ`, `REAL_MUL_LID`).
- Use monotonicity for all. Introduce `z:complex`
- Discharge and reintroduce the assumptions by matching against the conclusion.
- Discharge and specialize `SERIES_COMPLEX_LMUL` with `Cx b`, then simplify using basic properties of complex numbers such as `complex_div`, `COMPLEX_MUL_ASSOC`, `COMPLEX_MUL_RINV`, the injectivity of `Cx` (`CX_INJ`), properties of real numbers (`REAL_LT_IMP_NZ`), and the left identity of complex multiplication (`COMPLEX_MUL_LID`).

### Mathematical insight
The `NEWMAN_INGHAM_THEOREM_BOUND` theorem generalizes the `NEWMAN_INGHAM_THEOREM` such that instead of requiring that `|a_n| <= 1`, it allows `|a_n| <= b` for any positive real number `b`. This is achieved by a simple variable substitution, multiplying the function `f` and the sequence `a` by `inv(Cx(b))`.

### Dependencies
#### Theorems
- `NEWMAN_INGHAM_THEOREM`
#### Definitions & Theorems related to Analysis
- `ANALYTIC_ON_MUL`
- `ANALYTIC_ON_CONST`
- `SERIES_COMPLEX_LMUL`
#### Theorems related to Complex numbers
- `complex_div`
- `COMPLEX_MUL_ASSOC`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_INV`
- `COMPLEX_NORM_CX`
- `COMPLEX_MUL_RINV`
- `CX_INJ`
- `REAL_LT_IMP_NZ`
- `COMPLEX_MUL_LID`
#### Theorems related to Real numbers
- `REAL_DIV`
- `REAL_MUL_SYM`
- `REAL_LE_LDIV_EQ`
- `REAL_MUL_LID`

### Porting notes (optional)
- Porting this theorem relies on having a well-developed theory of complex numbers including complex analysis, norms, and series.
- The most significant step is the application of `NEWMAN_INGHAM_THEOREM` with the appropriate specializations.
- The simplification steps rely on properties of arithmetic, complex numbers, and real numbers. Ensure that these properties are available and that the simplifier can apply them effectively.



---

## NEWMAN_INGHAM_THEOREM_STRONG

### Name of formal statement
NEWMAN_INGHAM_THEOREM_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM_STRONG = prove
 (`!f a b. (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NEWMAN_INGHAM_THEOREM_BOUND THEN
  EXISTS_TAC `abs b + &1` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b + &1`]);;
```

### Informal statement
For all functions `f` from complex numbers to complex numbers, complex number sequences `a`, and real numbers `b`, if the absolute value of each term `a(n)` in the sequence `a` is bounded above by `b` for all natural numbers `n` greater than or equal to 1, the function `f` is analytic on the set of complex numbers `z` whose real part is greater than or equal to 1, and for all complex numbers `z` whose real part is strictly greater than 1, the series with terms `a(n) / n^z` (starting from `n = 1`) converges to `f(z)`, then for all complex numbers `z` whose real part is greater than or equal to 1, the series with terms `a(n) / n^z` (starting from `n = 1`) converges to `f(z)`.

### Informal sketch
The proof proceeds as follows:

- Start by generalizing and stripping the quantifiers.
- Apply `NEWMAN_INGHAM_THEOREM_BOUND`. This likely reduces the conclusion to proving that `f` is analytic at `1 + i*y` and requires a suitable bound.
- Provide the existential witness `abs b + &1` to satisfy the assumptions of `NEWMAN_INGHAM_THEOREM_BOUND`.
- Rewrite using assumptions.
- Split the goal into two subgoals using `CONJ_TAC`.
- Solve real arithmetic related subgoal with `REAL_ARITH_TAC` and trivially discharge the right subgoal with `ALL_TAC`.
- Finally, use `ASM_MESON_TAC` with a real arithmetic fact to discharge the final goal.

### Mathematical insight
This theorem extends the region of convergence of a Dirichlet series. It essentially states that if a Dirichlet series converges for `Re(z) > 1` and its coefficients are bounded, and the function it converges to is analytic on `Re(z) >= 1`, then the series converges on the larger region `Re(z) >= 1`. This is a strong version of the Newman-Ingham theorem. The Newman-Ingham theorem, in general, gives conditions under which the non-vanishing of a certain function on the line `Re(s) = 1` implies the prime number theorem.

### Dependencies
Theorems:
- `NEWMAN_INGHAM_THEOREM_BOUND`

Real Arithmetic:
- `x <= b ==> x <= abs b + &1`


---

## GENZETA_BOUND_LEMMA

### Name of formal statement
GENZETA_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_BOUND_LEMMA = prove
 (`!n s m. ~(n = 0) /\ &1 < Re s /\ n + 1 <= m
           ==> sum(n..m) (\x. norm(Cx(&1) / Cx(&x) cpow s))
                <= (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; MATCH_MP (ARITH_RULE `n + 1 <= m ==> n <= m`)
              (ASSUME `n + 1 <= m`)] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= a - x ==> x + y <= a`) THEN
  MP_TAC(SPECL
   [`\z. Cx(&1) / z cpow (Cx(Re s))`;
    `\z. Cx(&1) / ((Cx(&1) - (Cx(Re s))) * z cpow (Cx(Re s) - Cx(&1)))`;
    `n + 1`; `m:num`] SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(n + &1) - &1 = n`] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN COMPLEX_DIFF_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
      STRIP_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM LT_NZ]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
       [ASM_MESON_TAC[RE_CX; REAL_LT_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[CPOW_N; CPOW_SUB; COMPLEX_POW_1] THEN
      REWRITE_TAC[COMPLEX_ENTIRE; complex_div] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
        ASM_REWRITE_TAC[COMPLEX_INV_EQ_0; CPOW_EQ_0; COMPLEX_SUB_0] THEN
        REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < x /\ &0 < y` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT; GSYM LT_NZ]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; GSYM CX_DIV] THEN
    SIMP_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= s * (y - x) ==> --(s * y) <= --(s * x)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> x <= a ==> y <= b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_DIV; RE_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[RE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x /\ --y <= e ==> x - y <= e`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX; COMPLEX_NORM_DIV;
               REAL_OF_NUM_LT; NORM_CPOW_REAL; LT_NZ] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_INV_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_EXP_POS_LE; REAL_SUB_LE;
               REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_INV_MUL; GSYM REAL_EXP_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= n * e ==> i * e <= (n + i) * e - x`) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_EXP_POS_LT;
   REAL_FIELD `&0 < x /\ &0 < z ==> inv(x) * x / z = inv(z)`] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL]);;
```

### Informal statement
For all natural numbers `n`, real numbers `s`, and natural numbers `m`, if `n` is not equal to 0, `1 < Re s` (where `Re s` denotes the real part of `s`), and `n + 1 <= m`, then the sum from `n` to `m` of the absolute value of `Cx(1) / Cx(x)` raised to the power of `s` is less than or equal to `(1 / n + 1 / (Re s - 1)) * exp((1 - Re s) * log(n))`.

### Informal sketch
The proof aims to establish an upper bound for the sum of a complex-valued expression.
- The proof starts by simplifying the sum using `SUM_CLAUSES_LEFT` rule and by using the hypothesis `n + 1 <= m` to infer that `n <= m`
- It uses `SUM_INTEGRAL_UBOUND_DECREASING` to bound the sum by an integral. This lemma requires showing that the function being summed is decreasing in absolute value. This step introduces several subgoals related to the properties of complex numbers and real functions.
  - First, it's shown that `Cx(&1) / z cpow (Cx(Re s))` is differentiable, where `z` is a complex number.
  - Second, it is shown that `\z. Cx(&1) / ((Cx(&1) - (Cx(Re s))) * z cpow (Cx(Re s) - Cx(&1)))` is decreasing. This involves demonstrating that its derivative is non-positive.
  - Then complex number `z` is assumed to be complex and it is shown via `COMPLEX_DIFF_TAC` that it is differentiable if the real part of `z` is positive and `z` isn't zero.
  - Then, by splitting into real numbers `x` and `y` it is demonstrated that if `0 < x /\ 0 < y` then `norm(Cx(&1) / Cx(x) cpow (Re s)) <= norm(Cx(&1) / Cx(y) cpow (Re s))` implies that `--Re s * x <= --Re s * y`
- After bounding the sum with an integral, the proof simplifies the result and uses properties of real numbers (exponential, logarithm) to arrive at the final inequality.

### Mathematical insight
The theorem provides an upper bound for a finite sum of complex numbers, which is related to the generalized zeta function. The bound is expressed in terms of `n`, `s`, and `m`, where `n` and `m` define the summation range, and `s` is a complex variable. This inequality is crucial for analyzing convergence properties and estimating values of the generalized zeta function.

### Dependencies
* Theorems:
    * `SUM_CLAUSES_LEFT`
    * `SUM_INTEGRAL_UBOUND_DECREASING`
    * `SUM_EQ_NUMSEG`
* Definitions:
    * `norm`
    * `Cx`
    * `cpow`
    * `Re`
    * `exp`
    * `log`

### Porting notes (optional)
- The `SUM_INTEGRAL_UBOUND_DECREASING` theorem is a key dependency and may require a significant porting effort if it's not available.
- Complex analysis related tactics (`COMPLEX_DIFF_TAC`, `COMPLEX_FIELD`) might need to be replaced by equivalent tactics or manual proof steps in other proof assistants.
- The real number arithmetic reasoning (`REAL_ARITH`) relies on a decision procedure and might need adjustments for different systems.


---

## GENZETA_BOUND

### Name of formal statement
GENZETA_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &1 < Re s
         ==> norm(genzeta n s) <=
                (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. vsum(n..m) (\r. Cx(&1) / Cx(&r) cpow s)` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP GENZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[GENZETA_BOUND_LEMMA]);;
```
### Informal statement
For all natural numbers `n` and complex numbers `s`, if `n` is not equal to 0 and the real part of `s` is greater than 1, then the norm of `genzeta n s` is less than or equal to `(1 / n + 1 / (Re s - 1)) * exp((1 - Re s) * log(n))`.

### Informal sketch
The proof demonstrates an upper bound for the norm of the generalized zeta function `genzeta n s`.

- The proof begins by stripping the assumptions and applying `LIM_NORM_UBOUND` which provides a bound on the norm of a limit, given a condition on the norm of the sequence. It relies on showing that the infinite sum defining `genzeta n s` converges sequentially.

- An intermediate step involves bounding a series using the `GENZETA_BOUND_LEMMA`, and some real arithmetic. The convergence of the series `genzeta n s` is established using `GENZETA_CONVERGES`. Simplification rules for handling sums, intervals in the natural numbers, and trivial limits sequentially are used.

- Rewriting with `EVENTUALLY_SEQUENTIALLY` is used to deal with limits. The norm of the finite sum which appears during the application of `LIM_NORM_UBOUND` is then bounded using `VSUM_NORM` and some rewriting.

### Mathematical insight
The theorem provides an explicit upper bound on the magnitude of `genzeta n s` in terms of `n` and the real part of `s`. This bound is useful for estimating the growth and behavior of `genzeta n s` in various regions of the complex plane.

### Dependencies
- `sums`
- `FROM_INTER_NUMSEG`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `FINITE_NUMSEG`
- `GENZETA_BOUND_LEMMA`
- `LIM_NORM_UBOUND`
- `GENZETA_CONVERGES`


---

## NEARZETA_BOUND_SHARP

### Name of formal statement
NEARZETA_BOUND_SHARP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_BOUND_SHARP = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s) <=
                  norm(s * (s - Cx(&1))) *
                  (&1 / &n + &1 / Re s) / exp(Re s * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
    `\m. vsum(n..m)
              (\r. (s - Cx(&1)) / Cx(&r) cpow s -
                   (Cx(&1) / Cx(&r) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(r + 1)) cpow (s - Cx(&1))))` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (n..m)
                (\r. norm(s * (s - Cx (&1)) / Cx(&r) cpow (s + Cx(&1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NEARZETA_BOUND_LEMMA THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a / b = a * Cx(&1) / b`] THEN
  REWRITE_TAC[SUM_LMUL; COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GENZETA_BOUND_LEMMA o lhand o snd) THEN
  ASM_REWRITE_TAC[RE_ADD; REAL_LT_ADDL; RE_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) - &1 = x`;
              REAL_ARITH `(&1 - (s + &1)) * x = --(s * x)`] THEN
  REWRITE_TAC[real_div; REAL_EXP_NEG; REAL_LE_REFL]);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if `n` is not equal to 0 and the real part of `s` is greater than 0, then the norm of `nearzeta n s` is less than or equal to the norm of `s * (s - 1)` * (`1 / n + 1 / Re s`) / exp(`Re s` * log(`n`)).

### Informal sketch
The proof establishes an upper bound for the norm of the nearzeta function.
- First, we use `LIM_NORM_UBOUND` to relate the norm of `nearzeta n s` to the norm of a certain infinite sum, exploiting the fact that `nearzeta n s` is defined as a limit of a sum.
- An explicit expression for the summands is introduced using an existential instantiation.
- The convergence of `nearzeta n s` is established from `NEARZETA_CONVERGES`.
- Various simplifications are performed involving sums, including using `sums`, `FROM_INTER_NUMSEG`, and `TRIVIAL_LIMIT_SEQUENTIALLY`. Rewriting with `EVENTUALLY_SEQUENTIALLY` is performed to deal with the limit more explicitly.
- An existential instantiation introduces `n + 1` as a witness, and `m` is generalized. We then use arithmetic properties.
- Several rewrite steps using lemmas like `VSUM_NORM`, and `FINITE_NUMSEG`, and real arithmetic are applied to further simplify the expression.
- The proof proceeds by splitting the goal into two subgoals using `CONJ_TAC`.
- One subgoal uses `SUM_LE_NUMSEG`, `NEARZETA_BOUND_LEMMA`, and arithmetic reasoning.
- The other subgoal uses properties of complex and real arithmetic, along with lemmas like `GENZETA_BOUND_LEMMA`, combined with real arithmetic and rewriting rules such as `REAL_EXP_NEG`, to reach the desired inequality.

### Mathematical insight
This theorem provides a sharp upper bound for the `nearzeta` function, a variant of the Riemann zeta function. It is crucial for estimating the growth and behavior of `nearzeta` within a certain region of the complex plane, which is essential for analytic number theory. The bound is particularly useful when dealing with the asymptotics of `nearzeta`.

### Dependencies
- `sums`
- `FROM_INTER_NUMSEG`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `VSUM_NORM`
- `FINITE_NUMSEG`
- `REAL_LE_TRANS`
- `SUM_LE_NUMSEG`
- `NEARZETA_BOUND_LEMMA`
- `SIMPLE_COMPLEX_ARITH`
- `SUM_LMUL`
- `COMPLEX_NORM_MUL`
- `REAL_MUL_ASSOC`
- `NORM_POS_LE`
- `GENZETA_BOUND_LEMMA`
- `RE_ADD`
- `REAL_LT_ADDL`
- `RE_CX`
- `REAL_ARITH`
- `real_div`
- `REAL_EXP_NEG`
- `REAL_LE_REFL`
- `NEARZETA_CONVERGES`
- `LIM_NORM_UBOUND`


---

## NEARZETA_BOUND

### Name of formal statement
NEARZETA_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s)
                  <= ((norm(s) + &1) pow 3 / Re s) / exp (Re s * log (&n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NEARZETA_BOUND_SHARP) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_EXP_POS_LE; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_RING `(x pow 3):real = x * x * x`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(y) = b ==> norm(x - y) <= norm(x) + b`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a + y <= (x + &1) * y <=> a <= x * y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[REAL_INV_1; GSYM real_div; REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `s:complex` COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and complex numbers `s`, if `n` is not equal to 0 and the real part of `s` is greater than 0, then the norm of `nearzeta n s` is less than or equal to `((norm(s) + 1) pow 3 / Re s) / exp(Re s * log n)`.

### Informal sketch
The proof proceeds as follows:
- We are given the hypothesis `~(n = 0) /\ &0 < Re s`.
- We apply the sharp version of the nearzeta bound (`NEARZETA_BOUND_SHARP`).
- We use real arithmetic to manipulate the inequality, primarily focusing on isolating and bounding the terms involving `norm(s)` and `Re s`.
- We use inequalities about norms of complex numbers as well as real numbers (`COMPLEX_NORM_CX`).
- We use the norm arithmetic tactic `NORM_ARITH` to estimate `norm(x - y)`.
- We simplify by using `REAL_ARITH` to transform `a + y <= (x + &1) * y` into `a <= x * y`.
- We use `REAL_LE_TRANS` implying transitivity of inequality with an existential.
- We simplify using arithmetic rules (`ARITH`) and real number properties, and exponential and logarithm manipulations

### Mathematical insight
This theorem provides an upper bound for the norm of the `nearzeta` function in terms of the norm of the complex variable `s` and the natural number `n`. The bound is particularly useful in analytic number theory when dealing with estimations related to the Riemann zeta function and its variants, as `nearzeta` is related to the zeta function.

### Dependencies
- `NEARZETA_BOUND_SHARP`
- `real_div`, `REAL_MUL_ASSOC`, `REAL_LE_RMUL`, `REAL_LE_INV_EQ`, `REAL_EXP_POS_LE`, `REAL_MUL_LID`
- `REAL_RING`, `COMPLEX_NORM_MUL`, `REAL_LE_MUL2`, `REAL_LE_MUL`, `NORM_POS_LE`, `REAL_LE_ADD`, `REAL_POS`, `REAL_LT_IMP_LE`
- `NORM_ARITH`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `REAL_LE_TRANS`, `REAL_LE_INV2`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, `ARITH`, `REAL_INV_1`, `real_div`
- `COMPLEX_NORM_GE_RE_IM`

### Porting notes (optional)
- The proof relies heavily on real and complex analysis libraries. Ensure the target proof assistant has equivalent theories and tactics.
- Automation using arithmetic simplification (`REAL_ARITH_TAC`) is crucial. The porter needs to use similar automation in the target proof assistant.
- The tactic `ASM_SIMP_TAC` which simplifies using assumptions, requires some thought to reproduce faithfully in other systems.


---

## NEARNEWMAN_EXISTS

### Name of formal statement
NEARNEWMAN_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARNEWMAN_EXISTS = prove
 (`?f. !s. s IN {s | Re(s) > &1 / &2}
           ==> ((\p. clog(Cx(&p)) / Cx(&p) * nearzeta p s -
                     clog(Cx(&p)) / (Cx(&p) cpow s * (Cx(&p) cpow s - Cx(&1))))
                sums (f s)) {p | prime p} /\
               f complex_differentiable (at s)`,
  MATCH_MP_TAC SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_NEARZETA THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC];
      ALL_TAC] THEN
    COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ;
                 COMPLEX_SUB_0; PRIME_IMP_NZ; PRIME_GE_2; CPOW_NUM_NE_1;
                 REAL_ARITH `&1 / &2 < x ==> &0 < x`];
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &2) ((Re s - &1 / &2) / &2)` THEN
  EXISTS_TAC `\p. Cx(&2 * (norm(s:complex) + &2) pow 3 + &2) *
                  clog(Cx(&p)) /
                  Cx(&p) cpow (Cx(&1 + (Re s - &1 / &2) / &4))` THEN
  EXISTS_TAC `5` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[IN_FROM; SUBSET; IN_ELIM_THM; GSYM CX_LOG; CPOW_REAL_REAL;
             RE_CX; REAL_CX; REAL_OF_NUM_LT; LE_1; PRIME_IMP_NZ] THEN
    SIMP_TAC[GSYM CX_DIV; REAL_CX; RE_CX; LOG_POS; REAL_OF_NUM_LE;
             REAL_LE_DIV; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC
     `--(complex_derivative zeta (Cx(&1 + (Re s - &1 / &2) / &4)))` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC SERIES_NEG THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num` THENL
   [SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; GSYM CX_LOG; REAL_OF_NUM_LT;
             LT_NZ; PRIME_IMP_NZ; GSYM CX_DIV; GSYM CX_MUL] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &2`) THEN
      MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                   PRIME_GE_2]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_BALL; REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= a * b /\ a * b <= abs a * b ==> x <= abs a * b`) THEN
  SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; REAL_ABS_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= a /\ norm(y) <= b ==> norm(x - y) <= a + b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; CX_ADD; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ; GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV] THEN
    REWRITE_TAC[COMPLEX_POW_1; real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * a * b:real = a * x * b`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND o lhand o snd) THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y = x * &2 * y`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_LT_IMP_LE; REAL_POS; REAL_LE_ADD; GSYM REAL_INV_MUL;
                 REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_NORM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_IMP_NZ;
                 LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                 PRIME_GE_2] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y:complex. norm(x) <= &2 * norm(y) /\ norm(y) <= a
                ==> norm(x) <= &2 * a`) THEN
  EXISTS_TAC `clog(Cx(&p)) / Cx(&p) cpow (z + z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; complex_div; COMPLEX_MUL_ASSOC; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_ARITH `&0 < x * inv(&2) <=> &0 < x`; COMPLEX_NORM_NZ] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
                 COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(NORM_ARITH
     `&2 <= norm(a) /\ norm(b) = &1 ==> norm(a) * inv(&2) <= norm(a - b)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 0 < p`] THEN
    SUBST1_TAC(SYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &2`))) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / &2 * log(&4)` THEN
    SIMP_TAC[REAL_ARITH `l <= &1 / &2 * x <=> &2 * l <= x`;
             GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; ARITH;
                 LOG_MONO_LE_IMP; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 4 <= p`] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               ARITH_RULE `5 <= p ==> 0 < p`] THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
               PRIME_GE_2] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_ADD] THEN ASM_REAL_ARITH_TAC);;
```
### Informal statement
There exists a function `f` such that for all complex numbers `s` whose real part is greater than 1/2, the function that maps each prime number `p` to `clog(Cx(p)) / Cx(p) * nearzeta p s - clog(Cx(p)) / (Cx(p) cpow s * (Cx(p) cpow s - Cx(1)))` sums to `f s` over all primes `p`, and the function `f` is complex differentiable at `s`.

### Informal sketch
The proof shows the existence of a complex differentiable function `f` which is the sum of a series indexed by prime numbers. The series involves the `nearzeta` function.
- It starts by using the `SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX` theorem and rewriting using `OPEN_HALFSPACE_RE_GT`, `IN_ELIM_THM`, and `real_gt`.
- It then performs case splitting and demonstrates that the series is complex differentiable. This involves using theorems like `COMPLEX_DIFFERENTIABLE_SUB`, `COMPLEX_DIFFERENTIABLE_MUL_AT`, and `COMPLEX_DIFFERENTIABLE_NEARZETA`. It uses `PRIME_IMP_NZ` to show that primes are nonzero, and uses several simplifications involving complex and real arithmetic and properties of the complex exponential function.
- The proof then introduces existential variables, and shows that the series sums to the function by proving that the series is summable.
- The proof proceeds by showing that the series of terms `clog(Cx(&p)) / Cx(&p) cpow (Cx(&1 + (Re s - &1 / &2) / &4))` converges.
- It uses `SUMMABLE_COMPLEX_LMUL` and `SUMMABLE_SUBSET_COMPLEX`. Simplifications involve `CX_LOG`, `CPOW_REAL_REAL`, `RE_CX`, `REAL_CX`, `REAL_OF_NUM_LT`, `LE_1`, `PRIME_IMP_NZ`, `CX_DIV`. Further simplfications use `LOG_POS` and `REAL_LE_DIV`. It uses that the complex derivative of the zeta function converges and `SERIES_NEG`.
- It then shows that `norm(clog(Cx(&p)) / Cx(&p) cpow z)` is less than or equal to `Cx(&2 * (norm(z:complex) + &2) pow 3 + &2)`. Uses `REAL_LE_MUL`, `REAL_POW_LE`, `REAL_LE_DIV`, `REAL_EXP_POS_LE`, `REAL_ARITH`, `PRIME_GE_2`.
- It proves that if `z` is close to `s` then summing over the series `clog(Cx(&p)) / Cx(&p) cpow (z + z)` will be close to `f z`. This part of the proof uses `IN_BALL`, `REAL_LT_MIN`, `dist`, `COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `REAL_ARITH`, `REAL_LE_RMUL`, `NORM_POS_LE`, `REAL_ABS_LE`, `REAL_ADD_RDISTRIB`, `NORM_ARITH`, `CPOW_ADD`, `CX_ADD`, `CPOW_N`, `CX_INJ`, `REAL_OF_NUM_EQ`, `complex_div`, `COMPLEX_INV_MUL`, `COMPLEX_MUL_ASSOC`, `complex_div`, `COMPLEX_NORM_DIV`, `REAL_MUL_SYM`, `COMPLEX_NORM_NZ`, `COMPLEX_NORM_GE_RE_IM`, `REAL_LE_LMUL2`, `NORM_POS_LE`, `REAL_POW_LE`, `REAL_LE_INV_EQ`, `REAL_LE_MUL`, `REAL_LT_IMP_LE`, `REAL_POS`, `REAL_LE_ADD`, `REAL_INV_MUL`, `REAL_EXP_POS_LE`, `REAL_POW_LE2`, `REAL_INV_INV`, `NORM_CPOW_REAL`, `REAL_CX`, `RE_CX`, `REAL_OF_NUM_LT`, `LT_NZ`, `REAL_EXP_NEG`, `REAL_EXP_MONO_LE`, `LOG_POS`, `REAL_ARITH`, and `ARITH_RULE`.
### Mathematical insight
This theorem establishes the existence of a complex differentiable function that arises from summing a series involving the `nearzeta` function over prime numbers. The novelty of the nearzeta function is that, when summed, it interpolates back to the Riemann Zeta function. This kind of analytic continuation is important for calculating values of the zeta function, which is a central object of study in analytic number theory.

### Dependencies
#### Theorems
- `SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX`
- `IN_ELIM_THM`
- `PRIME_IMP_NZ`
- `COMPLEX_DIFFERENTIABLE_SUB`
- `COMPLEX_DIFFERENTIABLE_MUL_AT`
- `COMPLEX_DIFFERENTIABLE_NEARZETA`
- `SUMMABLE_COMPLEX_LMUL`
- `SUMMABLE_SUBSET_COMPLEX`
- `REAL_LE_MUL`
- `REAL_POW_LE`
- `REAL_LE_DIV`
- `REAL_EXP_POS_LE`
- `EXP_LOG`
- `REAL_LE_REFL`
- `REAL_LE_MUL2`
- `REAL_LE_DIV`
- `LOG_MONO_LE_IMP`
- `COMPLEX_NORM_GE_RE_IM`
- `REAL_LE_RMUL`
- `REAL_LE_INV2`
- `NEARZETA_BOUND`
- `EXP_LOG`
#### Definitions
- `nearzeta`
- `primeset`
- `summable`
#### Other
- `COMPLEX_ENTIRE`
- `CPOW_EQ_0`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `COMPLEX_SUB_0`
- `PRIME_GE_2`
- `CPOW_NUM_NE_1`
- `dist`
- `IN_BALL`

### Porting notes (optional)
- The proof relies heavily on real and complex analysis. Ensure the target system has comparable libraries.
- HOL Light's `REAL_ARITH` tactic is powerful. You may need to manually discharge some real arithmetic goals in other systems.
- The `NEARZETA_BOUND` theorem will need to be ported, and the `nearzeta` definition.


---

## nearnewman

### Name of formal statement
nearnewman

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let nearnewman = new_specification ["nearnewman"] NEARNEWMAN_EXISTS;;
```
### Informal statement
Introduce a constant `nearnewman` such that there exists a relation `r` for which `nearnewman` is equal to the reflexive, transitive closure of `r`.

### Informal sketch
- The specification introduces a new constant, `nearnewman`, representing the reflexive transitive closure of some relation.
- The existence of this relation is guaranteed by `NEARNEWMAN_EXISTS`, not shown, which probably uses `tc_rule` and demonstrates that reflexive transitive closures always exist for any relation.

### Mathematical insight
The specification ensures the existence of an operator that computes the reflexive transitive closure of a relation. This is a standard construction in many areas of mathematics and computer science, used, for instance, in reachability analysis or in defining equivalence relations.

### Dependencies
**Constants**:
- `NEARNEWMAN_EXISTS`

### Porting notes (optional)
- Proof assistants often have built-in support for reflexive transitive closures, so the existence proof might be trivial. However, some systems require the explicit construction of the closure via inductive definitions or least fixed points. Verify that the target system's handling of closures aligns with HOL Light's approach (likely based on least fixed points).


---

## [CONVERGES_NEARNEWMAN;

### Name of formal statement
`CONVERGES_NEARNEWMAN`

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let [CONVERGES_NEARNEWMAN; COMPLEX_DIFFERENTIABLE_NEARNEWMAN] =
  CONJUNCTS(REWRITE_RULE[FORALL_AND_THM; IN_ELIM_THM; real_gt;
                         TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                nearnewman);;
```

### Informal statement
The theorem `nearnewman` is split into two theorems: `CONVERGES_NEARNEWMAN` and `COMPLEX_DIFFERENTIABLE_NEARNEWMAN`.

### Informal sketch
The theorem `nearnewman` is rewritten using `FORALL_AND_THM`, `IN_ELIM_THM`, `real_gt` and `TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)``. The resulting conjunction is then split into two separate theorems called `CONVERGES_NEARNEWMAN` and `COMPLEX_DIFFERENTIABLE_NEARNEWMAN`.

### Mathematical insight
This step prepares `nearnewman` to be used in two different ways. This is a common step to split complex theorems for clarity and modularity.

### Dependencies
- Theorem: `nearnewman`
- Theorem: `FORALL_AND_THM`
- Theorem: `IN_ELIM_THM`
- Theorem: `real_gt`
- Tautology: `TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)``


---

## newman

### Name of formal statement
newman

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let newman = new_definition
 `newman(s) = (nearnewman(s) - (complex_derivative zeta s / zeta s)) /
              (s - Cx(&1))`;;
```
### Informal statement
The function `newman` of a complex number `s` is defined as the complex number resulting from the following expression:
`(nearnewman(s) - (complex_derivative zeta s / zeta s)) / (s - Cx(&1))`.

### Informal sketch
The definition introduces the `newman` function, which appears to be related to the Riemann zeta function and its properties. The function `newman(s)` involves the `nearnewman` function at `s`, subtracts the ratio of the complex derivative of the `zeta` function at `s` to the value of the `zeta` function at `s`, and divides the result by `(s - Cx(&1))`, where `Cx(&1)` represents the complex number 1 + 0i.

### Mathematical insight
The definition of the `newman` function likely plays a role in the study of the Riemann zeta function, potentially related to the Riemann Hypothesis or other analytic properties. The subtraction within the numerator, involving a derivative and division by the zeta function itself suggest logarithmic differentiation and meromorphic properties, while division by `(s - Cx(&1))` suggests a residue calculation or analytic continuation. The `nearnewman` function provides an approximation or some adjustment to the expression involving the Riemann `zeta` function, `complex_derivative` of the `zeta` function, and the number 1.

### Dependencies
- Definition: `nearnewman`
- Definition: `zeta`
- Definition: `complex_derivative`
- Definition: `Cx`


---

## COMPLEX_DERIVATIVE_ZETA

### Name of formal statement
COMPLEX_DERIVATIVE_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> complex_derivative zeta s =
                complex_derivative (nearzeta 1) s / (s - Cx(&1)) -
                (nearzeta 1 s + Cx(&1)) / (s - Cx(&1)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL zeta);
              REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL genzeta)] THEN
  REWRITE_TAC[CPOW_1; complex_div; COMPLEX_MUL_LID; COMPLEX_INV_1] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (nearzeta 1 s + Cx(&1)) * inv(s - Cx(&1))` THEN
  EXISTS_TAC `dist(Cx(&1),s)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`\z. nearzeta 1 z + Cx(&1)`; `complex_derivative(nearzeta 1) s`;
    `\z. inv(z - Cx(&1))`;
    `--Cx(&1) / (s - Cx(&1)) pow 2`;
    `s:complex`]
   HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_COMPLEX_ARITH_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    COMPLEX_DIFF_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
    CONV_TAC COMPLEX_FIELD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; ETA_AX] THEN
  MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
  SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM complex_differentiable; real_gt]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 0 and `s` is not equal to the complex number `1 + 0i` (i.e., `Cx(&1)`), then the complex derivative of the Riemann zeta function `zeta` at `s` is equal to the complex derivative of the function `nearzeta 1` at `s` divided by `s - Cx(&1)` minus `(nearzeta 1 s` + `Cx(&1)) / (s - Cx(&1))` raised to the power of 2.

### Informal sketch
The proof demonstrates the complex differentiability of the Riemann zeta function, `zeta`, away from its pole at 1. It establishes a formula for the derivative in terms of the `nearzeta 1` function. The main steps are:

- Start by stripping the goal and applying `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`.  This gives a differentiability goal and a derivative goal.
- Rewrite using the definitions of `zeta` and `genzeta` which expresses `zeta s` as `nearzeta 1 s + 1 / (s-1)`.
- Simplify using complex arithmetic `CPOW_1`, `complex_div`, `COMPLEX_MUL_LID`, `COMPLEX_INV_1`.
- Apply `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`. This requires exhibiting a suitable function whose derivative matches the expression.

- Instantiate `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` with the function `\s. (nearzeta 1 s + Cx(&1)) * inv(s - Cx(&1))`.
- Provide a delta for the differentiability `dist(Cx(&1),s)` and simplify using `DIST_POS_LT`.
- Prove the differentiability of the components `nearzeta 1 s+ Cx(&1)` and `inv(s - Cx(&1))`.
    - Differentiability of `nearzeta 1 s+ Cx(&1)` is handled using `HAS_COMPLEX_DERIVATIVE_MUL_AT` and `EQ_IMP`.
    - To prove differentiability use `COMPLEX_DIFF_TAC` and `COMPLEX_FIELD`.
- Reduce the conclusion using `COMPLEX_ADD_RID`, `HAS_COMPLEX_DERIVATIVE_ADD`, `HAS_COMPLEX_DERIVATIVE_CONST`, `HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE`, `HOLOMORPHIC_NEARZETA`, `HOLOMORPHIC_ON_OPEN`, `OPEN_HALFSPACE_RE_GT`, `IN_ELIM_THM`, `complex_differentiable`, `real_gt`.

### Mathematical insight
This theorem expresses the complex derivative of the Riemann zeta function `zeta` in terms of the `nearzeta 1` function. This is crucial because `nearzeta 1` is holomorphic on a larger domain than `zeta`, which allows us to compute the derivative of `zeta` even in a region near `s = 1`, where `zeta` has a pole. The formula reveals how the derivative behaves near the singularity.

### Dependencies
- `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`
- `CPOW_1`
- `complex_div`
- `COMPLEX_MUL_LID`
- `COMPLEX_INV_1`
- `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`
- `DIST_POS_LT`
- `HAS_COMPLEX_DERIVATIVE_MUL_AT`
- `EQ_IMP`
- `COMPLEX_FIELD`
- `COMPLEX_ADD_RID`
- `HAS_COMPLEX_DERIVATIVE_ADD`
- `HAS_COMPLEX_DERIVATIVE_CONST`
- `HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE`
- `HOLOMORPHIC_NEARZETA`
- `HOLOMORPHIC_ON_OPEN`
- `OPEN_HALFSPACE_RE_GT`
- `IN_ELIM_THM`
- `complex_differentiable`
- `real_gt`


---

## ANALYTIC_ZETA_DERIVDIFF

### Name of formal statement
ANALYTIC_ZETA_DERIVDIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANALYTIC_ZETA_DERIVDIFF = prove
 (`?a. (\z. if z = Cx(&1) then a
            else (z - Cx(&1)) * complex_derivative zeta z -
                 complex_derivative zeta z / zeta z)
       analytic_on {s | Re(s) >= &1}`,
  EXISTS_TAC
   `complex_derivative
     (\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
          ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
           (nearzeta 1 z + Cx(&1)))) (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
         ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
          (nearzeta 1 z + Cx(&1)))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; ARITH] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_INV_1; COMPLEX_SUB_REFL;
              COMPLEX_MUL_LZERO] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUB THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_INV THEN
      ASM_SIMP_TAC[IN_ELIM_THM; real_ge; NEARZETA_NONZERO] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX];
      MATCH_MP_TAC ANALYTIC_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC ANALYTIC_ON_MUL THEN
        SIMP_TAC[ETA_AX; ANALYTIC_ON_SUB; ANALYTIC_ON_CONST;
                 ANALYTIC_ON_ID] THEN MATCH_MP_TAC ANALYTIC_COMPLEX_DERIVATIVE;
        MATCH_MP_TAC ANALYTIC_ON_ADD THEN
        REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX]]] THEN
    MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
             HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
    DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEARZETA_NONZERO) THEN
    MP_TAC(ISPECL [`\z. nearzeta 1 z + Cx(&1)`; `z:complex`; `Cx(&0)`]
                CONTINUOUS_AT_AVOID) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; ETA_AX] THEN
      MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
      SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
      REWRITE_TAC[complex_differentiable; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    REWRITE_TAC[BALL_MIN_INTER; IN_INTER; IN_BALL; REAL_LT_MIN] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < Re w` ASSUME_TAC THENL
     [MP_TAC(SPEC `z - w:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM] zeta; genzeta] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD]);;
```

### Informal statement
There exists a complex number `a` such that the function, which maps a complex number `z` to `a` if `z` is equal to 1, and to `(z - 1) * complex_derivative(zeta, z) - complex_derivative(zeta, z) / zeta(z)` otherwise, is analytic on the set of complex numbers `s` such that the real part of `s` is greater than or equal to 1.

### Informal sketch
The proof demonstrates the existence of a value `a` that makes the given function analytic on the set `{s | Re(s) >= 1}`. The core idea is to use the `nearzeta` function, which is a modified version of the zeta function that is analytic around 1.

- First, the proof uses `POLE_THEOREM_ANALYTIC_0` to show that the derivative of `(Cx(&1) - inv(nearzeta 1 z + Cx(&1))) * ((z - Cx(&1)) * complex_derivative (nearzeta 1) z - (nearzeta 1 z + Cx(&1)))` is analytic at `Cx(&1)`.
- The proof constructs an auxiliary function based on `nearzeta` that is analytic in a neighborhood of 1. This involves proving the analyticity of each component and combining them using properties of analytic functions. Specifically, it leverages the facts that sums, differences, products, and inverses of analytic functions are analytic (where the inverse is defined).
- It proves that the constructed function is equal to a function which agrees with `(z - Cx(&1)) * complex_derivative (zeta z) - complex_derivative (zeta z) / zeta z` except possibly at `z = Cx(&1)`.
- The proof then establishes the analyticity of the function on the region `{s | Re(s) > 0}` using `HOLOMORPHIC_NEARZETA` and properties of analytic functions of halfspaces.
- Finally, it uses the fact that a continuous function is analytic if and only if it is complex differentiable, to extend analyticity to `{s | Re(s) >= 1}` and establishes the required continuity through the limit definition, leveraging continuity results such as `CONTINUOUS_AT_AVOID`.

### Mathematical insight
This theorem states that a singularity of `(z - 1) * zeta'(z) - zeta'(z) / zeta(z)` can be removed by assigning a value to the function at `z=1`. Analyticity is a key property for complex functions, allowing powerful results (e.g. Taylor series expansion) to hold.

### Dependencies
- `POLE_THEOREM_ANALYTIC_0`
- `NEARZETA_1`
- `ARITH`
- `COMPLEX_ADD_LID`
- `COMPLEX_INV_1`
- `COMPLEX_SUB_REFL`
- `COMPLEX_MUL_LZERO`
- `ANALYTIC_ON_MUL`
- `ANALYTIC_ON_SUB`
- `ANALYTIC_ON_CONST`
- `ANALYTIC_ON_INV`
- `IN_ELIM_THM`
- `real_ge`
- `NEARZETA_NONZERO`
- `ANALYTIC_ON_ADD`
- `ETA_AX`
- `ANALYTIC_ON_ID`
- `ANALYTIC_COMPLEX_DERIVATIVE`
- `ANALYTIC_ON_SUBSET`
- `SUBSET`
- `ANALYTIC_ON_OPEN`
- `OPEN_HALFSPACE_RE_GT`
- `HOLOMORPHIC_NEARZETA`
- `LE_REFL`
- `COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT`
- `COMPLEX_DIFFERENTIABLE_ADD`
- `COMPLEX_DIFFERENTIABLE_CONST`
- `HOLOMORPHIC_ON_OPEN`
- `complex_differentiable`
- `CONTINUOUS_AT_AVOID`
- `REAL_LT_MIN`
- `REAL_LT_01`
- `BALL_MIN_INTER`
- `IN_INTER`
- `IN_BALL`
- `COMPLEX_NORM_GE_RE_IM`
- `RE_SUB`
- `COMPLEX_DERIVATIVE_ZETA`
- `FUN_EQ_THM`
- `genzeta`
- `CPOW_1`
- `COMPLEX_DIV_1`


---

## ANALYTIC_NEWMAN_VARIANT

### Name of formal statement
ANALYTIC_NEWMAN_VARIANT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANALYTIC_NEWMAN_VARIANT = prove
 (`?c a. (\z. if z = Cx(&1) then a
              else newman z + complex_derivative zeta z + c * zeta z)
         analytic_on {s | Re(s) >= &1}`,
  X_CHOOSE_TAC `c:complex` ANALYTIC_ZETA_DERIVDIFF THEN
  EXISTS_TAC `--(c + nearnewman(Cx(&1)))` THEN
  EXISTS_TAC
   `complex_derivative
     (\z. nearnewman z +
          (if z = Cx(&1)
           then c
           else (z - Cx(&1)) * complex_derivative zeta z -
                complex_derivative zeta z / zeta z) +
           --(c + nearnewman (Cx(&1))) * (nearzeta 1 z + Cx(&1)))
     (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. nearnewman z +
         (if z = Cx(&1) then c
          else (z - Cx(&1)) * complex_derivative zeta z -
               complex_derivative zeta z / zeta z) +
          --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re(s) > &1 / &2}` THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_ON_OPEN; real_gt; GSYM complex_differentiable;
               COMPLEX_DIFFERENTIABLE_NEARNEWMAN] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ANALYTIC_ON_MUL THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN REWRITE_TAC[newman] THEN
    GEN_REWRITE_TAC (funpow 4 RAND_CONV o ONCE_DEPTH_CONV) [zeta] THEN
    ASM_REWRITE_TAC[genzeta; CPOW_1; COMPLEX_DIV_1] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
    SIMPLE_COMPLEX_ARITH_TAC]);;
```

### Informal statement
For any complex number `c` and any complex number `a`, the function that maps a complex number `z` to `a` if `z` equals `Cx(&1)` (the complex number corresponding to the real number 1), and to `newman z + complex_derivative zeta z + c * zeta z` otherwise, is analytic on the set of complex numbers `s` whose real part is greater than or equal to 1.

### Informal sketch
The proof demonstrates that a modified version of the `newman` function, when appropriately defined at `Cx(&1)`, is analytic for complex numbers with real part greater than or equal to 1.

- Choose an arbitrary complex number `c`.
- Instantiate an existential with `-- (c + nearnewman(Cx(&1)))`.
- Instantiate a second existential using the complex derivative of an expression involving `nearnewman`, `zeta`, and `c` at `Cx(&1)`.
- Apply `POLE_THEOREM_ANALYTIC_0` using `MATCH_MP_TAC` to leverage a previous result about the analyticity of zeta around its pole.
- Instantiate existentials with `nearnewman z + (if z = Cx(&1) then c else (z - Cx(&1)) * complex_derivative zeta z - complex_derivative zeta z / zeta z) + --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))` and `Cx(&1)`.
- Simplify using `NEARZETA_1` and `LE_REFL`.
- Split the proof goal via repeated application of `CONJ_TAC`.
  - The first subgoal is to show that `nearnewman z + (if z = Cx(&1) then c else (z - Cx(&1)) * complex_derivative zeta z - complex_derivative zeta z / zeta z) + --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))` is analytic on {s | Re(s) >= &1}. This is handled by:
    - Applying `ANALYTIC_ON_ADD`
    - Further splitting the goal with `CONJ_TAC`.
      - Showing that if `Re(s) > &1 / &2` then the expression is analytic using `ANALYTIC_ON_SUBSET`, `ANALYTIC_ON_OPEN`, `HOLOMORPHIC_ON_OPEN`, `COMPLEX_DIFFERENTIABLE_NEARNEWMAN` and `REAL_ARITH_TAC`.
      - Apply `ANALYTIC_ON_ADD`, `ANALYTIC_ON_MUL`, `ANALYTIC_ON_SUBSET` to show that the remaining part of the function is analytic on {s | Re(s) > &0} using facts about `HOLOMORPHIC_NEARZETA`.
  - The second subgoal is to show that `complex_derivative (nearnewman z + (if z = Cx(&1) then c else (z - Cx(&1)) * complex_derivative zeta z - complex_derivative zeta z / zeta z) + --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))) (Cx(&1)) = newman (Cx(&1)) + complex_derivative zeta (Cx(&1)) + c * zeta (Cx(&1))`.  This is handled by:
    - Introducing an arbitrary w, rewriting with `newman`, `zeta`, `genzeta`, `CPOW_1`, `COMPLEX_DIV_1`, and `COMPLEX_FIELD`.

### Mathematical insight
This theorem establishes the analyticity of a specifically constructed variant of the `newman` function. This variant is crucial for proving properties about the `newman` function in a region including the singularity of the `zeta` function.

### Dependencies
- `ANALYTIC_ZETA_DERIVDIFF`
- `POLE_THEOREM_ANALYTIC_0`
- `NEARZETA_1`
- `LE_REFL`
- `ANALYTIC_ON_ADD`
- `ANALYTIC_ON_SUBSET`
- `SUBSET`
- `IN_ELIM_THM`
- `ANALYTIC_ON_OPEN`
- `OPEN_HALFSPACE_RE_GT`
- `HOLOMORPHIC_ON_OPEN`
- `real_gt`
- `GSYM complex_differentiable`
- `COMPLEX_DIFFERENTIABLE_NEARNEWMAN`
- `ANALYTIC_ON_CONST`
- `ETA_AX`
- `HOLOMORPHIC_NEARZETA`
- `REAL_LT_01`
- `newman`
- `zeta`
- `genzeta`
- `CPOW_1`
- `COMPLEX_DIV_1`

### Porting notes (optional)
- The `analytic_on` predicate and associated theorems need to be defined/ported first.
- Special care is needed to handle the singularity of the `zeta` function and its derivative.
- The definitions of `nearnewman` and `nearzeta` must be ported, capturing their specific analytic properties and relation to the `newman` and `zeta` functions.


---

## CONVERGES_NEWMAN_PRIME

### Name of formal statement
CONVERGES_NEWMAN_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERGES_NEWMAN_PRIME = prove
 (`!s. &1 < Re s
       ==> ((\p. clog(Cx(&p)) / Cx(&p) * genzeta p s) sums newman(s))
           {p | prime p}`,
  X_GEN_TAC `s:complex` THEN ASM_CASES_TAC `s = Cx(&1)` THEN
  ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL; genzeta; newman] THEN
  DISCH_TAC THEN REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN REWRITE_TAC[GSYM complex_div] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_LOGZETA'') THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEARNEWMAN o MATCH_MP
   (REAL_ARITH `&1 < x ==> &1 / &2 < x`)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[GSYM complex_sub] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMS_IFF THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `c - b = a * m ==> (a:complex) * n - b + c = a * (n + m)`) THEN
  ASM_SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ; complex_div] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_SUB_LDISTRIB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_INV_MUL] THEN
  ASM_SIMP_TAC[CPOW_SUB; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ] THEN
  REWRITE_TAC[COMPLEX_POW_1] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(ps = Cx(&1)) /\ ~(ps = Cx(&1)) /\ ~(p = Cx(&0))
    ==> inv(ps - Cx(&1)) - inv(ps * (ps - Cx(&1))) =
        inv(p * ps / p)`) THEN
  ASM_SIMP_TAC[CPOW_NUM_NE_1; PRIME_GE_2; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the series whose general term is `clog(Cx(p)) / Cx(p) * genzeta p s`, where `p` ranges over all prime numbers, converges to `newman(s)`.

### Informal sketch
The proof proceeds as follows:
- Assume `&1 < Re s`.
- Perform a case split on `s = Cx(&1)`. If it holds, simplify using rewrites.
- Rewrite the goal using properties of complex division and associativity.
- Apply `SERIES_COMPLEX_RMUL` and rewrite using the inverse of complex division.
- Apply `CONVERGES_LOGZETA''` and `CONVERGES_NEARNEWMAN`. The latter requires application of `REAL_ARITH &1 < x ==> &1 / &2 < x`.
- Deduce that the complex subtraction series also converges using `SERIES_ADD`.
- Rewrite the goal by converting the `sums` relation to an `IFF`, introducing `p:num`.
- Eliminate the membership condition on the set of primes.
- Apply a complex ring equality reasoning tactic, simplify using various arithmetic and complex lemmas.
- Further simplify using properties of complex numbers, powers and related field-specific lemmas.

### Mathematical insight
This theorem expresses a relationship between the Newman function `newman(s)` and a series involving prime numbers. Specifically, it states that the Newman function can be represented as the sum of a convergent series involving the complex logarithm of primes and a generalized zeta function `genzeta`. This representation is valid for complex numbers `s` with a real part greater than 1. This is likely a key analytic result relating the distribution of prime numbers to complex analysis via the Newman function.

### Dependencies
- `RE_CX`
- `REAL_LT_REFL`
- `genzeta`
- `newman`
- `complex_div`
- `COMPLEX_MUL_ASSOC`
- `SERIES_COMPLEX_RMUL`
- `CONVERGES_LOGZETA''`
- `CONVERGES_NEARNEWMAN`
- `REAL_ARITH`
- `IMP_IMP`
- `SERIES_ADD`
- `complex_sub`
- `EQ_IMP`
- `SUMS_IFF`
- `IN_ELIM_THM`
- `COMPLEX_RING`
- `CX_LOG`
- `REAL_OF_NUM_LT`
- `LT_NZ`
- `PRIME_IMP_NZ`
- `complex_div`
- `COMPLEX_SUB_LDISTRIB`
- `COMPLEX_MUL_LID`
- `COMPLEX_INV_MUL`
- `CPOW_SUB`
- `CPOW_N`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `complex_sub`
- `COMPLEX_POW_1`
- `COMPLEX_FIELD`
- `CPOW_NUM_NE_1`
- `PRIME_GE_2`
- `CPOW_EQ_0`

### Porting notes (optional)
- The proof makes heavy use of rewriting with complex arithmetic lemmas. Ensure that the target proof assistant has similar lemmas available and that rewriting is performed efficiently.
- The `X_GEN_TAC` tactic is used to introduce quantifiers explicitly, and `ASM_CASES_TAC` for case splitting. Ensure alternatives are used to achieve similar effects.
- The properties applied by `COMPLEX_RING` and `COMPLEX_FIELD` may need to be stated explicitly in different provers.


---

## GENZETA_OFFSET

### Name of formal statement
GENZETA_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_OFFSET = prove
 (`!m n s. &1 < Re s /\ m <= n
           ==> genzeta m s - vsum(m..n) (\k. Cx(&1) / Cx(&k) cpow s) =
               genzeta (n + 1) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\k. Cx(&1) / Cx(&k) cpow s`; `from(n + 1)`] THEN
  ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  GEN_REWRITE_TAC (PAT_CONV `\n. (f sums (a - vsum(m..n) s)) k`)
   [ARITH_RULE `n = (n + 1) - 1`] THEN
  MATCH_MP_TAC SUMS_OFFSET THEN ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
For all real numbers `m`, `n`, and `s`, if 1 is strictly less than the real part of `s` and `m` is less than or equal to `n`, then `genzeta m s` minus the sum from `m` to `n` of the function that maps `k` to the complex number corresponding to 1 divided by the complex number corresponding to `k` raised to the power of `s`, is equal to `genzeta (n + 1) s`.

### Informal sketch
The proof demonstrates that a partial sum of the infinite series defining `genzeta m s` can be expressed as a difference between `genzeta m s` and `genzeta (n + 1) s`, where `n` is greater than or equal to `m`. It proceeds as follows:

- First, use `SERIES_UNIQUE` to show that the difference between `genzeta m s` and the partial sum is a convergent series.
- Next, make sure the function is applied to the necessary variables using `EXISTS_TAC`.
- Then, use `GENZETA_CONVERGES` to simplify the series.
- Rewrite the `f sums (a - vsum(m..n) s)` using `ARITH_RULE` to prepare it for using `SUMS_OFFSET`.
- Apply `SUMS_OFFSET` to manipulate the summation range.
- Finally, simplify the equation using `GENZETA_CONVERGES` and basic arithmetic.

### Mathematical insight
This theorem expresses the tail of the generalized zeta function's infinite series as a zeta function with a shifted index. In other words, it provides a way to compute the remainder of the series after a certain number of terms have been summed. This is useful in numerical computation and convergence analysis of the series.

### Dependencies
- `GENZETA_CONVERGES`
- `SUMS_OFFSET`


---

## NEWMAN_CONVERGES

### Name of formal statement
NEWMAN_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) /
                 Cx(&n) cpow s)
            sums (newman s)) (from 1)`,
  let lemma = prove
   (`vsum (1..n) (\m. vsum {p | prime p /\ p <= m} (\p. f p m)) =
     vsum {p | prime p /\ p <= n} (\p. vsum (p..n) (\m. f p m))`,
    SIMP_TAC[VSUM_VSUM_PRODUCT; FINITE_NUMSEG; FINITE_ATMOST] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    REPEAT(EXISTS_TAC `\(x:num,y:num). (y,x)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEWMAN_PRIME) THEN
  GEN_REWRITE_TAC LAND_CONV [sums] THEN
  SUBGOAL_THEN `!n. {p | prime p} INTER (0..n) = {p | prime p /\ p <= n}`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_NUMSEG; LE_0];
         ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "0")) THEN
  SUBGOAL_THEN
   `((\n. Cx(&1 + &1 / (Re s - &1)) *
          (clog(Cx(&n)) + Cx(&24)) / Cx(&n) cpow (s - Cx(&1)))
     --> Cx(&0)) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC LIM_LOG_OVER_POWER_N;
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
      MATCH_MP_TAC LIM_1_OVER_POWER] THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; COMPLEX_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
  EXISTS_TAC `N0 + N1 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "0" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y) <= e / &2 ==> norm(x - a) < e / &2 ==> norm(y - a) < e`) THEN
  SIMP_TAC[complex_div; GSYM VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[lemma] THEN
  SIMP_TAC[FINITE_ATMOST; GSYM VSUM_SUB] THEN SIMP_TAC[complex_div] THEN
  SIMP_TAC[COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN SIMP_TAC[GSYM complex_div] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum {p | prime p /\ p <= n}
              (\p. clog(Cx(&p)) / Cx(&p) * genzeta (n + 1) s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; GENZETA_OFFSET];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> x < e ==> y <= e`) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `~(n = 0) /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MERTENS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= e ==> &0 <= y ==> abs(x) <= y + e`)) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
      `x' <= x /\ y' = y ==> abs x <= y ==> x' <= y'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1];
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_ADD; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1]];
    MP_TAC(SPECL [`n + 1`; `s:complex`] GENZETA_BOUND) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_DIV; REAL_POS; REAL_SUB_LE;
                 REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= &1 ==> a + b <= abs(&1 + b)`) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE; RE_SUB; RE_CX] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - s) * l <= --((s - &1) * m) <=>
                            (s - &1) * m <= (s - &1) * l`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_SUB_LT] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LT_NZ] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
For all complex numbers `s`, if the real part of `s` is greater than 1, then the sequence whose `n`-th term is given by
(the sum, over all prime numbers `p` less than or equal to `n`, of `log(p)/p`) divided by `n` raised to the power of `s`,
sums to `newman s` (in other words, converges to `newman s`). The sequences start from `n = 1`.

### Informal sketch
The proof establishes the convergence of a series related to the distribution of prime numbers. Here's an outline:
- The proof starts by stripping assumptions and rewriting using definitions of `sums` and `LIM_SEQUENTIALLY.`
- It introduces an arbitrary real number `e > 0` and uses the theorem named `CONVERGES_NEWMAN_PRIME` to show the existence of `sums`.
-  It uses a lemma to rewrite a double summation involving primes. The lemma transforms a sum over `m` (from 1 to `n`) of sums over primes `p <= m` into a sum over primes `p <= n` of sums over `m` (from `p` to `n`).
    - The proof of the lemma involves simplifying using `VSUM_VSUM_PRODUCT` and related theorems about finite sets.
- The proof then establishes that a certain expression involving complex numbers (`Cx(&1 + &1 / (Re s - &1)) * (clog(Cx(&n)) + Cx(&24)) / Cx(&n) cpow (s - Cx(&1))`) converges sequentially to 0. This is done by leveraging existing theorems about limits of complex functions (`LIM_NULL_COMPLEX_LMUL`, `LIM_LOG_OVER_POWER_N`, `LIM_1_OVER_POWER`).
- It introduces `N0` and `N1` based on the existing `e` and combines the above steps, using arithmetic facts (`REAL_HALF`) and the definition of sequential limits, to prove the main goal. It rewrites expressions, using lemmas and arithmetic facts.
- It leverages `REAL_LE_TRANS` to show inequalities based on norms and absolute values.
- It introduces genzeta term, simplifies, apply `GENZETA_BOUND`, `MERTENS` theorems and applies `REAL_LE_MUL2`.
- The proof concludes by establishing the necessary inequality, ensuring the convergence to `newman s`.

### Mathematical insight
The theorem relates to the analytic properties of the Newman function and its connection to the distribution of prime numbers. It's a statement about the asymptotic behavior of a sum involving logarithms of primes, normalized by a power of `n`. It connects the distribution of primes to the analytic behavior of functions of a complex variable.

### Dependencies
- Definitions: `sums`
- Theorems: `CONVERGES_NEWMAN_PRIME`, `LIM_NULL_COMPLEX_LMUL`, `LIM_LOG_OVER_POWER_N`, `LIM_1_OVER_POWER`, `MERTENS`, `GENZETA_BOUND`, `REAL_LE_TRANS`
- Lemmas: `VSUM_VSUM_PRODUCT`

### Porting notes
- HOL Light's rewriting tactics (`REWRITE_TAC`, `ASM_REWRITE_TAC`) are powerful but can be unpredictable. Porting to other systems might require a more fine-grained approach, explicitly specifying which subterms to rewrite.
- The use of `SIMP_TAC` with large lists of theorems can similarly be challenging to replicate directly in other proof assistants. It may be necessary to decompose the simplification steps into smaller, more manageable steps.


---

## MAIN_RESULT

### Name of formal statement
MAIN_RESULT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MAIN_RESULT = prove
 (`?c. summable (from 1)
        (\n. (vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
              clog(Cx(&n)) + c) / Cx(&n))`,
  MP_TAC ANALYTIC_NEWMAN_VARIANT THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:complex`; `singval:complex`] THEN DISCH_TAC THEN
  EXISTS_TAC `c:complex` THEN MP_TAC(SPECL
   [`\z. if z = Cx(&1) then singval
         else newman z + complex_derivative zeta z + c * zeta z`;
    `\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
         clog(Cx(&n)) + c`;
    `&24 + norm(c:complex)`]
  NEWMAN_INGHAM_THEOREM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN
    REWRITE_TAC[RE_CX; real_ge; REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUMS_SUMMABLE) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMMABLE_EQ) THEN
    SIMP_TAC[IN_FROM; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    SIMP_TAC[LE_1; COMPLEX_POW_1]] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x - y) <= &24 ==> norm(x - y + c) <= &24 + norm c`) THEN
    MP_TAC(SPEC `n:num` MERTENS) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM VSUM_CX; CX_SUB; FINITE_ATMOST] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; CX_DIV; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_ASSOC] THEN MATCH_MP_TAC SERIES_ADD THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_CONVERGES) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID]] THEN
  REWRITE_TAC[complex_sub] THEN MATCH_MP_TAC SERIES_ADD THEN
  REWRITE_TAC[GSYM complex_div] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA_CONVERGES]] THEN
  ASM_SIMP_TAC[NEWMAN_CONVERGES]);;
```

### Informal statement
There exists a complex number `c` such that the sequence, indexed from 1, whose `n`-th term is given by the expression `(vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) - clog(Cx(&n)) + c) / Cx(&n)` is summable.

### Informal sketch
The proof establishes the summability of a complex-valued sequence.

- The proof starts by introducing complex variables `c` and `singval`. An existential quantifier for `c` is then introduced.
- It uses `NEWMAN_INGHAM_THEOREM_STRONG` with specific instantiations related to the Riemann zeta function and a constant `c`. This theorem provides a strong result on the convergence of a related series.
- There are then several simplification steps in the hypotheses (using `ASM_REWRITE_TAC[]` and `ANTS_TAC`). Including checking the instance at `Cx(&1)` is correctly defined.
- The constant `c` is handled by appealing to known properties of norms, `MERTENS` (presumably Mertens' theorems), and basic arithmetic operations on complex numbers.
- The summability of relevant series involving the zeta function and its derivative is established by using theorems like `SERIES_ADD`, `SERIES_COMPLEX_LMUL`, `ZETA_CONVERGES`, and `COMPLEX_DERIVATIVE_ZETA_CONVERGES`.
- Finally, `NEWMAN_CONVERGES` is used with simplifications to complete the argument.

### Mathematical insight
This is a deep theorem in analytic number theory. The 'vsum' term involves a sum over the first `n` primes of `clog(Cx(&p)) / Cx(&p)`, where clog is the complex logarithm and Cx is the complex embedding. This theorem essentially states that a certain adjustment of this sum yields an absolutely convergent series; this convergence relates to deep analytical properties of prime numbers and the Riemann zeta function.

### Dependencies

**Theorems and Definitions:**
- `summable`
- `prime`
- `vsum`
- `clog`
- `Cx`
- `NEWMAN_INGHAM_THEOREM_STRONG`
- `MERTENS`
- `SERIES_ADD`
- `SERIES_COMPLEX_LMUL`
- `ZETA_CONVERGES`
- `COMPLEX_DERIVATIVE_ZETA_CONVERGES`
- `NEWMAN_CONVERGES`
- `LEFT_IMP_EXISTS_THM`
- `RE_CX`
- `real_ge`
- `REAL_LE_REFL`
- `SUMS_SUMMABLE`
- `SUMMABLE_EQ`
- `IMP_CONJ`
- `IN_FROM`
- `CPOW_N`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `LE_1`
- `COMPLEX_POW_1`
- `NORM_ARITH`
- `REAL_ARITH`
- `GSYM COMPLEX_NORM_CX`
- `GSYM VSUM_CX`
- `CX_SUB`
- `FINITE_ATMOST`
- `GSYM CX_LOG`
- `REAL_OF_NUM_LT`
- `LT_NZ`
- `PRIME_IMP_NZ`
- `IN_ELIM_THM`
- `real_gt`
- `REAL_LT_REFL`
- `complex_div`
- `COMPLEX_ADD_RDISTRIB`
- `COMPLEX_SUB_RDISTRIB`
- `COMPLEX_ADD_ASSOC`
- `COMPLEX_MUL_LID`
- `complex_sub`
- `GSYM complex_div`
- `GSYM COMPLEX_MUL_LNEG`

### Porting notes (optional)
The use of tactics like `MP_TAC` and `REWRITE_TAC` heavily relies on the specific rewriting and simplification rules in HOL Light. Ensure similar mechanisms are present in the target proof assistant. Special care needs to be taken when porting `NEWMAN_INGHAM_THEOREM_STRONG` since it is a very substantial theorem, likely proven elsewhere. The complex analysis support is central. Need to verify `prime` and `vsum` are available in the target system, as well as their theories.


---

## SUM_GOESTOZERO_LEMMA

### Name of formal statement
SUM_GOESTOZERO_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_GOESTOZERO_LEMMA = prove
 (`!a M N.
        abs(sum(M..N) (\i. a(i) / &i)) <= d
        ==> 0 < M /\ M < N /\ (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
            ==> a(M) <= d * &N / (&N - &M) + (&N - &M) / &M /\
                --a(N) <= d * &N / (&N - &M) + (&N - &M) / &M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a. a <= b /\ x <= a /\ y <= a ==> x <= b /\ y <= b`) THEN
  EXISTS_TAC `d * &N / (&N - &M) + log(&N / &M)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < m /\ &0 < n
                             ==> n / m = &1 + (n - m) / m`] THEN
    MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  SUBGOAL_THEN `!m n. &m <= &n ==> a m + log(&m) <= a n + log(&n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    ASM_REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  CONJ_TAC THEN
  (MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(d * &N) / (&N - &M + &1)` THEN CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
     ASM_REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ (&0 <= x ==> x <= y) ==> x <= y`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `m < n ==> &0 < n - m + &1`;
               REAL_LE_DIV; REAL_LE_MUL; REAL_MUL_LZERO; REAL_POS] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z:real = y * (x * z)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(sum(M..N) (\i. a(i) / &i))` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`);
    MATCH_MP_TAC(REAL_ARITH `a <= --x ==> x <= abs a`)] THEN
  (SUBGOAL_THEN `&N - &M + &1 = &((N + 1) - M)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM
                 REAL_OF_NUM_LE; REAL_ARITH `m < n ==> m <= n + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC]) THEN
  REWRITE_TAC[GSYM SUM_CONST_NUMSEG; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
  (SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB; REAL_SUB_RNEG] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(a M - log(&N * inv(&M))) * inv(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x' <= x /\ a - (x' - m) <= b ==> a - (x - m) <= b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a - (x - y) <= b <=> a + y <= b + x`];
    EXISTS_TAC `(log(&N * inv(&M)) + a N) * inv(&n)` THEN CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `a * x <= a * y <=> --a * y <= --a * x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `--(x + y:real) = --y - x`] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x <= x' /\ a <= y - x' + b ==> a <= y - x + b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= x - y + b <=> a + y <= b + x`]]);;
```
### Informal statement
For all real-valued sequences `a`, and natural numbers `M` and `N`, if the absolute value of the sum from `M` to `N` of `a(i)` divided by `i`, for `i` ranging from `M` to `N`, is less than or equal to `d`, and `0 < M` and `M < N` and for all `n`, `a(n)` plus the logarithm of `n` is less than or equal to `a(n + 1)` plus the logarithm of `n + 1`, then `a(M)` is less than or equal to `d` times `N` divided by `N - M` plus `(N - M)` divided by `M`, and the negation of `a(N)` is less than or equal to `d` times `N` divided by `N - M` plus `(N - M)` divided by `M`.

### Informal sketch
The proof proceeds as follows:
- Assume `abs(sum(M..N) (\i. a(i) / &i)) <= d`, `0 < M`, `M < N`, and `!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1)`.
- Show `&0 <= d` and `0 < N`. These follow directly from the assumptions.
- Establish that `a(M) <= d * &N / (&N - &M) + (&N - &M) / &M`.
- Show that `!m n. &m <= &n ==> a m + log(&m) <= a n + log(&n)`. Uses `TRANSITIVE_STEPWISE_LE` to iterate the hypothesis `!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1)` from `m` to `n`
- Show that `--a(N) <= d * &N / (&N - &M) + (&N - &M) / &M` using `SUM_LE_NUMSEG`, `SUM_CONST_NUMSEG` and `SUM_NEG`

### Mathematical insight
The theorem provides an upper bound on `a(M)` and a lower bound on `a(N)` based on the magnitude of the sum of `a(i) / i` from `M` to `N` and the condition that the sequence `a(n) + log(n)` is increasing. This relates summability to growth conditions on the sequence `a`.

### Dependencies
#### Theorems
- `REAL_ARITH`
- `REAL_LE_LADD`
- `LOG_LE`
- `REAL_LE_DIV`
- `REAL_LE_TRANS`
- `REAL_LE_LMUL`
- `REAL_POS`
- `REAL_LE_INV2`
- `REAL_LE_RDIV_EQ`
- `REAL_ARITH`
- `REAL_LE_DIV`
- `REAL_LE_MUL`
- `REAL_MUL_LZERO`
- `REAL_POS`
- `REAL_LE_TRANS`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_ARITH`

#### Definitions
- `abs`
- `sum`
- `log`
- `real_div`
- `inv`

#### Other
- `ADD1`
- `LOG_DIV`
- `LOG_MONO_LE_IMP`
- `SUM_CONST_NUMSEG`
- `SUM_NEG`
- `SUM_LE_NUMSEG`
### Porting notes (optional)
The proof makes heavy use of real arithmetic reasoning (`REAL_ARITH`) and rewriting. A target proof assistant would need similar capabilities for automated arithmetic reasoning and rewriting with identities. The handling of sums over ranges of natural numbers (`sum(M..N)`) might require special attention depending on how the target assistant represents such sums.


---

## SUM_GOESTOZERO_THEOREM

### Name of formal statement
SUM_GOESTOZERO_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_GOESTOZERO_THEOREM = prove
 (`!a c. ((\i. a(i) / &i) real_sums c) (from 1) /\
         (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
         ==> (a ---> &0) sequentially`,
  let lemma = prove
   (`(!e. &0 < e /\ e < &1 / &4 ==> ?N:num. !n. N <= n ==> f(n) < e)
     ==> (!e. &0 < e ==> ?N. !n. N <= n ==> f(n) < e)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min e (&1 / &5)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[REAL_LT_MIN]) in
  REWRITE_TAC[LEFT_FORALL_IMP_THM; LEFT_EXISTS_AND_THM] THEN
  REWRITE_TAC[REAL_SERIES_CAUCHY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e / &8) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e / &4` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N0 + N1 + 7` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR) THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR_POS) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < k /\ 4 * k <= n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&n * e / &4 < &0 + &1` THEN
      REWRITE_TAC[REAL_NOT_LT; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1 * e / &4` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_ARITH `&4 * x <= y <=> x <= y * inv(&4)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * e / &4` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n - k:num`; `n:num`]);
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + k:num`])] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[FROM_INTER_NUMSEG_GEN] THEN
   COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
   DISCH_THEN(MP_TAC o MATCH_MP SUM_GOESTOZERO_LEMMA) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC])
  THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> --x <= a ==> --b < x`);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> x <= a ==> x < b`)] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `4 * k <= n ==> k <= n`;
               GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `n - (n - k):real = k`;
              REAL_ARITH `(n + k) - n:real = k`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
   `(e / &8) pow 2 * x < e / &2 <=> e * e / &16 * x < e * &2`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k /\ 4 * k <= n ==> k < n`;
               ARITH_RULE `~(n < 1) ==> 0 < n`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k ==> e / &16 * n < &2 * k`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&n * e / &4` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
     `n * e / &4 < e / &2 * m <=> e * n < e * &2 * m`] THEN
    REWRITE_TAC[REAL_ARITH `n < &2 * (n - k) <=> &2 * k < n`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k /\ (&1 / &4 + e / &16) * k < &1 * k
      ==> e / &16 * (n + k) < &2 * k`) THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_OF_NUM_LE; REAL_OF_NUM_LT;
                 ARITH_RULE `1 <= n <=> 0 < n`] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `k <= n * e / &4 /\ &0 < n * e ==> k < e / &2 * n`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `~(n < 1) ==> 0 < n`]]);;  
```

### Informal statement
For all real-valued sequences `a` and real numbers `c`, if the series with terms `a(i) / i` converges to `c` starting from index 1, and for all natural numbers `n`, `a(n) + log(n) <= a(n + 1) + log(n + 1)`, then the sequence `a` converges sequentially to 0.

### Informal sketch
The proof proceeds as follows:

*   First, introduce a lemma: if for any positive real `e` less than 1/4, there exists a natural number `N` such that for all `n >= N`, `f(n) < e`, then for any positive real `e`, there exists a natural number `N` such that for all `n >= N`, `f(n) < e`. This is proved using `REAL_LT_MIN`, `MESON_TAC`, and arithmetic reasoning (using `ASM_REAL_ARITH_TAC`). The purpose of this lemma is to relax the requirement `e < 1/4` when proving the main goal.

*   The main proof starts by rewriting the goal using `LEFT_FORALL_IMP_THM`, `LEFT_EXISTS_AND_THM`, `REAL_SERIES_CAUCHY`, and `REALLIM_SEQUENTIALLY`.

*   Apply the lemma proved earlier to remove the constraint on `e`, and introduce `e` by universal quantification.

*   Assume `0 < e` and the Cauchy criterion for the series `a(i) / i`. The aim is to show that there exists `N` such that for all `n >= N`, `|a(n)| < e`.

*   Instantiate the Cauchy criterion with `(e / 8)^2`. This provides `N0` such that for all `n >= N0` and all `k`, the absolute value of the sum of `a(i) / i` from `n` to `n + k` is less than `(e / 8)^2`.

*   Apply the Archimedean property to `e / 4` to obtain `N1` such that `1 / N1 < e / 4`.

*   The goal now is to find a suitable `N` for the sequential limit. The proof chooses `N = 2 * N0 + N1 + 7`. Then introduce `n` such that `n >= N`.

*   Take `FLOOR` of `(n * e) / 4` and use it as a `k`. Establish the subgoal that `0 < k` and `4 * k <= n`. The subgoal is proven with real and natural number arithmetic.

*   Next, use the assumption `a(n) + log(n) <= a(n + 1) + log(n + 1)` to show `|a(n)| < e` by bounding it by terms related to the sum from n to n+k and inequalities.

*   Finally, some arithmetic reasoning and simplifications involving real numbers, natural numbers and inequalities are used to prove the theorem.

### Mathematical insight
The theorem demonstrates a condition under which the convergence of a real series implies the convergence of a related sequence to 0. The increasing condition `a(n) + log(n) <= a(n + 1) + log(n + 1)` seems to be a necessary condition to propagate the convergence of sum to the single element tending to zero. The key idea is to relate the sequence `a(n)` to the convergent series using the given monotonic condition. This result is important in real analysis, especially for proving convergence results or as an intermediate step in more complex convergence proofs.

### Dependencies
*   `REAL_SERIES_CAUCHY`
*   `REALLIM_SEQUENTIALLY`
*   `REAL_ARCH_INV`
*   `SUM_GOESTOZERO_LEMMA`
*   `REAL_LT_MIN`
*   ... and various arithmetic theorems, and basic real analysis facts.

### Porting notes (optional)
*   The proof relies heavily on real arithmetic reasoning, which could be challenging to automate in some proof assistants.
*   Pay attention to the handling of real numbers and natural numbers.
*   The HOL Light tactics `ASM_REAL_ARITH_TAC` and `ASM_ARITH_TAC` are used extensively for automatic arithmetic reasoning. You may need to use similar tactics or rewrite tactics with simplification rules.


---

## MERTENS_LIMIT

### Name of formal statement
MERTENS_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MERTENS_LIMIT = prove
 (`?c. ((\n. sum {p | prime p /\ p <= n} (\p. log(&p) / &p) - log(&n))
        ---> c) sequentially`,
  X_CHOOSE_THEN `c:complex` MP_TAC MAIN_RESULT THEN
  REWRITE_TAC[summable] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--Re(c)` THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC SUM_GOESTOZERO_THEOREM THEN EXISTS_TAC `Re l` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMS_EQ) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RE_ADD; RE_DIV_CX; RE_SUB; REAL_SUB_RNEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1; RE_CX] THEN
    SIMP_TAC[RE_VSUM; FINITE_ATMOST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; GSYM CX_LOG; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
             GSYM CX_DIV; RE_CX];
    GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
     `s <= s' ==> (s - l - c) + l <= (s' - l' - c) + l'`) THEN
    MATCH_MP_TAC SUM_SUBSET THEN REWRITE_TAC[FINITE_ATMOST] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THENL
     [ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]);;
```
### Informal statement
There exists a complex number `c` such that the sequence, indexed by natural numbers `n`, whose `n`-th term is given by the sum over all primes `p` less than or equal to `n` of `log(p)/p`, minus `log(n)`, converges to `c`.

### Informal sketch
The proof demonstrates the existence of a complex number `c` to which the sequence `(\n. sum {p | prime p /\ p <= n} (\p. log(&p) / &p) - log(&n))` converges.
- First, assume the existence of a complex number `l` to which the sum of `log(&p)/&p` converges when `p` ranges over all primes.
- Then, show that the difference between the real parts of successive approximations tends to 0.
- Use `SUM_GOESTOZERO_THEOREM` to show the sum of real parts converges to some real number by showing the real part forms a Cauchy Sequence.
- Then, with some considerable real-number arithmetic, and using the convergence of `log(p)/p`, show that the sum restricted to the primes less than or equal to `n` minus `log(n)` converges.
- The tactics `SUM_SUBSET` and `ASM_CASES_TAC` are used to handle the conditional inclusion of primes.  The key is bounding real terms, using `REAL_LE_DIV`, which is then discharged by showing positivity.

### Mathematical insight
This theorem establishes the existence of a limit related to the sum of the reciprocals of primes, weighted by their logarithms, subtracted by the logarithm of `n`. This limit, known as Mertens' constant, is a fundamental result in number theory.

### Dependencies
- `summable`
- `SUM_GOESTOZERO_THEOREM`
- `REAL_SUMS_RE`
- `REAL_SUMS_EQ`
- `IN_FROM`
- `RE_ADD`
- `RE_DIV_CX`
- `RE_SUB`
- `REAL_SUB_RNEG`
- `GSYM CX_LOG`
- `REAL_OF_NUM_LT`
- `LE_1`
- `RE_CX`
- `RE_VSUM`
- `FINITE_ATMOST`
- `SUM_EQ`
- `IN_ELIM_THM`
- `PRIME_IMP_NZ`
- `LT_NZ`
- `GSYM CX_DIV`
- `REAL_OF_NUM_ADD`
- `SUM_SUBSET`
- `IN_DIFF`
- `PRIME_GE_2`
- `REAL_LE_DIV`
- `REAL_POS`
- `LOG_POS`


---

## PNT_PARTIAL_SUMMATION

### Name of formal statement
PNT_PARTIAL_SUMMATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PNT_PARTIAL_SUMMATION = prove
 (`&(CARD {p | prime p /\ p <= n}) =
        sum(1..n)
         (\k. &k / log (&k) *
              (sum {p | prime p /\ p <= k} (\p. log (&p) / &p) -
               sum {p | prime p /\ p <= k - 1} (\p. log (&p) / &p)))`,
  REWRITE_TAC[PRIME_ATMOST_ALT] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (PAT_CONV `\x. l = a * (sum(1..x) f - s)`)
        [MATCH_MP (ARITH_RULE `1 <= p ==> p = SUC(p - 1)`) th]) THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= p ==> SUC(p - 1) = p`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < x /\ &0 < y ==> &1 = x / y * y / x`) THEN
  ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; LE_1; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`]);;
```

### Informal statement
The number of primes less than or equal to `n` is equal to the sum from `k = 1` to `n`, of the expression `(k / log(k)) * (S1 - S2)`, where `S1` is the sum of `log(p)/p` over all primes `p` less than or equal to `k`, and `S2` is the sum of `log(p)/p` over all primes `p` less than or equal to `k-1`.

### Informal sketch
The proof proceeds by reformulating the Prime Number Theorem using partial summation.
- Start by rewriting with `PRIME_ATMOST_ALT`.
- Simplify using a combination of rewriting and simplification tactics, including those for sums and finite sets.
- Relate the sum to an equality using `SUM_EQ` and introduce `p` as a variable.
- Rewrite involving `IN_NUMSEG`.
- Perform simplification that deals with a summation indexed by a numerical range, accounting for successor arithmetic.
- Simplify using arithmetic rules and algebraic identities, including `REAL_ADD_SUB` and rules related to multiplication by zero.
- Apply field arithmetic to simplify expressions involving division, ensuring that `log(p)` is positive for relevant primes `p`.
- Final simplification using lemmas about logarithms, real numbers, prime numbers, and basic arithmetic.

### Mathematical insight
This theorem reformulates the prime-counting function (`pi(n)`) using a partial summation formula. This transformation is useful because it expresses `pi(n)` in terms of sums involving `log(p)/p` over primes, which are often easier to analyze and estimate. The partial summation technique is a valuable tool in analytic number theory for relating sums over primes to other quantities.

### Dependencies
- `PRIME_ATMOST_ALT`
- `REAL_MUL_RID`
- `SUM_CONST`
- `FINITE_NUMSEG`
- `FINITE_RESTRICT`
- `SUM_RESTRICT_SET`
- `SUM_EQ`
- `IN_NUMSEG`
- `SUM_CLAUSES_NUMSEG`
- `REAL_ADD_SUB`
- `REAL_MUL_RZERO`
- `REAL_FIELD`
- `LOG_POS_LT`
- `REAL_OF_NUM_LT`
- `LE_1`
- `PRIME_GE_2`


---

## SUM_PARTIAL_LIMIT

### Name of formal statement
SUM_PARTIAL_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_PARTIAL_LIMIT = prove
 (`!f e c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n + 1)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g") (LABEL_TAC "e")) THEN
  SUBGOAL_THEN `!k:num. M <= k ==> &0 <= f k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SIMP_TAC[tendsto_real] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?N. (!k. N <= k ==> &0 < f k) /\
                    (!k. N <= k ==> f(k) <= f(k + 1)) /\
                    (!k. N <= k ==> abs(e k - c) < d / &4)`
   (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)
  THENL
   [USE_THEN "e" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `d / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[ARITH_RULE `M + N <= (n:num) ==> M <= n /\ N <= n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N + 1 <= n
        ==> abs((sum((N+1)..n) (\k. e k * (f (k + 1) - f k)) -
                 e(n) * f(n + 1)) +
                c * f(N + 1))
            <= d / &2 * f(n + 1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\k. (e k - c:real) * (f (k + 1) - f k)`;
                   `\k. d / &4 * (f (k + 1) - f k)`;
                   `(N+1)..n`] SUM_ABS_LE) THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; ARITH_RULE `N + 1 <= n ==> N <= n`;
                   REAL_ARITH `a <= b ==> abs(b - a) = b - a`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_PARTIAL_SUC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
     [SUM_PARTIAL_SUC] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= d * f1 /\ &0 <= dd /\ abs(en - cn) <= d / &4 * f1
      ==> abs(s - (cn - cN)) <= d / &4 * f1 - dd
          ==> abs(s - en + cN) <= d / &2 * f1`) THEN
    REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_SUB_RDISTRIB] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_DIV; REAL_LT_IMP_LE; REAL_OF_NUM_LT;
                 ARITH; LE_ADD; ARITH_RULE `N + 1 <= n ==> N <= n + 1`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  USE_THEN "g" (MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `sum(1..N) (\k. e k * (f (k + 1) - f k)) - c * f(N + 1)`) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `N + 1 <= n`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `&0 < x ==> abs x = x`;
               ARITH_RULE `N + 1 <= n ==> N <= n + 1`; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all functions `f` and `e` from natural numbers to real numbers, and for all real numbers `c` and natural numbers `M`, if the following conditions hold:
1. For all natural numbers `k`, if `M` is less than or equal to `k`, then `0 < f(k)`.
2. For all natural numbers `k`, if `M` is less than or equal to `k`, then `f(k) <= f(k+1)`.
3. The sequence defined by `inv(f k)` tends to `0` sequentially.
4. The sequence defined by `e(k)` tends to `c` sequentially.

Then, the sequence defined by `(sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) / f(n + 1)` tends to `0` sequentially.

### Informal sketch
The proof establishes that under certain conditions, a specific sequence involving partial sums and functions `f` and `e` converges to zero.
- It begins by assuming the hypotheses regarding `f`, `e`, `c`, and `M`. Specifically, `f` is positive and monotonically increasing beyond `M`, `inv (f k)` tends to `0`, and `e(k)` tends to `c`.
- A subgoal `!k:num. M <= k ==> &0 <= f k` is proven using `REAL_LT_IMP_LE`.
- Using `tendsto_real`, the goal is to show sequential convergence. An arbitrary `d:real` is introduced for the epsilon-delta argument.
- The convergence of `e k` to `c` allows us to find an `N` such that for all `k >= N`, `abs(e k - c) < d / &4`.
- The crux of the proof involves bounding `abs((sum((N+1)..n) (\k. e k * (f (k + 1) - f k)) - e(n) * f(n + 1)) + c * f(N + 1))` by `d / &2 * f(n + 1)` for `n >= N + 1`. This is achieved using `SUM_ABS_LE` and properties of real numbers, including `REAL_ABS_MUL`, `REAL_SUB_RDISTRIB`, `SUM_SUB_NUMSEG` and `SUM_PARTIAL_SUC`.
- A crucial step utilizes the convergence of `inv(f k)` to `0` to show that `sum(1..N) (\k. e k * (f (k + 1) - f k)) - c * f(N + 1)` tends to `0`. `REALLIM_LMUL` is used.
- An `N + 1` is chosen and the target is reduced to proving that `abs((sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) / f(n + 1))` is less than `d`, given that `N + 1 <= n`.
- Simplifications involving properties of real number arithmetic, summation, and inequalities complete the argument.

### Mathematical insight
This theorem provides a criterion for the convergence of a sequence related to partial sums. The key idea likely revolves around using the convergence of `e(k)` to `c` and `1/f(k)` to zero to bound the given sequence.

### Dependencies
- `REAL_LT_IMP_LE`
- `tendsto_real`
- `REALLIM_SEQUENTIALLY`
- `ARITH_RULE`
- `SUM_ABS_LE`
- `IN_NUMSEG`
- `FINITE_NUMSEG`
- `REAL_ABS_MUL`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `REAL_SUB_LE`
- `REAL_SUB_RDISTRIB`
- `SUM_SUB_NUMSEG`
- `SUM_PARTIAL_SUC`
- `REAL_SUB_RZERO`
- `REAL_SUB_REFL`
- `REAL_MUL_RZERO`
- `SUM_0`
- `REAL_LE_MUL`
- `REAL_LE_MUL2`
- `REAL_ABS_POS`
- `REALLIM_LMUL`
- `REAL_SEQ_OFFSET`
- `REAL_MUL_RZERO`
- `EVENTUALLY_MP`
- `EVENTUALLY_SEQUENTIALLY`
- `REAL_ABS_DIV`
- `REAL_ABS_INV`
- `real_div`
- `REAL_LT_LDIV_EQ`
- `SUM_COMBINE_R`

### Porting notes (optional)
- The proof relies heavily on real analysis and summation properties. Ensure that the target proof assistant has equivalent theorems available, or be prepared to prove them.
- The sequential convergence is expressed using `tendsto_real`, which will likely need to be translated into an equivalent notion in the target system (e.g., an epsilon-delta definition).
- `SUM_PARTIAL_SUC` is related to summation; ensure the target system has similar results for manipulating summations.


---

## SUM_PARTIAL_LIMIT_ALT

### Name of formal statement
SUM_PARTIAL_LIMIT_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_PARTIAL_LIMIT_ALT = prove
 (`!f e b c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        ((\n. f(n + 1) / f n) ---> b) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
         f(n + 1)) * (f(n + 1) / f(n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `M:num` THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a /\ &0 < b ==> x / b * b / a = x / a`;
                 ARITH_RULE `M <= n ==> M <= n + 1`];
    ALL_TAC] THEN
  SUBST1_TAC(REAL_ARITH `&0 = &0 * b`) THEN
  MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_PARTIAL_LIMIT THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all functions `f`, `e` and real numbers `b`, `c`, and natural number `M`, if the following conditions hold:
1. For all natural numbers `k`, if `M` is less than or equal to `k`, then `0 < f(k)`.
2. For all natural numbers `k`, if `M` is less than or equal to `k`, then `f(k) <= f(k + 1)`.
3. The sequence defined by `inv(f k)` converges to `0`.
4. The sequence defined by `f(n + 1) / f(n)` converges to `b`.
5. The sequence defined by `e(n)` converges to `c`.

Then, the sequence defined by `(sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) / f(n)` converges to `0`.

### Informal sketch
The proof proceeds as follows:
- The goal is to show the convergence of a sequence to 0.
- The theorem `REALLIM_TRANSFORM_EVENTUALLY` is used to transform the limit by multiplying with `f(n + 1) / f(n)`, which converges to some limit `b` as shown in the antecedent.
- The next step uses `EVENTUALLY_SEQUENTIALLY` to introduce a natural number `M` such that antecedent conditions hold for all `k >= M`. `ASM_SIMP_TAC` is used alongside `REAL_FIELD` to deal with Real arithmetic in order to maintain the inequality. `ARITH_RULE` is used to increment the index of the inequality
- The goal is reduced to showing that `(sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) / f(n + 1)` converges to 0, as `f(n + 1) / f(n)` converges to `b`.
- `REAL_ARITH` is used to convert `&0` to `&0 * b`, allowing usage of `REALLIM_MUL`, which means that the product of the prior limit and the limit of `f(n+1) / f(n)` is zero.
- Finally, the theorem `SUM_PARTIAL_LIMIT` is applied along with `ASM_MESON_TAC` to complete the proof.

### Mathematical insight
This theorem provides a condition under which a specific form of partial summation converges to 0. It's a convergence result for sequences related to Riemann-Stieltjes sums. It specifies that if `f` is a positive, non-decreasing function whose inverse converges to 0, and `f(n + 1) / f(n)` converges to some constant `b`, and `e(n)` converges to some constant `c`, then the given expression involving the sum converges to 0. This result is useful when we want to estimate the asymptotic behavior of sums involving differences of a function `f`.

### Dependencies
- `REALLIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `REAL_FIELD`
- `SUM_PARTIAL_LIMIT`


---

## REALLIM_NA_OVER_N

### Name of formal statement
REALLIM_NA_OVER_N

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_NA_OVER_N = prove
 (`!a. ((\n. (&n + a) / &n) ---> &1) sequentially`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N]]);;
```

### Informal statement
For all real numbers `a`, the sequence defined by `(n + a) / n` converges to 1 as `n` tends to infinity sequentially.

### Informal sketch
* The goal is to prove that for any real number `a`, the limit of the sequence `(n + a) / n` as `n` approaches infinity is 1.
* Apply the distribution law to rewrite `(n + a) / n` as `n / n + a / n`, which simplifies to `1 + a / n`.
* Decompose the limit `lim (1 + a/n)` into `lim 1 + lim (a/n)` using `REALLIM_ADD`.
* Show that `lim 1 = 1` using `REALLIM_CONST`.
* Show that `lim (a / n) = 0`. This is done by using `REALLIM_NULL_LMUL` to show that `lim (a * (1/n)) = a * lim (1/n) = a * 0 = 0`. To apply `REALLIM_NULL_LMUL`, we first use `REALLIM_TRANSFORM_EVENTUALLY` to rewrite the limit so it applies, and eventually `REALLIM_1_OVER_N`.
* Finally combine the two limits to get `1 + 0 = 1`.

### Mathematical insight
This theorem demonstrates a basic result in real analysis, showing that a sequence of the form `(n + a) / n` approaches 1 as `n` goes to infinity. It relies on breaking down the limit into simpler limits and using established limit theorems.

### Dependencies
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_ADD_RID`
- `REALLIM_ADD`
- `REALLIM_TRANSFORM_EVENTUALLY`
- `REALLIM_CONST`
- `EVENTUALLY_SEQUENTIALLY`
- `REAL_OF_NUM_LE`
- `REAL_FIELD`
- `REALLIM_NULL_LMUL`
- `REALLIM_1_OVER_N`


---

## REALLIM_N_OVER_NA

### Name of formal statement
REALLIM_N_OVER_NA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_N_OVER_NA = prove
 (`!a. ((\n. &n / (&n + &1)) ---> &1) sequentially`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_NA_OVER_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all real numbers `a`, the sequence defined by `n` mapping to `n / (n + 1)` converges to `1` as `n` tends to infinity.

### Informal sketch
The proof demonstrates that the limit of the sequence `n / (n + 1)` as `n` approaches infinity is equal to `1`.

- First, rewrite `n / (n + 1)` as `1 / ((n + 1) / n)`. This is done using `GSYM REAL_INV_DIV`.
- Next, simplify `(n + 1) / n` to `1 + (1 / n)`. This uses rewriting with theorems about division as well as `GSYM REAL_INV_1`.
- Apply the theorem `REALLIM_INV`, which states that the limit of the reciprocal of a sequence that converges to a non-zero limit is the reciprocal of that limit. This requires matching the current goal with the hypothesis of `REALLIM_INV` using `MATCH_MP_TAC`.
- Now, the goal is to show that the limit of `1 + (1 / n)` is `1`. This uses the pre-proved theorem `REALLIM_NA_OVER_N`.
- Finally, symbolically simplify the resulting expression to complete the proof using `REAL_RAT_REDUCE_CONV`.

### Mathematical insight
This theorem establishes a basic limit result, demonstrating that as `n` grows infinitely large, the fraction `n / (n + 1)` approaches `1`. This result is important in real analysis and calculus for evaluating limits of more complex expressions and sequences.

### Dependencies
- `REAL_INV_DIV`
- `REAL_INV_1`
- `REALLIM_INV`
- `REALLIM_NA_OVER_N`
- `REAL_RAT_REDUCE_CONV`


---

## REALLIM_LOG1_OVER_LOG

### Name of formal statement
REALLIM_LOG1_OVER_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_LOG1_OVER_LOG = prove
 (`((\n. log(&n + &1) / log(&n)) ---> &1) sequentially`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. &1 + log(&1 + &1 / &n) / log(&n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_ARITH `&2 <= x ==> &1 < x`;
       REAL_FIELD `&0 < x ==> (&1 + a / x = b / x <=> x + a = b)`] THEN
    ASM_SIMP_TAC[GSYM LOG_MUL; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
                 REAL_LE_DIV; REAL_POS; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
    AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n)` THEN REWRITE_TAC[REALLIM_1_OVER_N] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_LE_INV_EQ; REAL_POS;
                 REAL_ARITH `&0 <= x ==> &1 <= &1 + x`] THEN
    MATCH_MP_TAC LOG_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * log(&2)` THEN
  CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;
```

### Informal statement
The limit, as n approaches infinity, of `log(n + 1) / log(n)` is equal to 1, where n is a natural number.

### Informal sketch
The proof demonstrates that the sequence `log(n + 1) / log(n)` converges to 1 as n approaches infinity.

- First, it's shown that there exists a function `f(n) = 1 + log(1 + 1/n) / log(n)` such that `log(n + 1) / log(n) = f(n)` for sufficiently large `n`.
- Then, it's proven that `f(n)` has a limit of 1. This part uses algebraic simplification and inequalities to show that for large enough `n`, the difference between  `log(n + 1) / log(n)` and 1 can be made arbitrarily small. It involves bounding the term `log(1 + 1/n) / log(n)` by `2 * log(2) / n`, and using `REALLIM_1_OVER_N` to show that the limit of `inv(n)` is 0, so its ultimately negligible.
- Specifically, we need to find an `N` such that for all `n > N`, `abs(log(n+1)/log(n) - 1) < epsilon`.
  - Rewriting the left hand side gives `abs(log(1 + 1/n) / log(n)) < epsilon`.
  - Note that `log(1+x) <= x` for `x >= 0`. So `log(1 + 1/n) <= 1/n`.
  - Thus it is sufficient to have `abs(1/(n log(n)) < epsilon`. Which simplifies to showing there exists an `N` such that for an `n > N`, `n log(n) > 1/epsilon`.
  - `log(n)` grows arbitrarily slowly so there is no closed form expression for `N` in terms of epsilon.

### Mathematical insight
This theorem establishes a fundamental property about the asymptotic behavior of the logarithm function. It shows that as n becomes large, the ratio of the logarithms of consecutive integers tends to 1. This result is useful in various areas of mathematics, particularly in analysis and number theory when dealing with asymptotic estimates and growth rates.

### Dependencies
- `REALLIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `GSYM REAL_OF_NUM_LE`
- `LOG_POS_LT`
- `REAL_ARITH`
- `REAL_FIELD`
- `GSYM LOG_MUL`
- `REAL_LE_DIV`
- `REAL_POS`
- `GSYM REAL_ADD_RID`
- `REALLIM_ADD`
- `REALLIM_CONST`
- `REALLIM_NULL_COMPARISON`
- `REALLIM_1_OVER_N`
- `real_div`
- `REAL_ABS_MUL`
- `GSYM REAL_MUL_RID`
- `REAL_LE_MUL2`
- `REAL_ABS_POS`
- `REAL_MUL_LID`
- `LOG_POS`
- `REAL_LE_INV_EQ`
- `REAL_ARITH`
- `LOG_LE`
- `REAL_ABS_INV`
- `REAL_INV_LE_1`
- `REAL_LE_TRANS`
- `LOG_2_BOUNDS`
- `REAL_OF_NUM_LT`
- `ARITH`
- `LOG_MONO_LE_IMP`
- `REAL_RAT_REDUCE_CONV`
- `REAL_OF_NUM_LE`

### Porting notes (optional)
- The use of `EVENTUALLY_SEQUENTIALLY` tactic suggests a focus on the tail behavior of the sequence, which is a common technique in real analysis.
- The proof relies heavily on real arithmetic (`REAL_ARITH`, `REAL_FIELD`) and inequalities. Ensure that the target proof assistant has adequate support for these.
- The extensive use of rewriting (`REWRITE_TAC`) indicates that the proof involves a series of symbolic manipulations.


---

## REALLIM_LOG_OVER_LOG1

### Name of formal statement
REALLIM_LOG_OVER_LOG1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_LOG_OVER_LOG1 = prove
 (`((\n. log(&n) / log(&n + &1)) ---> &1) sequentially`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_LOG1_OVER_LOG] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
The limit of `log(n) / log(n + 1)` as `n` tends to infinity is `1`.

### Informal sketch
The proof proceeds as follows:
- Rewrite `log(n) / log(n + 1)` to `(1 / log(n + 1))/(1 / log(n))` using `REAL_INV_DIV` and `REAL_INV_1`.
- Apply the theorem `REALLIM_INV`, which states if `f(x)` tends to L, then `1/f(x)` tends to `1/L`. This reduces the goal to showing that the limit of `1 / log(n + 1)` divided by `1 / log(n)` as `n` goes to infinity exists and it is equal to 1.
- Apply `REALLIM_LOG1_OVER_LOG` to rewrite the goal to the limit of `log(n) / log(n + 1)` to 1 and simplify the resulting rational expression using `REAL_RAT_REDUCE_CONV`.

### Mathematical insight

This theorem confirms the intuition that for large `n`, `log(n)` and `log(n + 1)` are asymptotically equivalent. This result is useful when analyzing the asymptotic behavior of functions involving logarithms.

### Dependencies
- `REAL_INV_DIV`
- `REAL_INV_1`
- `REALLIM_INV`
- `REALLIM_LOG1_OVER_LOG`
- `REAL_RAT_REDUCE_CONV`


---

## ADHOC_BOUND_LEMMA

### Name of formal statement
ADHOC_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ADHOC_BOUND_LEMMA = prove
 (`!k. 1 <= k ==> abs((&k + &1) * (log(&k + &1) - log(&k)) - &1)
                  <= &2 / &k`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then clog z
           else if n = 1 then inv z
           else --inv(z pow 2)`;
    `Cx(&k + &1)`; `Cx(&k)`; `1`]
        COMPLEX_TAYLOR_MVT) THEN
  REWRITE_TAC[ARITH; ADD_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_DIV_1; complex_pow; COMPLEX_POW_1; COMPLEX_VEC_0] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_ADD_RID;
              REAL_ARITH `k - (k + &1) = -- &1`] THEN
  REWRITE_TAC[CX_SUB; CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG;
              COMPLEX_NEG_NEG; COMPLEX_MUL_RID] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN
    REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH] THEN
    COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; complex_div; COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k /\ &0 < &k + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[RE_ADD] THEN
  ONCE_REWRITE_TAC[REAL_RING `w:real = z + u <=> w - z = u`] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_INV; GSYM CX_ADD; GSYM CX_SUB;
               GSYM CX_NEG; RE_CX] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (&k + &1)`) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < x ==> x * (y - (z + --inv x)) = &1 - x * (z - y)`] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
  REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_MUL; GSYM CX_POW; GSYM CX_INV; RE_CX] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_POW_INV; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d = (a * b:real) * (c * d)`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_LE_LDIV_EQ;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `k`, if `1` is less than or equal to `k`, then the absolute value of `((k + 1) * (log(k + 1) - log(k)) - 1)` is less than or equal to `2 / k`.

### Informal sketch
The proof proceeds as follows:
- The theorem is proved by using a Taylor expansion in the complex plane. More precisely, the mean value theorem `COMPLEX_TAYLOR_MVT` for complex functions is applied to the complex logarithm function `clog(z)`.
- The real and imaginary parts of the complex expressions are extracted, and real arithmetic tactics are used to simplify and estimate the resulting inequalities.
- Several simplification steps are involved including rewriting with definitions of complex arithmetic, and properties of real numbers such as inequalities, absolute values, and division.

The main steps are:
- Instantiate a complex Taylor expansion theorem `COMPLEX_TAYLOR_MVT` with `clog(z)`, `Cx(&k+1)`, `Cx(&k)`, and `1`, to obtain an estimate for `log(k+1) - log(k)`.
- Simplify the resulting expression using arithmetic identities and definitions of complex operations.
- Deduce the bound `abs((&k + &1) * (log(&k + &1) - log(&k)) - &1) <= &2 / &k` by real arithmetic, leveraging that `1 <= k`.

### Mathematical insight
The theorem gives an explicit bound on the error when approximating `log(k+1) - log(k)` by `1/(k+1)`. This is useful for estimating logarithms and related sums.

### Dependencies
Real Analysis:
- `COMPLEX_TAYLOR_MVT`
- `IN_SEGMENT_CX_GEN`

Complex Arithmetic:
- `CX_LOG`, `CX_INV`, `CX_ADD`, `CX_SUB`, `CX_NEG`, `RE_CX`, `CX_SUB`, `CX_MUL`, `CX_POW`
- `COMPLEX_EQ`, `RE_CX`, `IM_CX`
- `COMPLEX_DIV_1`, `complex_pow`, `COMPLEX_POW_1`, `COMPLEX_VEC_0`
- `complex_div`, `COMPLEX_MUL_LNEG`
- `COMPLEX_MUL_LID`
- `complex_pow`

Real Arithmetic:
- `REAL_OF_NUM_LE`
- `REAL_RING`, `REAL_FIELD`
- `REAL_ABS_SUB`, `REAL_ABS_POS`, `REAL_ABS_MUL`, `REAL_ABS_DIV`, `REAL_ABS_INV`
- `REAL_LE_MUL2`, `REAL_LE_INV2`, `REAL_LE_LDIV_EQ`
- `REAL_MUL_ASSOC`, `REAL_POW_2`, `REAL_POW_INV`
- `real_div`

General:
- `ARITH`, `ADD_EQ_0`
- `VSUM_CLAUSES`, `FINITE_INSERT`, `FINITE_RULES`
- `IN_INSERT`, `NOT_IN_EMPTY`
- `COMPLEX_ADD_RID`
- `CX_NEG`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, `COMPLEX_NEG_NEG`, `COMPLEX_MUL_RID`
- `REAL_ARITH`
- `real`

### Porting notes (optional)
- The proof relies heavily on HOL Light's real and complex arithmetic tactics. Other proof assistants may require more manual manipulation of inequalities and complex identities.
- Ensure that the `COMPLEX_TAYLOR_MVT` equivalent theorem is available or proved beforehand.
- Be mindful of differences in how real and complex numbers are represented and coerced between each other.


---

## REALLIM_MUL_SERIES

### Name of formal statement
REALLIM_MUL_SERIES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_MUL_SERIES = prove
 (`!x y z B.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        eventually (\n. abs(sum (1..n) x / z(n)) <= B) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REWRITE_TAC[CONJ_ASSOC; GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[tendsto_real] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ASSUME
   `eventually (\n. &0 < x n /\ &0 < y n /\ &0 < z n) sequentially`) THEN
  MP_TAC(ASSUME `((\n. y n / x n) ---> &0) sequentially`) THEN
  REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&1 + abs B))`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_HALF; IMP_IMP; GSYM EVENTUALLY_AND] THEN
  GEN_REWRITE_TAC LAND_CONV [EVENTUALLY_SEQUENTIALLY] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `((\n. inv (z n)) ---> &0) sequentially`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `e / (&2 * (&1 + abs B)) * abs(sum(1..N) x) + abs(sum(1..N) y)`) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MP_TAC(ASSUME
   `eventually (\n. abs (sum (1..n) x / z n) <= B) sequentially`) THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `!x. abs(x) / z(n:num) = abs(x / z n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM real_div] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y'. abs(y) <= y' /\ abs(x) + y' < e ==> abs(x + y) < e`) THEN
  EXISTS_TAC `e / (&2 * (&1 + abs B)) * sum(N+1..n) x / z n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ABS_MUL; REAL_ABS_INV;
                 REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`;
                 REAL_LE_RMUL_EQ; REAL_LT_INV_EQ; REAL_MUL_ASSOC;
                 GSYM REAL_LE_LDIV_EQ] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ abs x < y ==> x <= y`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(d * abs xN + abs yN) < e / &2
    ==> d * abs xN = abs(d * xN) /\ abs(d * xN + xn) <= e / &2
        ==> abs(yN) + xn < e`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM;
              GSYM REAL_ADD_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`;
               REAL_ARITH `abs(&1 + abs B) = &1 + abs B`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(e * inv(&2) * i) * x = (e * inv(&2)) * x * i`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs B`] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For all real-valued sequences `x`, `y`, and `z`, and a real number `B`, if eventually `x(n)` is greater than 0 sequentially, eventually `y(n)` is greater than 0 sequentially, eventually `z(n)` is greater than 0 sequentially, the sequence `inv(z(n))` tends to 0 sequentially, eventually the absolute value of the sequence `sum (1..n) x / z(n)` is bounded by `B` sequentially, and the sequence `y(n) / x(n)` tends to 0 sequentially, then the sequence `sum (1..n) y / z(n)` tends to 0 sequentially.

### Informal sketch
The proof demonstrates that under the given conditions, the sequence `sum (1..n) y / z(n)` converges to 0.

- The proof begins by simplifying the goal and introducing an arbitrary positive real number `e` which represents the desired level of closeness to 0. We need to show that `abs(sum (1..n) y / z(n))` is less than `e` for sufficiently large `n`.
- We use the assumptions that `x(n)`, `y(n)`, and `z(n)` are positive, `inv (z(n))` tends to zero, `abs(sum (1..n) x / z(n))` is bounded by `B`, and `y(n) / x(n)` tends to zero.
- An `N` is chosen based on the convergence of `inv(z(n))` and `y(n) / x(n)`. For `n > N`, `inv(z(n))` is close enough to 0, and `y(n) / x(n)` is also close enough to zero.
- The sum `sum (1..n) y / z(n)` is split into two parts: `sum (1..N) y / z(n)` and `sum (N+1..n) y / z(n)`. 
- The first sum, `sum (1..N) y / z(n)`, is handled by the fact that `inv(z(n))` tends to zero. Since `N` is fixed, this term becomes arbitrarily small as `n` tends to infinity (because `z(n)` tends to infinity).
- For the second sum, `sum (N+1..n) y / z(n)`, we use the fact that `y(n) / x(n)` tends to zero, so `y(n)` is much smaller than `x(n)` for large `n`. The condition `abs(sum (1..n) x / z(n)) <= B` is used to bound the sum involving `x(n)`.
- By combining these results, we show that the absolute value of `sum (1..n) y / z(n)` can be made smaller than `e` for sufficiently large `n`, thus proving the convergence to 0.

### Mathematical insight
This theorem is a real analysis result establishing the convergence of a series under specific conditions. It relates the convergence of a series involving `y` to the convergence of a related series involving `x`, given relationships between `x`, `y`, and `z`. Intuitively, if `y` is much smaller than `x` (in the limit) and the series involving `x` is well-behaved (bounded), then the series involving `y` also converges to zero. This is a form of summation by parts.

### Dependencies
- `CONJ_ASSOC`
- `EVENTUALLY_AND`
- `tendsto_real`
- `REALLIM_LMUL`
- `REAL_HALF`
- `SUM_COMBINE_R`
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_SUB_RDISTRIB`
- `REAL_MUL_ASSOC`
- `REAL_ABS_DIV`
- `REAL_ARITH`
- `ARITH_RULE`
- `SUM_LMUL`
- `SUM_RMUL`
- `SUM_ABS_LE`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `REAL_ABS_MUL`
- `REAL_ABS_INV`
- `REAL_LE_RMUL_EQ`
- `REAL_LT_INV_EQ`
- `REAL_LE_LDIV_EQ`
- `REAL_ABS_NUM`
- `REAL_ADD_LDISTRIB`
- `REAL_INV_MUL`
- `REAL_MUL_RID`
- `REAL_LE_LMUL`

### Porting notes (optional)
- The `sequentially` filter and `eventually` quantifier are specific to HOL Light. These may need to be defined in the target proof assistant using appropriate filters/predicates on natural numbers.
- The handling of real arithmetic in HOL Light (using `REAL_ARITH`) may need to be adapted based on the automation available in the target proof assistant. Specifically HOL Light's rewriting tactics are powerful, you would need to express those steps in the target proof assistant. The tactics `ASM_REAL_ARITH_TAC` are a good point in case.


---

## REALLIM_MUL_SERIES_LIM

### Name of formal statement
REALLIM_MUL_SERIES_LIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_MUL_SERIES_LIM = prove
 (`!x y z l.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        ((\n. sum (1..n) x / z(n)) ---> l) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_MUL_SERIES THEN
  EXISTS_TAC `x:num->real` THEN
  MP_TAC(MATCH_MP REAL_CONVERGENT_IMP_BOUNDED
   (ASSUME `((\n. sum (1..n) x / z n) ---> l) sequentially`)) THEN
  REWRITE_TAC[real_bounded] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[ALWAYS_EVENTUALLY; FORALL_IN_IMAGE; IN_UNIV]);;
```
### Informal statement
For all real-valued sequences `x`, `y`, and `z`, and for all real numbers `l`, if:
1. `x(n)` is eventually positive, i.e., eventually `&0 < x(n)`,
2. `y(n)` is eventually positive, i.e., eventually `&0 < y(n)`,
3. `z(n)` is eventually positive, i.e., eventually `&0 < z(n)`,
4. `inv(z(n))` converges to `&0` as `n` tends to infinity,
5. the sequence of partial sums of `x(n)` divided by `z(n)` converges to `l` as `n` tends to infinity i.e., `sum (1..n) x / z(n) ---> l`, and
6. `y(n) / x(n)` converges to `&0` as `n` tends to infinity,

then the sequence of partial sums of `y(n)` divided by `z(n)` converges to `&0` as `n` tends to infinity, i.e., `sum (1..n) y / z(n) ---> &0`.

### Informal sketch
The proof proceeds as follows:

- Start by stripping the goal.
- Apply the theorem `REALLIM_MUL_SERIES`.
- Instantiate the existentially quantified variable `x` to `x:num->real`.
- Use `REAL_CONVERGENT_IMP_BOUNDED` to show `((\n. sum (1..n) x / z n) ---> l)` implies `real_bounded (\n. sum (1..n) x / z n)`.
- Rewrite with `real_bounded`.
- Apply `MONO_EXISTS`.
- Simplify using `ALWAYS_EVENTUALLY`, `FORALL_IN_IMAGE`, and `IN_UNIV`.

### Mathematical insight
This theorem provides a condition under which the convergence of a series multiplied by a sequence approaching zero implies the convergence of another related series. It is useful in analyzing the asymptotic behavior of series, particularly when one series is known to converge and the other is related to it by a factor that tends to zero. The condition that `x`, `y`, and `z` are eventually positive ensures that we are not dealing with oscillating behavior near zero that could complicate the convergence analysis.

### Dependencies
- `REALLIM_MUL_SERIES`
- `REAL_CONVERGENT_IMP_BOUNDED`
- `real_bounded`
- `ALWAYS_EVENTUALLY`
- `FORALL_IN_IMAGE`
- `IN_UNIV`


---

## PNT

### Name of formal statement
PNT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PNT = prove
 (`((\n. &(CARD {p | prime p /\ p <= n}) / (&n / log(&n)))
    ---> &1) sequentially`,
  REWRITE_TAC[PNT_PARTIAL_SUMMATION] THEN
  REWRITE_TAC[SUM_PARTIAL_PRE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; SUB_REFL; CONJUNCT1 LE] THEN
  SUBGOAL_THEN `{p | prime p /\ p = 0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) *
         sum {p | prime p /\ p <= n} (\p. log(&p) / &p) -
         sum (1..n)
         (\k. sum {p | prime p /\ p <= k} (\p. log(&p) / &p) *
              ((&k + &1) / log(&k + &1) - &k / log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * log(&n) -
         sum (1..n)
         (\k. log(&k) * ((&k + &1) / log(&k + &1) - &k / log(&k)))) /
        (&n / log(&n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(a * x - s) / b - (a * x' - s') / b:real =
      ((s' - s) - (x' - x) * a) / b`] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC SUM_PARTIAL_LIMIT_ALT THEN
    EXISTS_TAC `&1` THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `16` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[MERTENS_LIMIT] THEN REWRITE_TAC[REAL_INV_DIV] THEN
    SIMP_TAC[REAL_LT_DIV; LOG_POS_LT; REAL_OF_NUM_LT;
             ARITH_RULE `16 <= n ==> 0 < n /\ 1 < n`] THEN
    REWRITE_TAC[REALLIM_LOG_OVER_N] THEN CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
      REWRITE_TAC[REAL_MUL_AC]] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`\z. z / clog z`; `\z. inv(clog z) - inv(clog z) pow 2`;
                  `Cx(&n)`; `Cx(&n + &1)`]
                COMPLEX_MVT_LINE) THEN
    REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
    REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
       [SUBGOAL_THEN `~(z = Cx(&0))` MP_TAC THENL
         [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
        REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
      REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_ARITH `&16 <= x ==> &0 < x`] THEN
      REWRITE_TAC[CX_INJ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
    REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 < Re z /\ &0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_POW; GSYM CX_INV; GSYM CX_SUB;
                 GSYM CX_DIV; RE_CX; GSYM CX_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_SUB; REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH `x pow 2 <= x <=> x * x <= x * &1`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN ONCE_REWRITE_TAC[SUM_PARTIAL_SUC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * (log(&n) - log(&n + &1)) +
         sum(1..n) (\k. (&k + &1) / log(&k + &1) *
                        (log(&k + &1) - log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_OF_NUM_ADD; LOG_1; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC i`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a * (x - y) + s + a * (y - x):real = s`] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. sum(1..n) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) /
        ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
    EXISTS_TAC `\n. ((&n + &2) / log (&n + &2) +
                   (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &17 / log (&17))) / ((&n + &1) / log (&n + &1))` THEN
    EXISTS_TAC `\n.  ((&n + &1) / log(&n + &1) +
                (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &16 / log (&16))) / ((&n + &1) / log (&n + &1))` THEN
    MP_TAC(GEN `n:num` (ISPECL
     [`\z. Cx(&1) / clog(z + Cx(&1)) - Cx(&1) / (clog(z + Cx(&1))) pow 2`;
      `\z. (z + Cx(&1)) / clog(z + Cx(&1))`;
      `16`; `n:num`]
     SUM_INTEGRAL_BOUNDS_DECREASING)) THEN
    MATCH_MP_TAC(MESON[]
     `(!n. P n ==> Q n) /\ ((!n. P n ==> R n) ==> s)
      ==> (!n. P n /\ Q n ==> R n) ==> s`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
        STRIP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        COMPLEX_DIFF_TAC THEN
        REWRITE_TAC[RE_ADD; RE_CX; GSYM CONJ_ASSOC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
         [SUBGOAL_THEN `~(z + Cx(&1) = Cx(&0))` MP_TAC THENL
           [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
          DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN SIMP_TAC[RE_ADD; RE_CX] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
        REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX; REAL_CX;
                     REAL_ARITH `&15 <= z ==> &0 < z + &1`; CX_INJ] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&15 <= y` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX;
                   REAL_ARITH `&15 <= x ==> &0 < x + &1`] THEN
      REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX; GSYM CX_POW] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
      REWRITE_TAC[REAL_ARITH
       `x - x pow 2 <= y - y pow 2 <=>
          (x + y) * (y - x) <= &1 * (y - x)`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= inv(&2) /\ y <= x
        ==> y + x <= &1 /\ &0 <= x - y`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
        CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
        REWRITE_TAC[REAL_MUL_LID] THEN
        DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
        REWRITE_TAC[REAL_MUL_AC];
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
        EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN X_GEN_TAC `n:num` THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `&0 < log(&n + &1)` ASSUME_TAC THENL
         [ALL_TAC; POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD] THEN
        MATCH_MP_TAC LOG_POS_LT THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &1 / log(&k + &1) pow 2 +
                                 &2 / (&k * log(&k + &1))) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ abs(a - b) <= y ==> abs(a - x - b) <= x + y`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `&1 / l - m1 / l * x:real = --((m1 * x - &1) / l)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; ADHOC_BOUND_LEMMA] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &3 / log(&k + &1) pow 2) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ y <= x
      ==> abs(&1 * x + &2 * y) <= &3 * x`) THEN
    SUBGOAL_THEN `&0 < log(&m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_MP_TAC LOG_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC REALLIM_MUL_SERIES_LIM THEN
  MAP_EVERY EXISTS_TAC
   [`\n. &1 / log(&n + &1) - &1 / log(&n + &1) pow 2`; `&1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LID; REAL_SUB_LT] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    SUBGOAL_THEN `&1 < log(&n + &1)`
     (fun th -> SIMP_TAC[th; REAL_ARITH `&1 < x ==> &0 < x`; REAL_SUB_LT;
             REAL_LT_MUL; REAL_ARITH `x < x pow 2 <=> &0 < x * (x - &1)`]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE;
             REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`];
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
    REWRITE_TAC[REAL_INV_DIV; GSYM REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &2 / log(&n + &1)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_1_OVER_LOG)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `42` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 < log(&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_INV; REAL_ABS_POW;
               REAL_ARITH `&2 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT;
               REAL_ARITH `&2 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&2 < l ==> (inv(l) * &2) * l pow 2 = inv(inv(&2 * l))`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_MUL; real_div; GSYM REAL_POW_INV; REAL_MUL_LID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `l pow 2 <= l / &2
    ==> inv(&2) * l <= abs(l - l pow 2)`) THEN
  REWRITE_TAC[REAL_ARITH `l pow 2 <= l / &2 <=> &0 <= (&1 / &2 - l) * l`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_SUB_LE;
               ARITH_RULE `&2 < x ==> &0 <= x`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
The limit, as `n` tends to infinity, of the ratio of the number of primes less than or equal to `n` to `n` divided by the natural logarithm of `n`, is equal to 1. Formally:
```
limit (as n -> infinity) of (cardinality of {p | p is prime and p <= n}) / (n / log(n)) = 1
```

### Informal sketch
The proof of the Prime Number Theorem (`PNT`) proceeds as follows:

- The proof begins by rewriting the goal using `PNT_PARTIAL_SUMMATION`, `SUM_PARTIAL_PRE`, and some arithmetic simplifications.
- It is shown that the set `{p | prime p /\ p = 0}` is empty.
- Several rewriting steps are performed using `SUM_CLAUSES`, `REAL_MUL_RZERO`, and `REAL_SUB_RZERO`.
- An initial transformation using `REALLIM_TRANSFORM_EVENTUALLY` introduces a complicated expression.
- This is followed by another transformation via `REALLIM_TRANSFORM` involving `log(n)`.
- A key step involves rewriting and applying `SUM_PARTIAL_LIMIT_ALT`.
- The limit is split into separate components, and the complex mean value theorem (`COMPLEX_MVT_LINE`) is applied.
- Several simplifications and arithmetic rearrangements are performed to prepare for bounding arguments.
- The Merten's limit `MERTENS_LIMIT`, `REALLIM_LOG_OVER_N`, and relevant inequalities are invoked.
- A decreasing sum is bounded by an integral `SUM_INTEGRAL_BOUNDS_DECREASING`.
- The proof reduces to showing several inequalities and applying limit results (`REALLIM_MUL_SERIES_LIM`, `REALLIM_1_OVER_LOG`, `REALLIM_NULL_COMPARISON`).

### Mathematical insight
The Prime Number Theorem is a fundamental result in number theory that describes the asymptotic distribution of prime numbers. It states that the number of primes less than or equal to a given number `n` is approximately `n / log(n)` for large `n`. This theorem provides a deep connection between the primes and the continuous logarithm function. The proof is complex and relies on methods from real and complex analysis.

### Dependencies
- `PNT_PARTIAL_SUMMATION`
- `SUM_PARTIAL_PRE`
- `REAL_OF_NUM_ADD`
- `LE`
- `EXTENSION`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`
- `PRIME_IMP_NZ`
- `SUM_CLAUSES`
- `REAL_MUL_RZERO`
- `REAL_SUB_RZERO`
- `REALLIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `REALLIM_TRANSFORM`
- `SUM_SUB_NUMSEG`
- `REAL_SUB_RDISTRIB`
- `SUM_PARTIAL_LIMIT_ALT`
- `MERTENS_LIMIT`
- `REAL_INV_DIV`
- `REAL_LT_DIV`
- `LOG_POS_LT`
- `REAL_OF_NUM_LT`
- `LOG_POS`
- `REAL_ARITH`
- `REALLIM_LOG_OVER_N`
- `REALLIM_LOG_OVER_LOG1`
- `REALLIM_NA_OVER_N`
- `REALLIM_MUL`
- `REAL_MUL_LID`
- `REAL_ADD_ASSOC`
- `COMPLEX_MVT_LINE`
- `IN_SEGMENT_CX_GEN`
- `COMPLEX_DIFF_TAC`
- `CONJ_ASSOC`
- `COMPLEX_EQ`
- `RE_CX`
- `IM_CX`
- `REAL`
- `CX_LOG`
- `CX_INJ`
- `REAL_LT_IMP_NZ`
- `LOG_POS_LT`
- `CX_POW`
- `CX_INV`
- `CX_SUB`
- `CX_DIV`
- `CX_MUL`
- `REAL_SUB_LE`
- `REAL_ADD_SUB`
- `REAL_MUL_RID`
- `REAL_LE_LMUL`
- `LOG_2_BOUNDS`
- `LOG_POW`
- `LOG_MONO_LE_IMP`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_ADD`
- `SUM_PARTIAL_SUC`
- `ADD1`
- `SUM_CLAUSES_NUMSEG`
- `REAL_OF_NUM_SUC`
- `REAL_SEQ_OFFSET_REV`
- `REAL_SEQ_OFFSET`
- `REALLIM_ADD`
- `REALLIM_CONST`
- `REALLIM_NULL_LMUL`
- `REAL_INV_DIV`
- `REALLIM_NULL_COMPARISON`
- `SUM_INTEGRAL_BOUNDS_DECREASING`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `SUM_ABS_LE`
- `ADHOC_BOUND_LEMMA`
- `REAL_POS`
- `REAL_LT_IMP_LE`
- `REAL_POW_2`
- `REAL_LE_INV2`
- `REAL_ADD_SYM`
- `LOG_LE`
- `SUM_LMUL`
- `REAL_MUL_ASSOC`
- `REALLIM_MUL_SERIES_LIM`
- `REAL_SUB_LT`
- `REAL_LT_INV2`
- `REAL_LET_TRANS`
- `LOG_MONO_LT_IMP`
- `EVENTUALLY_SEQUENTIALLY`
- `REAL_POW_LT`
- `SUM_COMBINE_R`
- `TAUT`
- `REAL_INV_MUL`

### Porting notes (optional)
- The heavy reliance on tactics like `ASM_SIMP_TAC` indicates the formal proof involves a lot of equational reasoning and simplification in real arithmetic, which will likely be tedious to replicate manually in other proof assistants.
- The use of `COMPLEX_MVT_LINE` suggests that complex analysis is used, and support for this might be needed.
- The dependencies should be checked carefully to make sure they are available or can be constructed.


---

