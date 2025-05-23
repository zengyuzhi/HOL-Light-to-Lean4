# leibniz.ml

## Overview

Number of statements: 10

The `leibniz.ml` file formalizes Leibniz's series for pi, a mathematical concept for approximating the value of pi. It imports `transc.ml` from the Library, indicating a connection to transcendental functions. The file's purpose is to define and prove properties related to Leibniz's series, contributing to the library's collection of mathematical theories and concepts. Its content is focused on this specific series expansion, providing a formal foundation for reasoning about pi in the HOL Light system.

## ALTERNATING_SUM_BOUNDS

### Name of formal statement
ALTERNATING_SUM_BOUNDS

### Type of the formal statement
Theorem

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
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC])
```

### Informal statement
For all sequences `a`, if for all natural numbers `n`, `a(2n + 1)` is less than or equal to `0` and `0` is less than or equal to `a(2n)`, and if for all `n`, the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)`, then for all natural numbers `m` and `n`, if `m` is even, `0` is less than or equal to the sum from `m` to `n` of `a` and the sum from `m` to `n` of `a` is less than or equal to `a(m)`, and if `m` is odd, `a(m)` is less than or equal to the sum from `m` to `n` of `a` and the sum from `m` to `n` of `a` is less than or equal to `0`.

### Informal sketch
* The proof starts by assuming the conditions on the sequence `a` and then proceeds by induction.
* It first considers the case when `m` is even and then when `m` is odd, utilizing the properties of even and odd numbers, and the definition of the sum.
* The `INDUCT_TAC` and `X_GEN_TAC` tactics are used to set up the inductive step and to introduce the variable `m`.
* The proof then applies various rewrite rules, such as `SWAP_FORALL_THM`, `ODD`, `EVEN`, and `SUM_SPLIT`, to simplify the expressions and apply the given conditions on `a`.
* The `ASM_CASES_TAC` is used to split the proof into cases based on whether `m` is even or odd, and then further reasoning is applied to each case, including the use of `REAL_ARITH_TAC` for real arithmetic reasoning.

### Mathematical insight
This theorem provides bounds for the sum of an alternating series under certain conditions on the sequence `a`. The conditions imply that the terms of the sequence alternate in sign and decrease in absolute value, which are key properties for the convergence of an alternating series. The theorem then gives bounds for the sum of the series, which can be useful in various mathematical and computational contexts.

### Dependencies
* Theorems:
  + `SWAP_FORALL_THM`
  + `ODD_EXISTS`
  + `EVEN_EXISTS`
  + `LEFT_IMP_EXISTS_THM`
  + `REAL_LE_REFL`
  + `SUM_1`
  + `NOT_EVEN`
* Definitions:
  + `sum`
  + `EVEN`
  + `ODD`
  + `abs`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of binders, quantifiers, and the `SUM` function, as these may be represented differently in the target system. Additionally, the `REAL_ARITH_TAC` tactic may need to be replaced with a corresponding tactic in the target system for real arithmetic reasoning.

---

## ALTERNATING_SUM_BOUND

### Name of formal statement
ALTERNATING_SUM_BOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ALTERNATING_SUM_BOUND = prove
 (`!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. abs(sum(m,n) a) <= abs(a m)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALTERNATING_SUM_BOUNDS) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN m` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `a`, if for all natural numbers `n`, `a(2n + 1)` is less than or equal to `0` and `0` is less than or equal to `a(2n)`, and for all `n`, the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)`, then for all natural numbers `m` and `n`, the absolute value of the sum from `m` to `n` of `a` is less than or equal to the absolute value of `a(m)`.

### Informal sketch
* The proof starts by assuming the given conditions about the function `a`, specifically the alternating bounds and the decreasing absolute values of successive terms.
* It then applies the `ALTERNATING_SUM_BOUNDS` theorem to establish a bound on the sum of the terms of `a`.
* The proof proceeds by considering all `m` and `n` and analyzing the sum from `m` to `n` of `a`.
* It uses `GEN_TAC` to generalize over all `m` and `n`, and `DISCH_THEN` combined with `MATCH_MP` to apply the `ALTERNATING_SUM_BOUNDS` theorem.
* The `REPEAT` and `MATCH_MP_TAC` tactics are used to handle the universal quantification and apply the `MONO_FORALL` rule.
* The proof then considers the case when `m` is even using `ASM_CASES_TAC` and simplifies using `ASM_REWRITE_TAC` and `REAL_ARITH_TAC`.

### Mathematical insight
This theorem provides a bound on the absolute value of the sum of terms of a sequence `a` that satisfies certain alternating bounds and has decreasing absolute values. It's a useful result in mathematical analysis, particularly in the study of series and sequences, as it gives a way to control the sum of a sequence based on the properties of its terms.

### Dependencies
* `ALTERNATING_SUM_BOUNDS`
* `MONO_FORALL`

### Porting notes
When translating this theorem into another proof assistant, special care should be taken with the handling of the `GEN_TAC` and `DISCH_THEN` tactics, as well as the application of `MATCH_MP` and `MONO_FORALL`. The `REAL_ARITH_TAC` tactic may also require special handling depending on the target system's support for real arithmetic. Additionally, the `ASM_CASES_TAC` and `ASM_REWRITE_TAC` tactics may need to be adapted based on the target system's case analysis and rewriting mechanisms.

---

## SUMMABLE_ALTERNATING

### Name of formal statement
SUMMABLE_ALTERNATING

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[ALTERNATING_SUM_BOUND; REAL_LET_TRANS])
```

### Informal statement
For all sequences `a`, if for all natural numbers `n`, `a(2n + 1)` is less than or equal to `0` and `0` is less than or equal to `a(2n)`, and for all `n`, the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)`, and `a` converges to `0` in the real numbers, then `a` is summable.

### Informal sketch
* The proof starts by assuming the given conditions about the sequence `a`.
* It then uses the `SER_CAUCHY` theorem to relate the summability of `a` to the Cauchy criterion.
* The proof proceeds by assuming an arbitrary positive real number `e` and deriving a bound on the sum of the sequence `a` using the `ALTERNATING_SUM_BOUND` theorem.
* The `MONO_EXISTS` tactic is used to establish the existence of a natural number `N` such that for all `n` greater than `N`, the sum of the sequence `a` from `n` to infinity is less than `e`.
* The final steps involve rewriting and simplifying the expression to establish the summability of `a`.

### Mathematical insight
This theorem establishes a sufficient condition for the summability of an alternating series. The condition involves the sequence having terms that alternate in sign, decrease in absolute value, and converge to `0`. This theorem is important because it provides a useful criterion for determining the convergence of series, particularly in the context of real analysis.

### Dependencies
* Theorems:
  * `SER_CAUCHY`
  * `ALTERNATING_SUM_BOUND`
  * `MONO_EXISTS`
* Definitions:
  * `summable`
  * `tends_num_real`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the sequence `a` is properly defined and that the `SER_CAUCHY` and `ALTERNATING_SUM_BOUND` theorems are available or can be derived. Additionally, the `MONO_EXISTS` tactic may need to be replaced with an equivalent tactic or construction in the target proof assistant.

---

## REAL_ATN_POWSER_ALT

### Name of formal statement
REAL_ATN_POWSER_ALT

### Type of the formal statement
Theorem

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
  SIMP_TAC[DIV_MULT; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_LID])
```

### Informal statement
For all real numbers x, if the absolute value of x is less than 1, then the series `(-1)^n / (2n + 1) * x^(2n + 1)` converges to the arctangent of x.

### Informal sketch
* The proof starts by assuming `abs(x) < 1`, which is a crucial constraint for the convergence of the series.
* It then invokes the `REAL_ATN_POWSER` theorem to establish a relationship between the series and the arctangent function.
* The `SUM_SUMMABLE` theorem is used to show that the series is summable, given the constraint on x.
* The proof then applies the `SER_GROUP` theorem to group terms in the series, followed by `SUM_UNIQ` to establish uniqueness of the sum.
* The `REWRITE_TAC` and `SIMP_TAC` tactics are used to simplify the expression and apply various arithmetic and real number properties.
* Key steps involve recognizing the series as an alternating series and applying properties of even and odd numbers.

### Mathematical insight
This theorem provides an alternative representation of the arctangent function as an infinite series, which is essential in mathematical analysis and calculus. The series expansion allows for the computation of arctangent values and is a fundamental result in the study of trigonometric functions.

### Dependencies
* Theorems:
  * `REAL_ATN_POWSER`
  * `SUM_SUMMABLE`
  * `SER_GROUP`
  * `SUM_UNIQ`
* Definitions:
  * `atn` (arctangent function)
  * `sums` (series convergence)
* Axioms and rules:
  * `REPEAT`
  * `STRIP_TAC`
  * `ASSUME_TAC`
  * `MATCH_MP`
  * `MP_TAC`
  * `CONJ`
  * `ARITH_RULE`
  * `REWRITE_TAC`
  * `SIMP_TAC`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of series convergence and the properties of real numbers. The `SUM_SUMMABLE` and `SER_GROUP` theorems may require special attention, as their equivalents in other systems might have different names or requirements. Additionally, the use of `REPEAT` and `STRIP_TAC` tactics might need to be adapted to the target system's proof scripting language.

---

## SUMMABLE_LEIBNIZ

### Name of formal statement
SUMMABLE_LEIBNIZ

### Type of the formal statement
Theorem

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
    ASM_ARITH_TAC])
```

### Informal statement
The series `∑[n=0 to ∞] ((-1)^n) / (2n + 1)` is summable.

### Informal sketch
* The proof involves applying the `SUMMABLE_ALTERNATING` theorem to establish the summability of the given series.
* It first rewrites the series using properties of real numbers, such as `REAL_POW_ADD`, `REAL_POW_MUL`, and `GSYM REAL_POW_POW`.
* The proof then proceeds by cases, using `REPEAT CONJ_TAC` to split the goal into multiple subgoals.
* In one branch, it applies `MATCH_MP_TAC REAL_LE_INV2` to establish a bound on the terms of the series.
* In another branch, it uses `MATCH_MP_TAC MONO_EXISTS` to show the existence of a limit for the series.
* The proof also employs various simplification and arithmetic tactics, such as `REWRITE_TAC`, `CONV_TAC`, and `ARITH_TAC`, to manipulate and simplify expressions.
* Key `HOL Light` terms used include `SUMMABLE_ALTERNATING`, `REAL_POW_ADD`, `REAL_POW_MUL`, `REAL_LE_INV2`, and `MONO_EXISTS`.

### Mathematical insight
The `SUMMABLE_LEIBNIZ` theorem establishes the summability of the Leibniz series for π, which is a fundamental result in mathematics. The series is an alternating series, and the proof relies on the `SUMMABLE_ALTERNATING` theorem to establish its summability. The theorem is important because it provides a way to compute π using an infinite series, which is a key result in mathematics and computer science.

### Dependencies
#### Theorems
* `SUMMABLE_ALTERNATING`
* `REAL_LE_INV2`
* `MONO_EXISTS`
* `REAL_ARCH`
#### Definitions
* `summable`
* `REAL_POW_ADD`
* `REAL_POW_MUL`
* `GSYM REAL_POW_POW`
* `REAL_LE_LNEG`
* `REAL_ADD_RID`
* `REAL_LE_INV_EQ`
* `REAL_POS`
* `REAL_ABS_DIV`
* `REAL_ABS_POW`
* `REAL_ABS_NEG`
* `REAL_ABS_NUM`
* `REAL_POW_ONE`
* `real_div`
* `REAL_MUL_LID`
* `REAL_MUL_LNEG`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the corresponding theorems and definitions are available. In particular, the `SUMMABLE_ALTERNATING` theorem and the various `REAL_` definitions and theorems may need to be ported or redefined. Additionally, the use of `MATCH_MP_TAC` and `REPEAT CONJ_TAC` may need to be adapted to the target proof assistant's tactic language.

---

## SUM_DIFFERENCES

### Name of formal statement
SUM_DIFFERENCES

### Type of the formal statement
Theorem

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
  REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `a` and for all integers `m` and `n` such that `m` is less than or equal to `n + 1`, the sum from `m` to `n` of `a(i) - a(i+1)` is equal to `a(m) - a(n + 1)`.

### Informal sketch
* The proof starts by generalizing over `m` and `n` using `GEN_TAC`, and then applies induction using `INDUCT_TAC`.
* The base case involves rewriting the condition `m <= 0 + 1` to `m = 0 \/ m = 1` using `ARITH_RULE`, and then simplifying the sum using `SUM_SING_NUMSEG` and `SUM_TRIV_NUMSEG`.
* The inductive step involves rewriting the condition `m <= SUC n + 1` to `m <= n + 1 \/ m = SUC n + 1` using `ARITH_RULE`, and then simplifying the sum using `SUM_CLAUSES_NUMSEG` and `REAL_ARITH_TAC`.
* Key steps involve simplifying the sum using `ASM_SIMP_TAC` and `ASM_REWRITE_TAC`, and applying `REAL_ARITH_TAC` to finalize the proof.

### Mathematical insight
This theorem provides a way to simplify sums of differences of a function `a` over a range, by reducing it to a simple difference of the function values at the endpoints. This can be useful in a variety of mathematical contexts, such as in the analysis of sequences or series.

### Dependencies
* `ARITH_RULE`
* `SUM_SING_NUMSEG`
* `SUM_TRIV_NUMSEG`
* `SUM_CLAUSES_NUMSEG`
* `REAL_SUB_REFL`
* `ADD1`
* `GEN_TAC`
* `INDUCT_TAC`
* `REWRITE_TAC`
* `STRIP_TAC`
* `ASM_REWRITE_TAC`
* `ASM_SIMP_TAC`
* `REAL_ARITH_TAC`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of arithmetic rules and the `SUM` function, as these may be implemented differently. Additionally, the use of `INDUCT_TAC` and `GEN_TAC` may need to be adapted to the specific proof assistant's syntax and tactics.

---

## SUM_REARRANGE_LEMMA

### Name of formal statement
SUM_REARRANGE_LEMMA

### Type of the formal statement
Theorem

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
  REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `a` and `v`, and for all integers `m` and `n` such that `m` is less than or equal to `n + 1`, the following equation holds: the sum from `m` to `n+1` of `a(i) * v(i)` equals the sum from `m` to `n` of the sum from `m` to `k` of `a` times `v(k) - v(k+1)` plus the sum from `m` to `n+1` of `a` times `v(n+1)`.

### Informal sketch
* The proof starts by assuming `m <= n + 1` and then proceeds by induction.
* It first checks the base case when `m = 0` and performs arithmetic simplifications.
* Then, it considers the case when `m` is not equal to `0` and applies the inductive hypothesis.
* The proof involves several rewriting steps using `SUM_CLAUSES_NUMSEG`, `ADD_CLAUSES`, and `REAL_ARITH_TAC` to simplify the summations and arithmetic expressions.
* Key steps include using `ANTS_TAC` to handle the inductive case and `DISCH_THEN SUBST1_TAC` to substitute the inductive hypothesis into the current goal.
* The proof also involves case analysis on `m = SUC(n + 1)` and uses `REAL_ARITH_TAC` to finalize the arithmetic simplifications.

### Mathematical insight
This theorem provides a rearrangement formula for sums involving products of functions `a` and `v`. The formula allows expressing a sum of products as a combination of sums of `a` and differences of `v`, which can be useful in various mathematical derivations, particularly in calculus and analysis. The theorem's conditions, `m <= n + 1`, ensure the validity of the rearrangement.

### Dependencies
* `SUM_CLAUSES_NUMSEG`
* `ADD_CLAUSES`
* `REAL_ARITH_TAC`
* `INDUCT_TAC`
* `REPLICATE_TAC`
* `GEN_TAC`
* `DISCH_TAC`
* `FIRST_X_ASSUM`
* `MP_TAC`
* `check`
* `is_imp`
* `concl`
* `ANTS_TAC`
* `ASM_ARITH_TAC`
* `REAL_ADD_ASSOC`
* `REAL_EQ_ADD_LCANCEL`
* `REAL_ADD_RDISTRIB`
* `REAL_EQ_ADD_RCANCEL`
* `GSYM`
* `ADD1`
* `SUM_CMUL`
* `SUM_ADD_NUMSEG`
* `REAL_SUB_ADD`
* `REAL_SUB_RDISTRIB`
* `REAL_MUL_SYM`
* `REAL_ADD_LDISTRIB`
* `GSYM SUM_CMUL`
* `GSYM SUM_ADD_NUMSEG`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to the handling of binders, summation notation, and arithmetic. The `SUM_REARRANGE_LEMMA` involves complex manipulations of summations and arithmetic expressions, which may require careful translation to ensure that the formal statement and its proof are correctly represented in the target system. Additionally, the use of `REAL_ARITH_TAC` and other arithmetic tactics may need to be adapted to the target system's arithmetic reasoning capabilities.

---

## SUM_BOUNDS_LEMMA

### Name of formal statement
SUM_BOUNDS_LEMMA

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[REAL_SUB_LE; ARITH_RULE `k <= n ==> k <= n + 1`])
```

### Informal statement
For all functions `a` and `v`, and for all real numbers `l` and `u`, and for all natural numbers `m` and `n` such that `m` is less than or equal to `n`, if for all `i` between `m` and `n` (inclusive), `0` is less than or equal to `v(i)` and `v(i+1)` is less than or equal to `v(i)`, and for all `k` between `m` and `n` (inclusive), `l` is less than or equal to the sum from `m` to `k` of `a(i)` and the sum from `m` to `k` of `a(i)` is less than or equal to `u`, then `l` times `v(m)` is less than or equal to the sum from `m` to `n` of `a(i)` times `v(i)`, and the sum from `m` to `n` of `a(i)` times `v(i)` is less than or equal to `u` times `v(m)`.

### Informal sketch
* The proof starts by assuming the given conditions and using `INDUCT_TAC` to perform induction.
* It then applies various simplification and rewriting tactics, including `REWRITE_TAC` for `LE` and `SUM_CLAUSES_NUMSEG`, and `SIMP_TAC` for arithmetic rules.
* The proof proceeds by cases, including when `m` equals `0`, and uses `ASM_CASES_TAC` and `ASM_REWRITE_TAC` for `SUM_SING_NUMSEG`.
* It applies `MATCH_MP_TAC` for `REAL_LE_TRANS` and `SUM_LE_NUMSEG`, and uses `X_GEN_TAC` to introduce a new variable `k`.
* The proof involves several applications of `CONJ_TAC` and `ASM_SIMP_TAC` to simplify and rearrange terms, including `SUM_LMUL` and `SUM_DIFFERENCES`.
* Key steps involve using `REAL_LE_RMUL` and `LE_REFL` to establish the desired inequalities.

### Mathematical insight
This theorem provides bounds on a weighted sum of a sequence `a(i)` with weights `v(i)`, given certain conditions on the sequence `v(i)` and the sum of `a(i)` over various intervals. The conditions on `v(i)` require it to be non-negative and non-increasing, and the conditions on the sum of `a(i)` require it to be bounded by `l` and `u`. The theorem then establishes that the weighted sum is bounded by `l` times `v(m)` and `u` times `v(m)`, where `m` is the starting index of the sum.

### Dependencies
* Theorems:
  + `REAL_LE_TRANS`
  + `SUM_LE_NUMSEG`
  + `REAL_LE_ADD2`
  + `SUM_REARRANGE_LEMMA`
* Definitions:
  + `SUM_CLAUSES_NUMSEG`
  + `SUM_SING_NUMSEG`
  + `SUM_LMUL`
  + `SUM_DIFFERENCES`
* Axioms and rules:
  + `ARITH_RULE`
  + `LEFT_FORALL_IMP_THM`
  + `RIGHT_EXISTS_AND_THM`
  + `EXISTS_REFL`
  + `LE_REFL`
  + `REAL_LE_RMUL`
  + `REAL_SUB_LE`

---

## SUM_BOUND_LEMMA

### Name of formal statement
SUM_BOUND_LEMMA

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[REAL_BOUNDS_LE])
```

### Informal statement
For all functions `a` and `v`, and for all real numbers `b`, `m`, and `n`, if `m` is less than or equal to `n`, and for all `i` such that `m` is less than or equal to `i` and `i` is less than or equal to `n`, `v(i)` is non-negative and `v(i+1)` is less than or equal to `v(i)`, and for all `k` such that `m` is less than or equal to `k` and `k` is less than or equal to `n`, the absolute value of the sum from `m` to `k` of `a` is less than or equal to `b`, then the absolute value of the sum from `m` to `n` of `a(i)` times `v(i)` is less than or equal to `b` times the absolute value of `v(m)`.

### Informal sketch
* The proof starts by assuming the given conditions: `m` is less than or equal to `n`, and the properties of `v` and the sum of `a` hold.
* It then applies `REAL_ARITH` to establish a bound on the absolute value of a quantity, using the given condition on `a` and `b`.
* The `ASM_SIMP_TAC` tactic is used to simplify the expression using `LE_REFL` and `real_abs`.
* The proof then applies `MATCH_MP_TAC` with `SUM_BOUNDS_LEMMA` to establish a bound on the sum of `a` times `v`.
* Finally, `ASM_REWRITE_TAC` is used with `REAL_BOUNDS_LE` to rewrite the expression and complete the proof.
* Key steps involve using the `SUM_BOUNDS_LEMMA` to establish the bound on the sum, and applying `REAL_ARITH` to simplify the absolute value expression.

### Mathematical insight
This theorem provides a bound on the absolute value of a weighted sum, given bounds on the individual terms and a non-increasing weight function `v`. The key idea is to use the given bounds on `a` and `v` to establish a bound on the weighted sum, by applying the `SUM_BOUNDS_LEMMA` and simplifying the expression using `REAL_ARITH` and `REAL_BOUNDS_LE`. This theorem is likely useful in establishing bounds on quantities in mathematical analysis, particularly in cases where a non-increasing weight function is involved.

### Dependencies
* Theorems:
 + `REAL_ARITH`
 + `SUM_BOUNDS_LEMMA`
* Definitions:
 + `real_abs`
 + `LE_REFL`
 + `REAL_BOUNDS_LE`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `REAL_ARITH` and `SUM_BOUNDS_LEMMA` theorems are properly translated, as they are crucial to the proof. Additionally, the `ASM_SIMP_TAC` and `ASM_REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant, taking into account any differences in the handling of binders or automation.

---

## LEIBNIZ_PI

### Name of formal statement
LEIBNIZ_PI

### Type of the formal statement
Theorem

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
  ASM_REAL_ARITH_TAC)
```

### Informal statement
The theorem `LEIBNIZ_PI` states that the infinite series `∑[n=0 to ∞] ((-1)^n) / (2n + 1)` converges to `π / 4`. This series is a well-known expansion for the arctangent function `atn(1)`.

### Informal sketch
* The proof begins by assuming the summability of the series `∑[n=0 to ∞] ((-1)^n) / (2n + 1)` using `SUMMABLE_LEIBNIZ`.
* It then defines `s` as the sum of this series and `e` as the absolute difference between `s` and `atn(1)`.
* The proof proceeds by showing that `s` is equal to `atn(1)` using `REAL_ARITH` and `MATCH_MP`.
* It then uses `DIFF_CONT` and `DIFF_ATN` to establish the continuity of the series at `x = 1`.
* The proof also employs `REAL_ATN_POWSER_ALT` to relate the series to the arctangent function.
* The main stages of the proof involve:
  + Establishing the summability of the series
  + Defining `s` and `e`
  + Showing `s = atn(1)`
  + Using continuity and arctangent properties to derive the final result
* Key tactics include `MATCH_MP_TAC`, `REWRITE_TAC`, `ASSUME_TAC`, and `SUBGOAL_THEN`.

### Mathematical insight
This theorem provides a formal proof of the convergence of the Leibniz series for `π`, which is a fundamental result in mathematics. The series `∑[n=0 to ∞] ((-1)^n) / (2n + 1)` is a well-known expansion for the arctangent function `atn(1)`, and its convergence to `π / 4` is a classic result in mathematics.

### Dependencies
* Theorems:
  + `SUMMABLE_LEIBNIZ`
  + `REAL_ARITH`
  + `DIFF_CONT`
  + `DIFF_ATN`
  + `REAL_ATN_POWSER_ALT`
* Definitions:
  + `atn`
  + `suminf`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of infinite series, continuity, and the arctangent function. The `SUMMABLE_LEIBNIZ` theorem and `REAL_ATN_POWSER_ALT` may require special care, as they involve subtle properties of series and functions. Additionally, the use of `MATCH_MP_TAC` and `REWRITE_TAC` tactics may need to be adapted to the target proof assistant's tactic language.

---

