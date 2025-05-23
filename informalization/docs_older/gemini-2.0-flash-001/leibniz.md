# leibniz.ml

## Overview

Number of statements: 10

`leibniz.ml` formalizes Leibniz's series for π. It resides within a library containing transcendental functions, as indicated by its import of `transc.ml`. The file likely proves the convergence of the Leibniz series and establishes its equality to π/4.


## ALTERNATING_SUM_BOUNDS

### Name of formal statement
ALTERNATING_SUM_BOUNDS

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
For any sequence `a` of real numbers, if the following conditions hold:
1. For all natural numbers `n`, `a(2 * n + 1)` is less than or equal to 0 and 0 is less than or equal to `a(2 * n)`.
2. For all natural numbers `n`, the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)`.

Then, for all natural numbers `m` and `n`, the following implications hold:
1. If `m` is even, then 0 is less than or equal to the sum from `m` to `n` of `a`, and the sum from `m` to `n` of `a` is less than or equal to `a(m)`.
2. If `m` is odd, then `a(m)` is less than or equal to the sum from `m` to `n` of `a`, and the sum from `m` to `n` of `a` is less than or equal to 0.

### Informal sketch
The proof proceeds by induction on `n`.

*   **Base Case:** The base case involves showing that the theorem holds when `n = m`. This reduces to showing `0 <= a(m) /\ a(m) <= a(m)` when `m` is even, and `a(m) <= a(m) /\ a(m) <= 0` when `m` is odd. This is handled by `sum`, `ODD_EXISTS`, `EVEN_EXISTS`, `LEFT_IMP_EXISTS_THM`, `ADD1` and `REAL_LE_REFL`.
*   **Inductive Step:** Assume the theorem holds for some `n`. The goal is to prove it for `SUC n = n + 1`.
    *   The sum from `m` to `n + 1` is split into the sum from `m` to `n` plus `a(SUC n)` using `SUM_SPLIT`.
    *   The inductive hypothesis is applied to the sum from `m` to `n`.
    *   Cases are then split based on whether `m` is even or odd. The definitions of `ODD` and `EVEN` as well as `SUM_1` are applied.
    *   An assumption about the absolute values `!n. abs(a(n+1)) <= abs(a n)` along with a case split using `ASM_CASES_TAC` on `EVEN m` is used.
    *   Real arithmetic (`REAL_ARITH_TAC`) is then used to complete the inductive step.

### Mathematical insight
This theorem provides bounds for the partial sums of an alternating sequence. The conditions ensure that the terms of the sequence alternate in sign and decrease in absolute value. Under these conditions, the partial sums oscillate around zero, and the theorem gives upper and lower bounds for these partial sums depending on whether the starting index `m` is even or odd. This result is useful for determining the convergence of alternating series, and bounding the truncation error.

### Dependencies
*   Definitions: `sum`, `ODD`, `EVEN`
*   Theorems: `ODD_EXISTS`, `EVEN_EXISTS`, `LEFT_IMP_EXISTS_THM`, `ADD1`, `REAL_LE_REFL`, `ARITH_RULE` (specifically `SUC n = 1 + n`), `SUM_SPLIT`, `SUM_1`, `NOT_EVEN`, `EVEN_EXISTS`

### Porting notes (optional)
*   The proof relies heavily on the `REAL_ARITH_TAC`, which incorporates real number arithmetic. The equivalent tactic must be available in the target proof assistant.
*   The use of `ASM_CASES_TAC` is used to split the proof based on whether `m` is even or odd. Similar case-splitting tactics are available in other proof assistants.
*   The tactic `DISCH_THEN(X_CHOOSE_THEN ... SUBST_ALL_TAC)` is a common idiom in HOL Light for instantiating an existentially quantified variable. This needs to be translated into equivalent commands in the target proof assistant.


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
For all sequences `a`, if the sequence `a` is alternating such that for all natural numbers `n`, `a(2 * n + 1) <= 0` and `0 <= a(2 * n)`, and if the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)` for all natural numbers `n`, then for all natural numbers `m` and `n`, the absolute value of the sum of `a(i)` from `i = m` to `n` is less than or equal to the absolute value of `a(m)`.

### Informal sketch
The proof proceeds as follows:
- Assume the alternating condition on `a`: `!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)` and the decreasing absolute value condition `!n. abs(a(n + 1)) <= abs(a(n))`.
- Apply `ALTERNATING_SUM_BOUNDS` to obtain a preliminary result.
- Generalize the quantified variables `m` and `n`.
- Rewrite using the fact that `NOT_EVEN` equals `ODD`.
- Perform a case split on whether `m` is even (`EVEN m`).
- In each case, simplify using assumptions and then apply real arithmetic (`REAL_ARITH_TAC`) to complete each sub-goal.

### Mathematical insight
This theorem provides a bound on the partial sums of an alternating sequence. It states that under the assumption of decreasing absolute values and alternating signs, the absolute value of any partial sum is bounded by the absolute value of the first term in the sum. The alternating series test relies on this bound.

### Dependencies
- `ALTERNATING_SUM_BOUNDS`
- `MONO_FORALL`
- `NOT_EVEN`

### Porting notes (optional)
The `REAL_ARITH_TAC` tactic in HOL Light uses a decision procedure for linear real arithmetic, which may need to be replaced by a suitable tactic or manual proof steps in other systems. Specifically, the properties of absolute values and sums will need to be carefully applied.


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
For any sequence of real numbers `a`, if the sequence satisfies the following conditions:
1. For all natural numbers `n`, `a(2 * n + 1)` is less than or equal to 0, and 0 is less than or equal to `a(2 * n)`.
2. For all natural numbers `n`, the absolute value of `a(n + 1)` is less than or equal to the absolute value of `a(n)`.
3. The sequence `a` converges to 0,
then the sequence `a` is summable.

### Informal sketch
The proof proceeds as follows:
- Assume that the sequence `a` satisfies the alternating condition (`!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)`), the decreasing absolute value condition (`!n. abs(a(n + 1)) <= abs(a(n))`), and converges to 0 (`a tends_num_real &0`).
- Apply the Cauchy criterion for summability i.e. `SER_CAUCHY`.
- Introduce a real number `e` to represent an arbitrary positive real number.
- Use an assumption that asserts that for any positive real `e`, there exist `N` such that for all `n >= N`, `|a_n - 0| < e` implies applying the alternating sum bound theorem (`ALTERNATING_SUM_BOUND`) and the real number let transformation (`REAL_LET_TRANS`) to establish the summability of `a`.

### Mathematical insight
The theorem `SUMMABLE_ALTERNATING` formalizes the Leibniz criterion (or alternating series test) for the convergence of an infinite series. It states that if a series has terms that alternate in sign, decrease in absolute value, and converge to zero, then the series converges (is summable). This is a fundamental result in real analysis and is frequently used to determine the summability of series.

### Dependencies
- `SER_CAUCHY`
- `ALTERNATING_SUM_BOUND`
- `REAL_LET_TRANS`


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
For all real numbers `x`, if the absolute value of `x` is less than 1, then the series whose `n`-th term is `(-- 1) pow n / (2 * n + 1) * x pow (2 * n + 1)` sums to `atn x`.
Here, `-- 1` stands for -1 and `atn x` represents the arctangent of `x`.

### Informal sketch
The proof proceeds as follows:
- First, we start with the assumption that the absolute value of `x` is less than 1.
- Next, apply `REAL_ATN_POWSER`, which is the alternating Taylor series expansion for `arctan(x)`.
- Show that the series is summable via `SUM_SUMMABLE` and `ARITH_RULE 0 < 2`.
- Apply `SER_GROUP` to rearrange the series.
- Ensure uniqueness of the sum using `SUM_UNIQ` and `SUBST1_TAC`.
- Simplify the expressions using rewrite rules related to `SUM_2`, `EVEN_MULT`, `EVEN_ADD`, `ARITH_EVEN`, and `ADD_SUB`. Apply an arithmetic rewrite rule `n * 2 = 2 * n`. Finally, simplify the expression using rules for division, multiplication, addition, and zero.

### Mathematical insight
This theorem provides an alternative formulation of the Taylor series expansion for the arctangent function, specifically emphasizing the form suitable for formal manipulation and summation within the HOL Light system. The standard Taylor series for arctangent converges for `|x| < 1`, and this theorem expresses that convergence precisely within the logic.

### Dependencies
- `REAL_ATN_POWSER`
- `SUM_SUMMABLE`
- `SER_GROUP`
- `SUM_UNIQ`
- `SUM_2`
- `EVEN_MULT`
- `EVEN_ADD`
- `ARITH_EVEN`
- `ADD_SUB`
- `DIV_MULT`
- `ARITH_EQ`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `ARITH_RULE`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification. Other proof assistants might require different tactics to achieve the same effect.
- The handling of series and summation might vary in other proof assistants, potentially requiring adjustments to the proof strategy.
- Porting `REAL_ATN_POWSER` is crucial, as this theorem depends on it.


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
The series whose nth term is given by `(-- &1) pow n / &(2 * n + 1)` is summable.

### Informal sketch
The proof proceeds as follows:
- Apply `SUMMABLE_ALTERNATING` to show summability of the series.
- The proof involves verifying the conditions of the alternating series test. This involves showing that the absolute value of the terms decreases monotonically to zero.
- Several rewriting steps are performed to simplify the expression, including using rules related to exponents (`REAL_POW_ADD`, `REAL_POW_MUL`, `REAL_POW_POW`), rational number reduction (`REAL_RAT_REDUCE_CONV`), and basic real number arithmetic (`REAL_MUL_LID`, `REAL_MUL_LNEG`, `REAL_LE_LNEG`, `REAL_ADD_RID`, `REAL_LE_INV_EQ`, `REAL_POS`).
- The monotonicity condition is proved by showing that `abs((-- &1) pow (n + 1) / &(2 * (n + 1) + 1))` is less than `abs((-- &1) pow n / &(2 * n + 1))`. This involves rewriting using absolute values (`REAL_ABS_DIV`, `REAL_ABS_POW`, `REAL_ABS_NEG`, `REAL_ABS_NUM`) and simplifying.
- The limit of the terms converging to zero is shown, involving first proving that for an arbitrary positive real number `e`, there exists some N such that for all `n > N`, `1/(2*n + 1) < e`. This invokes `REAL_ARCH`.
- Finally, a real arithmetic tactic (`REAL_ARITH`) is used to show that for any `x`, with `1< x*e` and `e *x <= y` then `1 < y`. The conditions are simplified using assumptions (`REAL_LE_LMUL_EQ`, `REAL_OF_NUM_LE`) and arithmetic.

### Mathematical insight
This theorem demonstrates the summability of a specific alternating series. The Leibniz formula for `pi/4` can be derived by evaluating the sum of this series. The alternating series test provides a convenient way to establish the summability of such series by checking the decreasing monotonicity and convergence to zero of the absolute values of its terms.

### Dependencies
- `SUMMABLE_ALTERNATING`
- `REAL_POW_ADD`
- `REAL_POW_MUL`
- `REAL_POW_POW`
- `REAL_RAT_REDUCE_CONV`
- `REAL_POW_ONE`
- `real_div`
- `REAL_MUL_LID`
- `REAL_MUL_LNEG`
- `REAL_LE_LNEG`
- `REAL_ADD_RID`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `REAL_ABS_DIV`
- `REAL_ABS_POW`
- `REAL_ABS_NEG`
- `REAL_ABS_NUM`
- `REAL_LE_INV2`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`
- `SEQ`
- `REAL_SUB_RZERO`
- `REAL_LT_LDIV_EQ`
- `REAL_ARCH`
- `MONO_EXISTS`
- `GE`
- `REAL_LE_LMUL_EQ`


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
For any function `a` from natural numbers to real numbers, and any natural numbers `m` and `n`, if `m` is less than or equal to `n + 1`, then the sum of the differences `a(i) - a(i+1)` from `i = m` to `i = n` is equal to `a(m) - a(n + 1)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base Case: `n = 0`.  The condition `m <= n + 1` becomes `m <= 1`, which is equivalent to `m = 0 \/ m = 1`.
    - If `m = 0`, we want to show `sum(0..0) (\i. a(i) - a(i+1)) = a(0) - a(0 + 1)`. This simplifies to `a(0) - a(1) = a(0) - a(1)`, which is true. We use `SUM_SING_NUMSEG` to reduce the sum to a single term and simplify.
    - If `m = 1`, we want to show `sum(1..0) (\i. a(i) - a(i+1)) = a(1) - a(0 + 1)`. `sum(1..0)` is zero and `REAL_SUB_REFL` takes care of simplifying the right hand side to 0 and then proving the goal.
- Inductive Step: Assume the statement holds for `n`. We want to show it holds for `SUC n`.
   The condition `m <= SUC n + 1` is equivalent to `m <= n + 1 \/ m = SUC n + 1`.
   We must show `sum(m..SUC n) (\i. a(i) - a(i+1)) = a(m) - a(SUC n + 1)`.
   We split the sum using `SUM_CLAUSES_NUMSEG` and rewrite using the inductive hypothesis.
   The condition `m <= n + 1` implies both `m <= SUC n` and `m <= SUC n + 1`.
   The inductive step simplifies algebraically using `REAL_ARITH_TAC`.

### Mathematical insight
This theorem provides a closed form for the sum of differences of a function `a`. It is a telescoping sum and a core result in calculus. Its usefulness stems from converting discrete sums over deltas into direct differences of the end points.

### Dependencies
- `SUM_SING_NUMSEG`
- `SUM_TRIV_NUMSEG`
- `SUM_CLAUSES_NUMSEG`
- `ARITH`
- `REAL_SUB_REFL`
- `ADD1`
- `REAL_ARITH_TAC`

### Porting notes (optional)
- The `ARITH_RULE` tactic is specific to HOL Light and may need to be replaced by a different arithmetic simplification tactic or a manual proof step in other proof assistants.
- The automation provided by `REAL_ARITH_TAC` might need to be replicated using field tactics or similar tools in other systems.
- The handling of numerical intervals with `sum` may vary in other proof assistants; ensure compatibility or adapt accordingly.


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
For all functions `a` and `v` from natural numbers to real numbers, and natural numbers `m` and `n`, if `m` is less than or equal to `n + 1`, then the sum from `m` to `n+1` of `a(i) * v(i)` is equal to the sum from `m` to `n` of `(sum from m to k of a) * (v(k) - v(k+1))` plus `(sum from m to n+1 of a) * v(n+1)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n` is a natural number, in the case `m = 0`, the goal is rewritten using basic arithmetic and the definition of `sum`, along with simplification.
- Inductive step: Assume the theorem holds for `n`. We need to prove it for `n+1`. First, split the goal into cases based on whether `m = SUC(n+1)`.
  - If `m = SUC(n+1)`, then the left-hand side and right-hand side of equation are each the single term `a(n+1) * v(n+1)`, so the goal simplifies using the definition of sum over empty segments using `SUM_TRIV_NUMSEG`.
  - If `m <= n+1`, then the hypothesis of the original theorem is rewritten to `m <= SUC(n)` AND `~(m = SUC(n + 1))`.The equation is rewritten using the inductive hypothesis and algebraic identities, rearranging the terms until the left-hand side and right-hand side are equal.

### Mathematical insight
This theorem provides a formula for rearranging a sum of products into a different form, relating it to a sum that involves differences of the `v` function and cumulative sums of the `a` function. It is an analogue of integration by parts.

### Dependencies
- `SUM_CLAUSES_NUMSEG`
- `ADD_CLAUSES`
- `LE_SUC`
- `SUM_TRIV_NUMSEG`
- `REAL_ADD_ASSOC`
- `REAL_EQ_ADD_LCANCEL`
- `REAL_ADD_RDISTRIB`
- `REAL_EQ_ADD_RCANCEL`
- `SUM_CMUL`
- `SUM_ADD_NUMSEG`
- `REAL_SUB_ADD`
- `REAL_SUB_RDISTRIB`
- `REAL_ADD_LDISTRIB`



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
For all natural numbers `a`, `v`, `l`, `u`, `m`, and `n`, if `m` is less than or equal to `n`, and for all `i`, if `m` is less than or equal to `i` and `i` is less than or equal to `n`, then `0` is less than or equal to `v(i)` and `v(i+1)` is less than or equal to `v(i)`, and for all `k`, if `m` is less than or equal to `k` and `k` is less than or equal to `n`, then `l` is less than or equal to the sum from `m` to `k` of `a`, and the sum from `m` to `k` of `a` is less than or equal to `u`, then `l` times `v(m)` is less than or equal to the sum from `m` to `n` of `a(i)` times `v(i)`, and the sum from `m` to `n` of `a(i)` times `v(i)` is less than or equal to `u` times `v(m)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: when the upper bound `n` is equal to `m`.
  - Simplify the sums using `SUM_CLAUSES_NUMSEG` and properties of arithmetic.
  - The case where `m = 0` needs special treatment, involving `SUM_SING_NUMSEG`.
- Inductive step: Assume the theorem holds for `n`, prove for `n+1`.
  - Rearrange the sum using `SUM_REARRANGE_LEMMA`.
  - The proof splits into showing two inequalities: `l * v(m) <= sum(m..n) (\i. a(i) * v(i))` and `sum(m..n) (\i. a(i) * v(i)) <= u * v(m)`.
  - Invoke the transitivity of real number inequality `REAL_LE_TRANS`.
  - Introduce a suitable intermediate expression to enable transitivity. This expression involves the sum of `l * (v(k) - v(k+1))` and `u * (v(k) - v(k+1))`.
  - Use properties of sums, such as `SUM_LMUL` and `SUM_DIFFERENCES`, to simplify expressions.
  - Use `REAL_LE_ADD2` and `REAL_LE_RMUL` to combine inequalities.
  - Apply `SUM_LE_NUMSEG` after generalizing `k`.
  - Deduce `k <= n ==> k <= n + 1` for the application of transitivity.

### Mathematical insight
This theorem provides bounds for a weighted sum, where the weights `v(i)` are monotonically decreasing and bounded above by zero, and the terms `a(i)` satisfy bounds on their partial sums. The theorem essentially states that the weighted sum is bounded by the product of the extreme weight `v(m)` and the lower and upper bounds `l` and `u` of the partial sums of `a`. This result is useful in analysis and numerical methods for estimating the error in approximations.

### Dependencies
- Real Analysis
  - `LE`
  - `REAL_LE_TRANS`
  - `REAL_LE_ADD2`
  - `REAL_LE_RMUL`
  - `REAL_SUB_LE`
  - `LE_REFL`
  - `REAL_ARITH_TAC`
 - Summation
  - `SUM_CLAUSES_NUMSEG`
  - `SUM_SING_NUMSEG`
  - `SUM_REARRANGE_LEMMA`
  - `SUM_LMUL`
  - `SUM_DIFFERENCES`
  - `SUM_LE_NUMSEG`
- Logic
  - `LEFT_FORALL_IMP_THM`
  - `RIGHT_EXISTS_AND_THM`
  - `EXISTS_REFL`

### Porting notes (optional)
- The proof relies heavily on real arithmetic reasoning, which might require adjustments depending on the target proof assistant's capabilities.
- The summation lemmas used (`SUM_CLAUSES_NUMSEG`, `SUM_SING_NUMSEG`, `SUM_REARRANGE_LEMMA`, `SUM_LMUL`, `SUM_DIFFERENCES`, `SUM_LE_NUMSEG`) need to be available or proven in the target environment.
- Handling of quantifiers and indices might differ across systems. Pay careful attention to the variable binding and scope.


---

## SUM_BOUND_LEMMA

### Name of formal statement
SUM_BOUND_LEMMA

### Type of the formal statement
theorem

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
For all real-valued functions `a` and `v`, and real numbers `b`, `m`, and `n`, if `m` is less than or equal to `n`, and for all `i` such that `m` is less than or equal to `i` and `i` is less than or equal to `n`, `0` is less than or equal to `v(i)` and `v(i+1)` is less than or equal to `v(i)`, and for all `k` such that `m` is less than or equal to `k` and `k` is less than or equal to `n`, the absolute value of the sum of `a(i)` from `i = m` to `k` is less than or equal to `b`, then the absolute value of the sum of `a(i) * v(i)` from `i = m` to `n` is less than or equal to `b * abs(v m)`.

### Informal sketch
The proof proceeds as follows:

- It starts by stripping the quantifiers and assumptions.
- It uses a real arithmetic tactic to rewrite the goal into the form `abs(a) <= b * k` using the assumption `--b * k <= a /\ a <= b * k`.
- It then simplifies the goal using assumptions like reflexivity of `<=` and properties of `real_abs`.
- The proof uses `SUM_BOUNDS_LEMMA`.
- Assumptions are rewritten using `REAL_BOUNDS_LE`.

### Mathematical insight
This theorem provides a bound on the absolute value of a sum of products, where one factor in each term is bounded by a constant, and the other factor is a non-negative and monotonically decreasing function. It is a generalization of the summation by parts formula.

### Dependencies
- `LE_REFL`
- `real_abs`
- `SUM_BOUNDS_LEMMA`
- `REAL_BOUNDS_LE`


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
The series defined by the function that maps `n` to `(-1)^n / (2*n + 1)` sums to `pi / 4`. In other words, the infinite series `∑ ((-1)^n / (2n + 1))` converges to `pi / 4`.

### Informal sketch
The proof establishes that the Leibniz formula for `pi / 4` holds by showing the series `∑ ((-1)^n / (2n + 1))` converges to `pi / 4`.

- First use `ATN_1` and `SUMMABLE_LEIBNIZ` to state that the series is summable. Define `s` to be the infinite sum of `(-1)^n / (2n + 1)`.
- Show that `s = arctan(1)`.
- Prove this by contradiction. Assume that `s ≠ arctan(1)`. Define `e` to be the absolute value of the difference between `s` and `arctan(1)`. Assume that `e > 0`
- Use the Cauchy criterion (`SER_CAUCHY`) for convergence to find an `N` such that the tail of the series is less than `e / 7`.
- Next we will show that the function `(\x. sum(0,N) (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1)))` is continuous on the interval &1.
 - This proceeds by first showing that the function is differentiable, and therefore continuous.
- Show that the arctangent function is continuous at `1`.
- Use the continuity of arctangent function to show that the limit as x approaches 1 of `arctan(x)` is `arctan(1)`.
- Choose `d1` and `d2` and define x to be `1 - min (min (d1 / 2) (d2 / 2)) (1 / 2)`. This x will be arbitrarily close to 1.
- Show that `0 < x < 1 /\ abs x < 1`.
- Establish that `arctan(x)` has the power series representation `∑ ((-1)^n * x^(2n + 1) / (2n + 1))`.
- Use the sequential property of sums to state the sum is equal to the sum of the terms.
- Choose `N1` based on the arctangent power series.
- Choose `N2` based on the infinite series `((-1)^n/(2n+1))`.
- Split the sum from 0 to infinity into three parts: 0 to N, N to N+N1+N2, and N+N1+N2 to infinity.
- Show that the absolute value of the sum from `N` to `N1 + N2` of `(-1)^n * x^(2n + 1) / (2n + 1)` is less than `e / 6`. This is done by splitting the sum, using inequalities to bound the terms, and considering the cases where `N1 + N2 = 0`.
- Finally, combine these results using arithmetic and transitivity of inequalities to show a contradiction, completing the proof.

### Mathematical insight
The Leibniz formula for `pi / 4` is a classical result connecting an infinite series to a fundamental mathematical constant. This theorem demonstrates the convergence of the alternating series and provides a method to approximate pi. The proof relies on the power series expansion of the arctangent function and the properties of convergent series.

### Dependencies
- `ATN_1`
- `SUMMABLE_SUM`
- `SUMMABLE_LEIBNIZ`
- `REAL_ARITH`
- `SUM_SUMMABLE`
- `SER_CAUCHY`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `DIFF_CONT`
- `DIFF_SUM`
- `real_div`
- `REAL_MUL_ASSOC`
- `DIFF_CMUL`
- `DIFF_POW`
- `TAUT`
- `ADD_SUB`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_POW_ONE`
- `DIFF_ATN`
- `CONTL_LIM`
- `LIM`
- `AND_FORALL_THM`
- `SUM_SUB`
- `REAL_ABS_NEG`
- `SUM_NEG`
- `REAL_NEG_SUB`
- `REAL_MUL_RNEG`
- `REAL_SUB_LDISTRIB`
- `REAL_ATN_POWSER_ALT`
- `sums`
- `SEQ`
- `ADD_CLAUSES`
- `REAL_LE_TRANS`
- `REAL_MUL_RID`
- `REAL_ABS_POS`
- `REAL_LT_IMP_LE`
- `REAL_ABS_POW`
- `REAL_ABS_NUM`
- `REAL_POW_1_LE`
- `PSUM_SUM_NUMSEG`
- `SUM_BOUND_LEMMA`
- `REAL_POW_LT`
- `REAL_POW_ADD`
- `REAL_POW_LE`
- `ADD_EQ_0`
- `ARITH_EQ`
### Porting notes (optional)
- The proof relies heavily on real analysis theorems and tactics. Ensure that the target proof assistant has similar libraries and automation capabilities.
- Pay close attention to the handling of infinite sums and their convergence criteria.
- Some tactics like `ASM_REAL_ARITH_TAC` provide significant automation for real arithmetic reasoning. Replicating this level of automation in other systems might require custom tactics or specialized libraries.


---

