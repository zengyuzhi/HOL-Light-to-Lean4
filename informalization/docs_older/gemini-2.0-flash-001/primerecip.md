# primerecip.ml

## Overview

Number of statements: 7

`primerecip.ml` proves the divergence of the prime reciprocal series. It depends on results from `bertrand.ml` (Bertrand's postulate) and `divharmonic.ml` (divergence of the harmonic series). The file focuses on formalizing the mathematical theorem related to the sum of reciprocals of prime numbers.


## INDUCTION_FROM_1

### Name of formal statement
INDUCTION_FROM_1

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
For any predicate `P` on natural numbers, if `P 0` and `P 1` hold, and for any natural number `n`, if `1 <= n` and `P n` holds, then `P (SUC n)` holds, then `P n` holds for all natural numbers `n`.

### Informal sketch
The theorem is proved by induction.
- First, universally quantify and strip the goal.
- Perform induction on `n`.
  - Base case: `n = 0`. The goal is now `P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P (SUC n)) ==> P 0`, which follows directly from the assumption `P 0`.
  - Inductive step: Assume `P n` and the goal is `P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P (SUC n)) ==> P (SUC n)`.
    - Rewrite using assumptions.
    - Use MESON to solve the goal. The important arithmetic fact to finish the proof is `n = 0 \/ 1 <= n`. Also, the conversion `num_CONV \`1\`` is used in the MESON call.

### Mathematical insight
This theorem provides a variant of mathematical induction. Instead of showing `P 0` and `!n. P n ==> P (SUC n)`, we need to show `P 0`, `P 1`, and `!n. 1 <= n ==> (P n ==> P (SUC n))`. This variant can be useful when the standard form of induction is difficult to apply directly.

### Dependencies
- `num_CONV \`1\``
- `ARITH_RULE \`n = 0 \/ 1 <= n\``
- `MESON`


---

## SUM_CONV

### Name of formal statement
SUM_CONV

### Type of the formal statement
theorem

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
The theorem states an equational definition of a conversion `SUM_CONV` that evaluates sums over explicitly given integer ranges via a primitive recursive algorithm. The algorithm determines the value of `sum(1..n) f` for any function `f` and any explicit natural number `n`. The conversion rewrites `sum(1..1) f` to `f 1`, and reduces `sum(1..SUC n) f` to `sum(1..n) f + f(SUC n)`.

### Informal sketch
The construction of the conversion `SUM_CONV` involves the following steps:
- First, a theorem `pth` is proved using simplification tactics (`SIMP_TAC`) and arithmetic reasoning (`ARITH_RULE`). This theorem establishes the fundamental recursive property of the summation over numbered segments: `sum(1..1) f = f 1 /\ sum(1..SUC n) f = sum(1..n) f + f(SUC n)`.
- Two elementary conversions `econv_0` and `econv_1`, are created using `GEN_REWRITE_CONV`. `econv_0` rewrites using the first conjunct of `pth`, specifically `sum(1..1) f = f 1`. `econv_1` rewrites using the second conjunct of `pth`, specifically `sum(1..SUC n) f = sum(1..n) f + f(SUC n)`.
- The conversion `sconv` is then defined recursively.
  - It first attempts to apply `econv_0`.
  - If `econv_0` fails then
    - It applies `num_CONV` to the right-hand side of an equality (using `LAND_CONV(RAND_CONV num_CONV)` to make sure the argument is an explicit number)
    - Then applies `econv_1` to rewrite the sum.
    - Then recursively applies `sconv` to the first term `sum(1..n) f` in the resulting expression `sum(1..n) f + f(SUC n)`, and applies `NUM_SUC_CONV` to the second term to reduce the successor.

### Mathematical insight
This conversion provides a method for evaluating a summation over an explicit finite range by iteratively applying the recursive definition of the summation. The initial theorem `pth` expresses this inductive definition as an equivalence. The conversion automates the process of unwinding the summation until only explicit values remain, which can then be simplified further.

### Dependencies
- Definitions: `SUM_CLAUSES_NUMSEG`, `SUM_SING_NUMSEG`
- Theorems: `LE_0`, `1 <= SUC n`

### Porting notes (optional)
- The implementation relies on HOL Light's conversionals for rewriting terms, specifically `GEN_REWRITE_CONV`, `ORELSEC`, `LAND_CONV`, `RAND_CONV`, and `COMB2_CONV`. These may need to be emulated using similar tactics or term manipulation functions in other proof assistants.
- The use of `ARITH_RULE` indicates a reliance on HOL Light's arithmetic reasoning capabilities, which might need to be explicitly invoked or replaced with equivalent tactics in other systems.


---

## PRIMERECIP_HARMONIC_LBOUND

### Name of formal statement
PRIMERECIP_HARMONIC_LBOUND

### Type of the formal statement
theorem

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
For all natural numbers `n`, the following inequality holds: `(&3 / (&16 * ln(&32))) * sum(1..n) (\i. &1 / &i)` is less than or equal to `sum(1..32 EXP n) (\i. if prime(i) then &1 / &i else &0)`.
In other words, `(3/(16*ln(32))) * (sum from i=1 to n of 1/i)` is less than or equal to `(sum from i=1 to 32^n of (1/i if i is prime else 0))`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base Case: For `n = 1`, we need to show that `(3/(16*ln(32))) * 1 <= (sum from i=1 to 32 of (1/i if i is prime else 0))`.  This is handled by simplifying both sides using facts about the `prime` function and arithmetic.
- Inductive Step: Assume the inequality holds for some `n`. We need to prove that it holds for `n+1`.
   1. The inductive hypothesis is used with `REAL_ARITH` to show that if `b - a <= s2 - s1` and `a <= s1`, then `b <= s2`.
   2. The lower and upper bound of prime numbers (`PII_LBOUND`, `PII_UBOUND`) are used to justify some inequalities, along with properties of logarithms (`LN_POW`) and exponentials.
   3. The sums are split (`SUM_ADD_SPLIT`) and combined (`SUM_LMUL`, `SUM_RMUL`).
   4. Some inequalities concerning real numbers and exponentials are used to complete the proof. `REAL_LE_INV2`,
   5. Finally, a series of arithmetic manipulations and simplifications involving real numbers, logarithms, and the prime counting function are applied until the inductive step is proved.

### Mathematical insight
This theorem gives a lower bound for the sum of the reciprocals of primes up to `32^n`, relative to the harmonic series up to `n`.  It relates the sum of reciprocals of primes to the natural logarithm and provides a quantitative bound.

### Dependencies
- `SUM_TRIV_NUMSEG`
- `ARITH`
- `SUM_SING_NUMSEG`
- `REAL_MUL_RZERO`
- `PRIME_1`
- `REAL_LE_REFL`
- `SUM_CONV`
- `PRIME_CONV`
- `REAL_RAT_REDUCE_CONV`
- `LN_POW`
- `REAL_OF_NUM_LT`
- `real_div`
- `REAL_INV_MUL`
- `REAL_MUL_ASSOC`
- `REAL_MUL_RID`
- `REAL_MUL_SYM`
- `GSYM REAL_LE_RDIV_EQ`
- `REAL_LT_DIV`
- `GSYM REAL_INV_DIV`
- `REAL_LE_INV2`
- `LN_2_COMPOSITION`
- `real_sub`
- `REALCALC_REL_CONV`
- `REAL_ARITH`
- `GSYM REAL_SUB_LDISTRIB`
- `SUM_CLAUSES_NUMSEG`
- `REAL_ADD_SUB`
- `ARITH_RULE `1 <= SUC n``
- `LE_TRANS`
- `LE_EXP`
- `IMP_IMP`
- `pii`
- `PSUM_SUM_NUMSEG`
- `EXP_EQ_0`
- `ADD_SUB2`
- `GSYM REAL_OF_NUM_POW`
- `EXP`
- `ARITH_RULE `32 * n = n + 31 * n``
- `SUM_ADD_SPLIT`
- `ARITH_RULE `1 <= n + 1``
- `GSYM(CONJUNCT2 EXP)`
- `SUM_LE_NUMSEG`
- `COND_CASES_TAC`
- `REAL_LE_REFL`
- `REAL_MUL_RZERO`
- `REAL_MUL_LID`
- `REAL_MUL_RID`
- `ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT]`
- `GSYM CONTRAPOS_THM`
- `ARITH_RULE `~(0 < i) <=> i = 0``
- `LE`
- `ADD_EQ_0`
- `GSYM real_div`
- `REAL_POW_LT`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `real_pow`
- `GSYM REAL_OF_NUM_SUC`
- `REAL_FIELD
   `&1 / &2 * (&32 * n32) / (n1 * l) - &5 * n32 / (n * l) =
    (n32 / l) * (&16 / n1 - &5 / n)``
- `REAL_FIELD
   `(&3 / (&16 * l) * i) * &32 * n32 = (n32 / l) * (&6 * i)``
- `REAL_LE_LMUL`
- `REAL_LE_DIV`
- `REAL_POW_LE`
- `LN_POS`
- `REAL_OF_NUM_LE`
- `REAL_ARITH
   `&6 * &1 * n1 <= &16 * n1 - &5 * n <=> n <= inv(inv(&2)) * n1``
- `GSYM REAL_INV_MUL`

### Porting notes (optional)
- The proof relies on `REAL_ARITH_TAC` for many steps, which might need to be replaced by more explicit reasoning in other proof assistants.
- The tactic `COND_CASES_TAC` does case splits on conditional statements which may have different syntax in different systems.


---

## PRIMERECIP_LBOUND

### Name of formal statement
PRIMERECIP_LBOUND

### Type of the formal statement
theorem

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
For all natural numbers `n`, the following inequality holds: `(3 / (32 * ln(32))) * n <= sum (i=1 to 32^(2^n)) (if i is prime then 1/i else 0)`.

### Informal sketch
The proof establishes a lower bound for the sum of reciprocals of prime numbers up to `32^(2^n)`.

- The proof starts by using `GEN_TAC` and `MATCH_MP_TAC REAL_LE_TRANS`, suggesting a transitivity argument with a known inequality.
- An intermediate expression involving `sum (1 .. 2 EXP n) (\i. &1 / &i)` is introduced using `EXISTS_TAC`, i.e., it is shown that `(3 / (32 * ln(32))) * n <= (3 / (16 * ln(32))) * sum (i=1 to 2^n) (1/i)` and `(3 / (16 * ln(32))) * sum (i=1 to 2^n) (1/i) <= sum (i=1 to 32^(2^n)) (if i is prime then 1/i else 0)`.
- `PRIMERECIP_HARMONIC_LBOUND` is used to rewrite the expression, which should relate the sum of reciprocals of primes to a harmonic sum.
- The expression `&3 / (&32 * ln(&32)) * &n = &3 / (&16 * ln(&32)) * (&n / &2)` is then rewritten by `REAL_FIELD`, which is a field operation.
- A monotonic property is applied with `MATCH_MP_TAC REAL_LE_LMUL` to multiply both sides of the inequality by a real number.
- `HARMONIC_LEMMA` is used to rewrite some expression with `REWRITE_RULE[real_ge]`.
- Finally, simplification tactics (`SIMP_TAC`) are applied using `REAL_LE_DIV`, `REAL_LE_MUL`, `LN_POS`, `REAL_OF_NUM_LE`, and `ARITH`. These probably involve handling the real number calculations and arithmetic to obtain the final result.

### Mathematical insight
This theorem provides a lower bound for the sum of the reciprocals of primes up to a certain limit. The key idea is to relate this sum to the harmonic sum, for which good lower bounds are known. This gives an explicit lower bound depending on `n`. This result contributes to the field of number theory.

### Dependencies
- `PRIMERECIP_HARMONIC_LBOUND`
- `REAL_LE_TRANS`
- `REAL_FIELD`
- `REAL_LE_LMUL`
- `HARMONIC_LEMMA`
- `real_ge`
- `REAL_LE_DIV`
- `REAL_LE_MUL`
- `LN_POS`
- `REAL_OF_NUM_LE`
- `ARITH`


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
For any sequence `s`, if for all `k` there exists an `N` such that for all `n`, if `n` is greater than or equal to `N`, then the sum of the sequence `s` from 1 to `n` is greater than or equal to `k`, then it is not the case that the sequence of partial sums of `s` converges.

### Informal sketch
The proof proceeds by assuming the unbounded divergence condition and then negating the conclusion, assuming that the sequence of partial sums `\n. sum(1..n) s` converges. Then, it proceeds as follows:
- Unfold the definition of `convergent`.
- Assume that for all `k`, there exists an `N` such that for all `n`, if `n >= N`, then `sum(1..n) s >= k`. Also assume that there exists a limit `l` such that for every real number `e > 0`, there exists a natural number `M` such that for all `n`, if `n >= M` then the absolute value of `sum(1..n) s - l` is less than `e`.
- Instantiate the unbounded divergence assumption with 1, and get the existence of `N` such that for all `n`, if `n >= N`, then `sum(1..n) s >= 1`.
- Instantiate the convergence assumption with `e/2` (where `e` stands for epsilon), and get the existence of `M` such that for all `n`, if `n >= M`, then the absolute value of `sum(1..n) s - l` is less than `e/2`.
- Introduce a fresh variable `M` for the choice of witnessing `N` from the hypothesis by universal specialization with `M + N`. Specialize universal quantifiers and rewrite according to `LE_ADD, ADD_SYM, GE` lemmas.
- Perform arithmetic reasoning to derive a contradiction.

### Mathematical insight
This theorem formalizes the intuition that if the partial sums of a sequence grow without bound, then the sequence of partial sums cannot converge. It connects the concepts of divergence (specifically, unbounded divergence) and convergence of sequences.

### Dependencies
- `convergent`
- `REAL_LT_01`
- `NOT_EXISTS_THM`
- `LE_ADD`
- `ADD_SYM`
- `GE`


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
The sum of the reciprocals of the prime numbers diverges; that is, it is not the case that the infinite sum, where each term in the sum is `1/i` if `i` is prime and `0` otherwise, converges.

### Informal sketch
The proof demonstrates the divergence of the sum of the reciprocals of primes. It uses the fact that a bounded sequence is necessary for convergence, contrapositively showing divergence by demonstrating that the partial sums are unbounded.

- The divergence is shown by contradiction, assuming convergence.
- A real number `k` is introduced, representing a potential bound on the sum.
- The theorem `REAL_ARCH` is instantiated with `&3 / (&32 * ln(&32))` to show that there exists an `N` such that `&3 / (&32 * ln(&32))` is less than `N`, for an `N:num`.
- Then, an `N:num` is chosen such that `k < &N * (&3 / (&32 * ln (&32)))`.
- An existential is introduced with `32 EXP (2 EXP N)`.
- An arbitrary natural number `n` is assumed greater or equal to `32 EXP (2 EXP N)`.
- With `REAL_LE_TRANS` show that the sum from 1 to `32 EXP (2 EXP N)` of `1/i` if i is prime `0` otherwise is greater than `&Log2N`.
- Then apply PRIMERECIP_LBOUND.
- Finally, contradiction is derived, proving divergence.

### Mathematical insight
This theorem is a well-known result in number theory. It states that even though the prime numbers become less frequent as numbers grow larger, the sum of their reciprocals still diverges, indicating that primes are "dense enough" in the integers.

### Dependencies
`REAL_ARCH`, `REAL_LT_DIV`, `LN_POS_LT`, `REAL_LT_MUL`, `REAL_OF_NUM_LT`, `GE`, `real_ge`, `REAL_LE_TRANS`, `REAL_LT_IMP_LE`, `REAL_MUL_SYM`, `PRIMERECIP_LBOUND`, `LE_EXISTS`, `SUM_ADD_SPLIT`, `ARITH_RULE`, `SUM_POS_LE_NUMSEG`, `REAL_LE_ADDR`, `REAL_LE_DIV`, `REAL_POS`


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
The series of reciprocals of prime numbers diverges. Formally, it is not the case that the series `sum {p | prime p /\ p <= n} (\p. &1 / &p)` converges as `n` tends to infinity.

### Informal sketch
The proof proceeds by contradiction. It assumes that the series of reciprocals of primes converges, and then derives a contradiction.
- First, the theorem `PRIMERECIP_DIVERGES_NUMSEG` is used with `MP_TAC`.
- A tautology is used to rewrite the goal from `convergent` to `~convergent`.
- The goal is specialized by universally quantifying then substituting `n` for `n`.
- Then the proof proceeds by induction on `n`.
  - Base case: It is required to show that `{p | prime p /\ p <= 0} = {}`. Simplify the set using `SUM_CLAUSES`, `SUM_TRIV_NUMSEG`, and arithmetic, and show that a prime number is never less than or equal to 0 using `PRIME_0`.
  - Inductive step: Assume the result holds for `n`. Goal is to show it also holds for `SUC n`.
    - Simplify with `SUM_CLAUSES_NUMSEG` and arithmetic rule `1 <= SUC n`.
    - Simplify the set `{p | prime p /\ p <= SUC n}`. We need to show that this set is equal to `if prime(SUC n) then (SUC n) INSERT {p | prime p /\ p <= n} else {p | prime p /\ p <= n}`.
    - Perform case split on the condition of `prime(SUC n)`.
    - Simplify with `REAL_ADD_RID`.
    - Need to prove that `{p | prime p /\ p <= n}` is finite.
    - Use `FINITE_SUBSET` and show that `{p | prime p /\ p <= n}` is a subset of `1..n`.
    - Simplify with `FINITE_NUMSEG`, `IN_NUMSEG`, `IN_ELIM_THM`, and `SUBSET`. `PRIME_0` and `ARITH_RULE \`1 <= i <=> ~(i = 0)\`` are used to complete the proof.

### Mathematical insight
This theorem states a fundamental result in number theory: despite primes becoming less frequent as numbers grow larger, the sum of their reciprocals still diverges. This contrasts with the sum of the reciprocals of squares, which converges. This result highlights the abundance of prime numbers.

### Dependencies
- `PRIMERECIP_DIVERGES_NUMSEG`
- `SUM_CLAUSES`
- `SUM_TRIV_NUMSEG`
- `ARITH`
- `EXTENSION`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`
- `LE`
- `PRIME_0`
- `SUM_CLAUSES_NUMSEG`
- `REAL_ADD_RID`
- `FINITE_SUBSET`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `SUBSET`
- `REAL_ADD_AC`

### Porting notes (optional)
Pay close attention to how set theory is handled, particularly set comprehension and finiteness. The handling of real number arithmetic may differ significantly depending on the target proof assistant.


---

