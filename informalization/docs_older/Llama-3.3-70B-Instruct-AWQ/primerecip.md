# primerecip.ml

## Overview

Number of statements: 7

The `primerecip.ml` file formalizes the divergence of the prime reciprocal series. It builds upon concepts from `bertrand.ml` and `divharmonic.ml`, which are loaded at the beginning of the file. The file's primary purpose is to establish theorems related to the series of prime reciprocals, contributing to the library's coverage of number theory. Its content is focused on proving the divergence of this specific series.

## INDUCTION_FROM_1

### Name of formal statement
INDUCTION_FROM_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INDUCTION_FROM_1 = prove
 (`!P. P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P(SUC n)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[num_CONV `1`; ARITH_RULE `n = 0 \/ 1 <= n`])
```

### Informal statement
For all properties P, if P holds for 0 and 1, and for all n greater than or equal to 1, if P holds for n then it also holds for the successor of n, then P holds for all n.

### Informal sketch
* The proof starts by assuming a property P and its validity for 0 and 1.
* It then proceeds by induction, using `INDUCT_TAC`, to show that if P holds for any n greater than or equal to 1, it also holds for the successor of n.
* The base case is covered by the initial assumptions about P holding for 0 and 1.
* The inductive step uses `ASM_MESON_TAC` with `num_CONV` and `ARITH_RULE` to establish the relationship between n and its successor, ensuring the property P holds for all n.
* The use of `GEN_TAC`, `STRIP_TAC`, and `ASM_REWRITE_TAC` helps in managing the quantifiers and assumptions during the proof.

### Mathematical insight
This theorem provides a variant of mathematical induction, starting from 1 instead of the traditional 0. It's crucial for proving statements about natural numbers where the base case naturally begins at 1, such as in the study of prime numbers or properties of sequences that are defined starting from the first term.

### Dependencies
#### Theorems and Definitions
* `GEN_TAC`
* `STRIP_TAC`
* `INDUCT_TAC`
* `ASM_REWRITE_TAC`
* `ASM_MESON_TAC`
* `num_CONV`
* `ARITH_RULE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles induction, particularly the starting point of the induction and how quantifiers are managed. The `GEN_TAC`, `STRIP_TAC`, and `INDUCT_TAC` tactics in HOL Light may have direct counterparts or require slight adjustments in other systems to achieve the same effect. Additionally, the use of `ASM_MESON_TAC` with specific convolutions and arithmetic rules may need to be re-expressed using the target system's tactics for automated reasoning and arithmetic manipulations.

---

## SUM_CONV

### Name of formal statement
SUM_CONV

### Type of the formal statement
Theorem/Conversion

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
  sconv
```

### Informal statement
The `SUM_CONV` conversion evaluates sums over explicit intervals. It is based on two main equations: 
1. `sum(1..1) f = f 1`, which states that the sum of `f` over the interval from 1 to 1 is equal to `f(1)`.
2. `sum(1..SUC n) f = sum(1..n) f + f(SUC n)`, which states that the sum of `f` over the interval from 1 to the successor of `n` is equal to the sum of `f` over the interval from 1 to `n` plus `f` applied to the successor of `n`.

### Informal sketch
* The proof starts by establishing the base case `sum(1..1) f = f 1` and the inductive step `sum(1..SUC n) f = sum(1..n) f + f(SUC n)` using `SIMP_TAC` with `SUM_CLAUSES_NUMSEG`, `LE_0`, `ARITH_RULE`, and `SUM_SING_NUMSEG`.
* Two conversions, `econv_0` and `econv_1`, are defined based on the first and second conjuncts of the proven theorem `pth`, respectively.
* A recursive conversion `sconv` is defined, which applies `econv_0` or, if that fails, applies a combination of conversions to handle more complex terms, including recursive application of `sconv` itself and conversion of numeric terms.

### Mathematical insight
The `SUM_CONV` conversion is essential for simplifying and evaluating sums over explicit intervals in a formal proof system. It provides a foundational tool for reasoning about summations, enabling the simplification of complex expressions by breaking them down into more manageable parts.

### Dependencies
* Theorems:
  + `SUM_CLAUSES_NUMSEG`
  + `LE_0`
  + `SUM_SING_NUMSEG`
* Definitions:
  + `SUC`
  + `num_CONV`
  + `NUM_SUC_CONV`
* Tactics:
  + `SIMP_TAC`
  + `GEN_REWRITE_CONV`
  + `LAND_CONV`
  + `RAND_CONV`
  + `COMB2_CONV`
  + `ORELSEC`

### Porting notes
When translating `SUM_CONV` into other proof assistants, special attention should be paid to the handling of recursive conversions and the application of specific tactics. The exact implementation may vary depending on the target system's support for recursive functions, conversion tactics, and term manipulation. Additionally, the porting process may require adjustments to accommodate differences in how summations and arithmetic are represented and manipulated in the target system.

---

## PRIMERECIP_HARMONIC_LBOUND

### Name of formal statement
PRIMERECIP_HARMONIC_LBOUND

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
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the inequality `(&3 / (&16 * ln(&32))) * sum(1..n) (\i. &1 / &i) <= sum(1..32 EXP n) (\i. if prime(i) then &1 / &i else &0)` holds.

### Informal sketch
The proof of `PRIMERECIP_HARMONIC_LBOUND` involves:
* Using induction to prove the statement for all `n`.
* Establishing a base case and an inductive step.
* Employing various mathematical properties and theorems, including:
 + `SUM_TRIV_NUMSEG`, `ARITH`, `SUM_SING_NUMSEG`, and `REAL_MUL_RZERO` for simplifying summations.
 + `PRIME_1` and `REAL_LE_REFL` for handling prime numbers and real number comparisons.
 + `REAL_ARITH` for performing arithmetic operations on real numbers.
 + `REAL_LE_INV2` for comparing real numbers using inverses.
 + `LN_POW` and `REAL_POW_LT` for properties of logarithms and exponentiation.
* Utilizing tactics such as `MATCH_MP_TAC`, `CONJ_TAC`, `REWRITE_TAC`, `CONV_TAC`, and `SIMP_TAC` to manipulate and simplify the expressions.

### Mathematical insight
The `PRIMERECIP_HARMONIC_LBOUND` theorem provides a lower bound for the sum of reciprocals of prime numbers up to `32 EXP n`, relative to the harmonic series. This result has implications for number theory and the distribution of prime numbers.

### Dependencies
* Theorems:
 + `INDUCTION_FROM_1`
 + `REAL_ARITH`
 + `SUM_TRIV_NUMSEG`
 + `ARITH`
 + `SUM_SING_NUMSEG`
 + `REAL_MUL_RZERO`
 + `PRIME_1`
 + `REAL_LE_REFL`
 + `REAL_LE_INV2`
 + `LN_POW`
 + `REAL_POW_LT`
 + `PII_UBOUND_5`
 + `PII_LBOUND`
* Definitions:
 + `prime`
 + `sum`
 + `exp`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of:
* Induction and recursion
* Real number arithmetic and comparison
* Properties of logarithms and exponentiation
* Summation and series
* Prime numbers and their distribution
Note that the specific tactics and theorems used in the HOL Light proof may not have direct counterparts in other systems, so some creativity may be required to recreate the proof.

---

## PRIMERECIP_LBOUND

### Name of formal statement
PRIMERECIP_LBOUND

### Type of the formal statement
Theorem

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
  SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; LN_POS; REAL_OF_NUM_LE; ARITH])
```

### Informal statement
For all natural numbers n, the following inequality holds: `3 / (32 * ln(32)) * n` is less than or equal to the sum from 1 to `2^(2^n)` of `1/i` if `i` is prime, and 0 otherwise.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce a universal quantifier over `n`.
* It then uses `MATCH_MP_TAC REAL_LE_TRANS` to apply a transitive property of less than or equal to, introducing an existential quantifier.
* The `EXISTS_TAC` tactic is used to introduce a specific value that satisfies the existential quantifier: `3 / (16 * ln(32)) * sum (1 .. 2^n) (1/i)`.
* The proof then applies several rewrite rules, including `PRIMERECIP_HARMONIC_LBOUND` and `REAL_FIELD`, to simplify the expression.
* `MATCH_MP_TAC REAL_LE_LMUL` is used to apply a property of less than or equal to with multiplication.
* The `REWRITE_TAC` and `SIMP_TAC` tactics are used to further simplify the expression, applying various properties of real numbers, including `HARMONIC_LEMMA`.

### Mathematical insight
This theorem provides a lower bound on the sum of reciprocals of prime numbers up to a certain limit, which is a fundamental result in number theory. The proof relies on properties of real numbers, particularly inequalities and limits, as well as the definition of prime numbers.

### Dependencies
* `PRIMERECIP_HARMONIC_LBOUND`
* `REAL_LE_TRANS`
* `REAL_LE_LMUL`
* `HARMONIC_LEMMA`
* `REAL_FIELD`
* `REAL_OF_NUM_LE`
* `LN_POS`
* `REAL_LE_DIV`
* `REAL_LE_MUL`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the properties of real numbers and the definition of prime numbers are handled correctly. The use of `GEN_TAC` and `EXISTS_TAC` may need to be adapted to the target system's syntax for introducing quantifiers. Additionally, the rewrite rules and simplification tactics may need to be modified to match the target system's capabilities.

---

## UNBOUNDED_DIVERGENT

### Name of formal statement
UNBOUNDED_DIVERGENT

### Type of the formal statement
Theorem

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
  REAL_ARITH_TAC)
```

### Informal statement
For all sequences `s`, if for every number `k`, there exists a number `N` such that for all numbers `n` greater than or equal to `N`, the sum from `1` to `n` of `s` is greater than or equal to `k`, then the sequence of sums from `1` to `n` of `s` is not convergent.

### Informal sketch
* Start with the assumption that for any `k`, there's an `N` such that for all `n >= N`, the sum of the sequence `s` from `1` to `n` exceeds `k`.
* Use the definition of `convergent` to set up a contradiction, assuming the sequence of sums is convergent.
* Apply the `convergent` definition and `SEQ` to establish a bound on the sequence.
* Utilize `REAL_LT_01` to derive a contradiction by showing that for any proposed limit `l`, there exists a value that violates the convergence criterion.
* Employ `NOT_EXISTS_THM` and `X_GEN_TAC` to handle the existential quantifier and introduce a new variable `M`.
* Leverage `DISCH_THEN` and `MP_TAC` to apply the assumption to `M + N`, and then apply `REWRITE_TAC` with `LE_ADD` and `GE` to derive the final contradiction.
* The proof relies on `REAL_ARITH_TAC` for arithmetic manipulations.

### Mathematical insight
This theorem establishes that if a sequence of sums grows without bound (for every `k`, there's a point `N` after which the sum exceeds `k`), then the sequence of these sums cannot converge. This is a fundamental property linking the growth rate of sequences with their convergence behavior.

### Dependencies
* `convergent`
* `SEQ`
* `REAL_LT_01`
* `NOT_EXISTS_THM`
* `LE_ADD`
* `GE`
* `REAL_ARITH_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles sequences, convergence, and real arithmetic. Specifically, the use of `REAL_ARITH_TAC` in HOL Light might need to be replaced with equivalent tactics or automated reasoning tools in the target system. Additionally, the representation of sequences and the `convergent` predicate may differ, requiring adjustments to the proof script.

---

## PRIMERECIP_DIVERGES_NUMSEG

### Name of formal statement
PRIMERECIP_DIVERGES_NUMSEG

### Type of the formal statement
Theorem

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
  REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS])
```

### Informal statement
The theorem `PRIMERECIP_DIVERGES_NUMSEG` states that the series `∑[1, n] (1/i if i is prime, otherwise 0)` does not converge as `n` approaches infinity. In other words, the sum of the reciprocals of prime numbers does not converge.

### Informal sketch
* The proof starts by assuming the series converges and then derives a contradiction.
* It uses the `UNBOUNDED_DIVERGENT` theorem to establish that if a series is unbounded, it diverges.
* The tactic `MATCH_MP_TAC` is used to apply the `REAL_ARCH` theorem with a specific value `&3 / (&32 * ln(&32))`.
* The proof then proceeds to establish a lower bound for the sum of the reciprocals of prime numbers using the `PRIMERECIP_LBOUND` theorem.
* The `SUM_POS_LE_NUMSEG` theorem is used to establish that the sum of the reciprocals of prime numbers is bounded below by a divergent series.
* The proof concludes by showing that the sum of the reciprocals of prime numbers is greater than a divergent series, and therefore diverges.

### Mathematical insight
The theorem `PRIMERECIP_DIVERGES_NUMSEG` is a fundamental result in number theory, showing that the sum of the reciprocals of prime numbers diverges. This result has important implications for many areas of mathematics, including analytic number theory and algebraic geometry. The proof relies on a combination of techniques from real analysis and number theory, including the use of the prime number theorem and the properties of the logarithmic function.

### Dependencies
#### Theorems
* `UNBOUNDED_DIVERGENT`
* `REAL_ARCH`
* `PRIMERECIP_LBOUND`
* `SUM_POS_LE_NUMSEG`
#### Definitions
* `convergent`
* `prime`
* `sum`
* `ln`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `MATCH_MP_TAC` and `GEN_REWRITE_TAC` tactics are properly translated. Additionally, the `PRIMERECIP_LBOUND` theorem may require special attention, as it relies on a specific property of prime numbers. The use of `REAL_ARCH` and `UNBOUNDED_DIVERGENT` theorems may also require careful handling, as they rely on specific properties of real numbers and series convergence.

---

## PRIMERECIP_DIVERGES

### Name of formal statement
PRIMERECIP_DIVERGES

### Type of the formal statement
Theorem

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
    REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `~(SUC n <= n)`; REAL_ADD_AC]])
```

### Informal statement
The theorem `PRIMERECIP_DIVERGES` states that the function `(\n. sum {p | prime p /\ p <= n} (\p. &1 / &p))` is not convergent. This means that as `n` increases, the sum of the reciprocals of prime numbers less than or equal to `n` does not approach a finite limit.

### Informal sketch
* The proof starts by assuming the negation of the statement, i.e., that the function is convergent.
* It then uses the `MATCH_MP_TAC` tactic to apply a tautology `(a <=> b) ==> ~a ==> ~b`, which allows us to assume the existence of a sequence that does not converge.
* The proof then proceeds by induction on `n`, considering two cases: when `n` is 0 and when `n` is a successor.
* In the base case (`n = 0`), it shows that the sum is empty, and hence convergent.
* In the inductive step, it uses the `SUBGOAL_THEN` tactic to substitute the expression for the sum of primes less than or equal to `SUC n`, and then applies various simplification and rewriting tactics to simplify the expression.
* The proof then uses the `COND_CASES_TAC` tactic to consider two cases: when `SUC n` is prime and when it is not.
* In both cases, it applies further simplification and rewriting tactics to show that the sum does not converge.
* The `FINITE` tactic is used to show that the set of primes less than or equal to `n` is finite, which is used to justify the use of the `SUM` function.

### Mathematical insight
The theorem `PRIMERECIP_DIVERGES` is a fundamental result in number theory, stating that the sum of the reciprocals of prime numbers diverges. This result has important implications for many areas of mathematics, including analytic number theory and algebraic geometry. The proof of this theorem is a classic example of a non-trivial application of mathematical induction and careful manipulation of logical and mathematical expressions.

### Dependencies
* `PRIME_0`
* `FINITE_NUMSEG`
* `IN_NUMSEG`
* `IN_ELIM_THM`
* `SUBSET`
* `REAL_ADD_RID`
* `SUM_CLAUSES`
* `SUM_TRIV_NUMSEG`
* `ARITH_RULE`
* `TAUT`
* `FUN_EQ_THM`
* `EXTENSION`
* `NOT_IN_EMPTY`
* `LE`

### Porting notes
When porting this theorem to other proof assistants, care should be taken to ensure that the induction and rewriting tactics are properly translated. In particular, the use of `SUBGOAL_THEN` and `MATCH_MP_TAC` may require special attention, as these tactics may not have direct analogues in other systems. Additionally, the `FINITE` tactic may need to be replaced with a different tactic or lemma, depending on the specific proof assistant being used.

---

