# div3.ml

## Overview

Number of statements: 3

The file `div3.ml` formalizes the divisibility by 3 rule. It proves theorems related to the divisibility of natural numbers by 3, leveraging results from `prime.ml` and `pocklington.ml`. The file contributes to number theory within the HOL Light library by providing a formal proof of this divisibility criterion.


## EXP_10_CONG_3

### Name of formal statement
EXP_10_CONG_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXP_10_CONG_3 = prove
 (`!n. (10 EXP n == 1) (mod 3)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `10 * 1` THEN CONJ_TAC THEN
  ASM_SIMP_TAC[CONG_MULT; CONG_REFL] THEN
  SIMP_TAC[CONG; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;
```

### Informal statement
For all natural numbers `n`, 10 to the power of `n` is congruent to 1 modulo 3; that is, `(10 EXP n == 1) (mod 3)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: When `n` is 0, `10 EXP 0` is 1, so `(10 EXP 0 == 1) (mod 3)` holds because `CONG_REFL` proves that `1 == 1 (mod 3)`.
- Inductive step: Assume `(10 EXP n == 1) (mod 3)`. We need to prove `(10 EXP (SUC n) == 1) (mod 3)`. We proceed as follows:
    - `10 EXP (SUC n)` is equivalent to `10 * (10 EXP n)` by definition of `EXP`.
    - Since `(10 EXP n == 1) (mod 3)` by the inductive hypothesis, and `10 == 10 (mod 3)` per reflexivity, we want to show `10 * (10 EXP n) == 10 * 1 (mod 3)`. This is handled by `CONG_MULT`.
    - We then need to show `10 * 1 == 1 (mod 3)`.
    - Since `10 == 1 (mod 3)` by `ARITH`, `10 * 1 == 1 * 1 (mod 3)` and therefore `10 * 1 == 1 (mod 3)`
    - Thus, `(10 EXP (SUC n) == 1) (mod 3)`. The theorem is proved by establishing both base and inductive cases.

### Mathematical insight
This theorem demonstrates a basic property of modular arithmetic, specifically how powers of 10 behave modulo 3. Since 10 is congruent to 1 modulo 3, any power of 10 is also congruent to 1 modulo 3. This is crucial for understanding divisibility rules and number theory in general.

### Dependencies
- `EXP`
- `CONG_REFL`
- `CONG_TRANS`
- `CONG_MULT`
- `CONG`
- `ARITH`


---

## SUM_CONG_3

### Name of formal statement
SUM_CONG_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_CONG_3 = prove
 (`!d n. (nsum(0..n) (\i. 10 EXP i * d(i)) == nsum(0..n) (\i. d i)) (mod 3)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES; CONG_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LE_0] THEN MATCH_MP_TAC CONG_ADD THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `d = 1 * d`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL; EXP_10_CONG_3]);;
```

### Informal statement
For all functions `d` from natural numbers to natural numbers, and for all natural numbers `n`, the sum from `0` to `n` of `10` to the power of `i` multiplied by `d(i)` is congruent modulo 3 to the sum from `0` to `n` of `d(i)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: When `n` is `0`, the sums `nsum(0..n) (\i. 10 EXP i * d(i))` and `nsum(0..n) (\i. d(i))` are both just `d(0)`, so they are congruent modulo `3`. Tactics used: `NSUM_CLAUSES_NUMSEG`, `EXP`, `MULT_CLAUSES`, `CONG_REFL`, `LE_0`.
- Inductive step: Assume the theorem holds for `n`. We want to show it holds for `n+1`.
  - We have to show `nsum(0..n+1) (\i. 10 EXP i * d(i))` is congruent modulo `3` to `nsum(0..n+1) (\i. d(i))`.
  - We can split the sums: `nsum(0..n+1) (\i. 10 EXP i * d(i))` is equal to `nsum(0..n) (\i. 10 EXP i * d(i)) + (10 EXP (n+1) * d(n+1))` and similarly `nsum(0..n+1) (\i. d(i))` is equal to `nsum(0..n) (\i. d(i)) + d(n+1)`.
  - By the inductive hypothesis, `nsum(0..n) (\i. 10 EXP i * d(i))` is congruent modulo `3` to `nsum(0..n) (\i. d(i))`.
  - We need to show `(10 EXP (n+1) * d(n+1))` is congruent modulo `3` to `d(n+1)`.
  - Since `10 EXP (n+1)` is congruent to `1` modulo `3` (this is `EXP_10_CONG_3`),  `(10 EXP (n+1) * d(n+1))` is congruent modulo `3` to `(1 * d(n+1))`, which is just `d(n+1)`. Tactics used `ARITH_RULE`.
  - Now using congruence of sums and products, we derive that  `nsum(0..n+1) (\i. 10 EXP i * d(i))` is congruent modulo `3` to `nsum(0..n+1) (\i. d(i))`. Tactics used: `CONG_ADD`, `CONG_MULT`, `EXP_10_CONG_3`.

### Mathematical insight
The theorem states that when determining the remainder of a natural number when divided by 3, it suffices to sum the digits of the base-10 representation of the number. This reflects the fact that 10 is congruent to 1 modulo 3, hence any power of 10 is also congruent to 1 modulo 3.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`
- `EXP`
- `MULT_CLAUSES`
- `CONG_REFL`
- `LE_0`
- `CONG_ADD`
- `ARITH_RULE`
- `CONG_MULT`
- `EXP_10_CONG_3`


---

## DIVISIBILITY_BY_3

### Name of formal statement
DIVISIBILITY_BY_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIVISIBILITY_BY_3 = prove
 (`3 divides (nsum(0..n) (\i. 10 EXP i * d(i))) <=>
   3 divides (nsum(0..n) (\i. d i))`,
  MATCH_MP_TAC CONG_DIVIDES THEN REWRITE_TAC[SUM_CONG_3]);;
```
### Informal statement
For all natural numbers `n` and functions `d` from the interval `[0, n]` to natural numbers, 3 divides the sum from `i = 0` to `n` of `10^i * d(i)` if and only if 3 divides the sum from `i = 0` to `n` of `d(i)`.

### Informal sketch
The proof proceeds by showing that `3 divides (nsum(0..n) (\i. 10 EXP i * d(i)))` if and only if `3 divides (nsum(0..n) (\i. d i))`.

- The proof starts by applying `CONG_DIVIDES`, which allows the conditional replacement of terms inside the divisibility predicate. In this case, to prepare for this conditional term rewriting, we need to show that for each i: `10 EXP i * d(i)` and `d(i)` are congruent modulo 3.
- The main reduction is done by rewriting using `SUM_CONG_3`. This theorem states that if two sums are congruent modulo 3 term by term, then they are congruent modulo 3 overall.

### Mathematical insight
This theorem provides a practical way to check the divisibility by 3 of a number represented by its digits. It states that a number is divisible by 3 if and only if the sum of its digits is divisible by 3. It relies on the fact that 10 is congruent to 1 modulo 3, and therefore any power of 10 is also congruent to 1 modulo 3.

### Dependencies
- Theorems: `SUM_CONG_3`
- Tactics: `MATCH_MP_TAC`, `CONG_DIVIDES`, `REWRITE_TAC`


---

