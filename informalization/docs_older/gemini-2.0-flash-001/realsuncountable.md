# realsuncountable.ml

## Overview

Number of statements: 12

`realsuncountable.ml` proves the uncountability of the real numbers, formalizing the non-denumerability of the continuum. It relies on definitions and theorems from `card.ml` (cardinality) and `analysis.ml`. The file likely contains the proof that there is no bijection between the natural numbers and the real numbers.


## countable

### Name of formal statement
- countable

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;
```

### Informal statement
- For any set `s`, `s` is countable if and only if there exists an injection from `s` into the set of natural numbers (`UNIV:num->bool`).

### Informal sketch
- The definition introduces the concept of countability for a set `s`.
- `s <=_c (UNIV:num->bool)` represents that the cardinality of `s` is less than or equal to the cardinality of the set of natural numbers.
- This inequality of cardinalities is defined by the existence of an injection (one-to-one function) from `s` into the set of natural numbers.

### Mathematical insight
- This definition of countability is standard. A set is countable if it is either finite or in bijection with the set of natural numbers (i.e., countably infinite).
- The definition uses the concept of injection to formally express the idea that a countable set can be "enumerated" by natural numbers.

### Dependencies
- Theories: `Library/card.ml`
- Definitions: `cardinality`, `injection` (hidden in the notation `<=_c`)


---

## repeating

### Name of formal statement
repeating

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let repeating = new_definition
 `repeating = {s:num->bool | ?n. !m. m >= n ==> s m}`;;
```
### Informal statement
The set `repeating` is defined to be the set of sequences `s` from natural numbers to booleans, such that there exists a natural number `n` where, for all natural numbers `m`, if `m` is greater than or equal to `n`, then `s m` holds.

### Informal sketch
- The definition introduces `repeating` as a set of boolean-valued sequences (functions from natural numbers to booleans).
- A sequence `s` belongs to the set `repeating` if there exists some index `n` such that all elements of the sequence from index `n` onwards are `true`.
- Thus `repeating` is the set of eventually-true boolean sequences.

### Mathematical insight
The set `repeating` captures the concept of sequences that eventually become constantly true. This definition is likely a component in formalizing certain notions of convergence or stability criteria within a discrete setting. It's a basic yet important step towards reasoning about the behavior of infinite sequences in formal logic.

### Dependencies
None

### Porting notes (optional)
- This definition should be easily translatable into other proof assistants like Coq, Lean, or Isabelle. The core components—sets, functions, quantifiers—are standard.
- Pay attention to how the target proof assistant handles function types (e.g., `num -> bool`). Some systems might use different notations for function spaces.


---

## BINARY_BOUND

### Name of formal statement
BINARY_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_BOUND = prove
(`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_0; EXP_ADD; EXP_1; EXP] THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of the terms defined by the function that maps `i` to `2` to the power of `i` if `b(i)` is true, and to `0` otherwise, is less than `2` to the power of `n + 1`.

### Informal sketch
The theorem is proved by induction on `n`.

- Base case: When `n = 0`, the sum reduces to `if b(0) then 2 EXP 0 else 0`.  If `b(0)` is true, then the sum is `1`, which is less than `2 EXP (0+1) = 2`.  If `b(0)` is false, the sum is `0`, which is less than `2`.
- Inductive step: Assume the theorem holds for `n`.  We need to prove it for `n + 1`.  The summation can be split into the sum from `0` to `n` plus the `(n+1)`-th term i.e., `if b(n+1) then 2 EXP (n+1) else 0`. By the inductive hypothesis, the sum from 0 to `n` is less than `2 EXP (n+1)`. If `b(n+1)` is false, the `(n+1)`-th term is `0`, so the sum from `0` to `n+1` is less than `2 EXP (n+1)`, which is less than `2 EXP (n+2)`. If `b(n+1)` is true, the `(n+1)`-th term is `2 EXP (n+1)`. Then the sum becomes less than `2 EXP (n+1) + 2 EXP (n+1) = 2 * 2 EXP (n+1) = 2 EXP 1 * 2 EXP (n+1) = 2 EXP (n+2)`.

### Mathematical insight
The theorem states that the sum of a subset of powers of 2, where the subset is determined by the boolean function `b`, is strictly less than the next power of 2. This captures the idea that the binary representation of a number is unique and that any number is smaller than the next power of 2.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`
- `LE_0`
- `EXP_ADD`
- `EXP_1`
- `EXP`


---

## BINARY_DIV_POW2

### Name of formal statement
BINARY_DIV_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0`,
  SIMP_TAC[ADD1; DIV_LT; BINARY_BOUND]);;
```
### Informal statement
For all natural numbers `n`, the result of dividing the sum from `0` to `n` of the terms defined by the function that maps `i` to `2 EXP i` if `b(i)` is true and to `0` otherwise, by `2 EXP (SUC n)` is `0`. Here `b` is assumed to be a boolean function over natural numbers.

### Informal sketch
The theorem states that a binary number (represented as a sum of powers of 2, where the `b(i)` function determines the presence of the `i`-th power of 2) divided by 2 to the power of `n+1` is 0, meaning the binary number is smaller than `2^(n+1)`.
- The proof uses `SIMP_TAC` which simplifies the goal using the given theorems.
- `ADD1` probably handles the simplification of `SUC n`.
- `DIV_LT` is used to prove that a quotient is zero because the divisor is strictly less than the dividend.
- `BINARY_BOUND` probably establishes the bound on the binary number, showing it's less than `2^(n+1)`.

### Mathematical insight
The theorem captures the idea that if you have a binary number represented by the sum `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)`, then its value is necessarily less than `2^(n+1)`. Consequently, dividing that number by `2^(n+1)` will result in `0` due to integer division.

### Dependencies
- Constants: `ADD1`, `DIV_LT`
- Theorems: `BINARY_BOUND`


---

## PLUS_MOD_REFL

### Name of formal statement
PLUS_MOD_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PLUS_MOD_REFL = prove
 (`!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_EQ THEN MESON_TAC[MULT_CLAUSES]);;
```
### Informal statement
For all natural numbers `a` and `b`, if `b` is not equal to 0, then `(a + b) mod b` is equal to `a mod b`.

### Informal sketch
The theorem states a basic property of the modulo operation. The proof proceeds as follows:
- Start by stripping the goal.
- Apply the theorem `MOD_EQ`, which states that `(m MOD n = k) <=> (?q. m = k + q * n)`.
- Use MESON to automatically discharge the goal using `MULT_CLAUSES`.

### Mathematical insight
The theorem expresses the fact that adding a multiple of the modulus `b` to a number `a` does not change the remainder when dividing by `b`. This is a fundamental property used in modular arithmetic.

### Dependencies
- Theorems: `MOD_EQ`, `MULT_CLAUSES`
- Tactics: `REPEAT STRIP_TAC`, `MATCH_MP_TAC`, `MESON_TAC`


---

## BINARY_PLUS_DIV_POW2

### Name of formal statement
BINARY_PLUS_DIV_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_PLUS_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` THEN
  ASM_REWRITE_TAC[BINARY_BOUND; ADD1] THEN
  REWRITE_TAC[ADD_AC; MULT_CLAUSES]);;
```

### Informal statement
For all natural numbers `n`, the integer division of the sum of `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` plus `2` to the power of the successor of `n` by `2` to the power of the successor of `n` is equal to `1`.

### Informal sketch
The proof proceeds as follows:
- Use `DIV_UNIQ` to show that the result of the division is 1. This requires showing that `nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n)` is equal to `2 EXP (SUC n)`.
- Introduce an existential variable for `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)`.
- Rewrite using `BINARY_BOUND`, which provides a bound related to the binary representation, and `ADD1`.
- Apply rewriting using additive commutativity and associativity (`ADD_AC`) and clauses for multiplication (`MULT_CLAUSES`).

### Mathematical insight
The theorem essentially states that if you have a number represented in binary format (using the function `b(i)` to determine if the i-th bit is set), and you add `2^(n+1)` to it, then the result divided by `2^(n+1)` is 1. The `nsum` term calculates the value represented by the binary digits `b(i)` from `0` to `n`. Adding `2^(n+1)` ensures the number is at least `2^(n+1)`, so dividing by `2^(n+1)` yields 1.

### Dependencies
- `BINARY_BOUND`
- `ADD1`
- `ADD_AC`
- `MULT_CLAUSES`
- `DIV_UNIQ`



---

## BINARY_UNIQUE_LEMMA

### Name of formal statement
BINARY_UNIQUE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_UNIQUE_LEMMA = prove
 (`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) =
       nsum(0..n) (\i. if c(i) then 2 EXP i else 0)
       ==> !i. i <= n ==> (b(i) <=> c(i))`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [SIMP_TAC[LE] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);
    REWRITE_TAC[LE_0]] THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_THEN `i = SUC n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; BINARY_DIV_POW2; BINARY_PLUS_DIV_POW2] THEN
    REWRITE_TAC[ARITH_EQ];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    SIMP_TAC[ADD_CLAUSES; BINARY_BOUND; MOD_LT; PLUS_MOD_REFL; EXP_EQ_0; ARITH;
             ADD1] THEN
    ASM_MESON_TAC[LE_REFL]]);;
```
### Informal statement
For every natural number `n`, if the sum from `i = 0` to `n` of `2` to the power of `i` if `b(i)` is true, and `0` otherwise, is equal to the sum from `i = 0` to `n` of `2` to the power of `i` if `c(i)` is true, and `0` otherwise, then for all `i` such that `i` is less than or equal to `n`, `b(i)` is equivalent to `c(i)`.

### Informal sketch
The proof proceeds by induction on `n`.
- **Base case:** When `n = 0`, the sums are equal if and only if `b(0)` is equivalent to `c(0)`.
- **Inductive step:** Assuming the theorem holds for `n`, we aim to prove it for `n+1`.
  - Assume that the sums from `0` to `n+1` are equal: `nsum(0..n+1) (\i. if b(i) then 2 EXP i else 0) = nsum(0..n+1) (\i. if c(i) then 2 EXP i else 0)`.
  - We need to show that for all `i` such that `i <= n+1`, `b(i)` is equivalent to `c(i)`.
  - Consider the case `i = n+1`. Divide both sides of the assumed equation by `2 EXP (SUC n)`. By properties of integer division, the sums from `0` up to `n` are eliminated and we infer that indeed `b(SUC n)` is the same as `c(SUC n)`.
  - Consider the case `i <= n`. Take the original equation and compute the remainder of division by `2 EXP (SUC n)`. Then by the inductive hypothesis, it is shown that `b(i)` is equivalent to `c(i)` for `i <= n`.
  - The general equation for `i` is proved.

### Mathematical insight
The theorem states that the binary representation of a number, up to a certain number of bits, is unique. The function `b` and `c` can be considered as representations of binary numbers using bits `0` and `1`. The sum expresses the decoded integer value. The theorem proves that if two binary expansions have the same value, their coefficients have to be the same.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`
- `LE`
- `ARITH`
- `LE_0`
- `ADD_CLAUSES`
- `BINARY_DIV_POW2`
- `BINARY_PLUS_DIV_POW2`
- `ARITH_EQ`
- `BINARY_BOUND`
- `MOD_LT`
- `PLUS_MOD_REFL`
- `EXP_EQ_0`
- `ADD1`
- `LE_REFL`


---

## COUNTABLE_REPEATING

### Name of formal statement
COUNTABLE_REPEATING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COUNTABLE_REPEATING = prove
 (`countable repeating`,
  REWRITE_TAC[countable] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) *_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC CARD_EQ_IMP_LE THEN REWRITE_TAC[CARD_SQUARE_NUM]] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC
   `\s:num->bool. let n = minimal n. !m. m >= n ==> s m in
                  n,nsum(0..n) (\i. if s(i) then 2 EXP i else 0)` THEN
  REWRITE_TAC[repeating; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN LET_TAC THEN REWRITE_TAC[mul_c; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `k = minimal n. !m. m >= n ==> s m` THEN
  ABBREV_TAC `l = minimal n. !m. m >= n ==> t m` THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  ASM_CASES_TAC `l:num = k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FUN_EQ_THM; GE] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP BINARY_UNIQUE_LEMMA) THEN
  ASM_MESON_TAC[LE_CASES]);;
```

### Informal statement
The set of repeating sequences of natural numbers is countable. That is, the cardinality of the set of sequences `s` of natural numbers such that there exists a natural number `n` such that for all `m`, if `m` is greater than or equal to `n`, then `s(m)` is equal to `s(n+1)`, is less than or equal to the cardinality of the natural numbers.

### Informal sketch
The proof demonstrates that the set of repeating sequences is countable by showing that its cardinality is less than or equal to the cardinality of the natural numbers. The proof proceeds as follows:
- First, it rewrites `countable` using the definition (likely, `countable` means "can be injected to the natural number", which can be proved by its cardinality is less equal to that of natural number)
- It uses transitivity to relate the cardinality of `repeating` to the cardinality of `(UNIV:num->bool)` by `(UNIV:num->bool)`.
- It proves two subgoals with cardinality comparison.
  - The first subgoal is shown to be true, which is for every set, the cardinality of the set is no more than itself.
  - The second subgoal relates cardinality of `(UNIV:num->bool) *_c (UNIV:num->bool)` is no more than that of `num`. This is proved by first proving that the cardinality of `(UNIV:num->bool)` is no more than that of natural number, and then apply `CARD_SQUARE_NUM` to finalize the proof.
- An explicit injection `f` from the set of repeating sequences to the set of pairs of natural numbers is defined, where `f(s) = (n, nsum(0..n) (\i. if s(i) then 2 EXP i else 0))`, `n` is the smallest natural number such that for all `m`, if `m` is greater than or equal to `n`, then `s(m)` is equal to `s(m+1)`. `nsum(0..n) (\i. if s(i) then 2 EXP i else 0)` essentially encodes the sequence `s` from `0` to `n`. `n` is also called `k` in later proof.
- Rewrites `repeating` and performs elimination on `IN_ELIM_THM`.
- Proves injecting to the pair of numbers.
  GEN_TAC and LET_TAC introduce universal quantification and local variables.
  `mul_c`, `IN_ELIM_THM`, and `IN_UNIV` are used to simplify cardinalities.
  `MESON_TAC` is used for automated reasoning.
- Introduces two universally quantified sequences, `s` and `t`.
- Renames `minimal n. !m. m >= n ==> s m` to `k` and `minimal n. !m. m >= n ==> t m` to `l`.
- Uses `ASM_CASES_TAC` to split the proof into two cases based on whether `l = k`.
- Handles these cases using rewriting, substitution, and `ASM_MESON_TAC` along with `LE_CASES` to establish the desired result

### Mathematical insight
The theorem establishes that the set of repeating sequences of natural numbers is countable. This is achieved by constructing an injection from the set of repeating sequences to the set of pairs of natural numbers. The first element of the pair represents the index from which the sequence starts repeating. The second element encodes the initial segment of the sequence before it starts repeating, represented as a sum of powers of 2 using predicate `s(i)`. This encoding allows each repeating sequence to be uniquely associated with a pair of natural numbers, demonstrating countability.

### Dependencies
- Definitions:
  - `countable`
  - `repeating`
- Theorems:
  - `CARD_LE_TRANS`
  - `CARD_EQ_IMP_LE`
  - `CARD_SQUARE_NUM`
  - `FUN_EQ_THM`
  - `IN_ELIM_THM`
  - `le_c`
  - `mul_c`
  - `IN_UNIV`
  - `MINIMAL`
  - `PAIR_EQ`
  - `BINARY_UNIQUE_LEMMA`
  - `LE_CASES`
  - `GE`
- Other:
  - `LET_DEF`
  - `LET_END_DEF`


---

## canonical

### Name of formal statement
canonical

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let canonical = new_definition
 `canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)}`;;
```

### Informal statement
The set `canonical` is defined as the set of all functions `s` from natural numbers to booleans such that for every natural number `n`, there exists a natural number `m` such that `m` is greater than or equal to `n` and `s(m)` is false.

### Informal sketch
The definition introduces the set of infinite sequences of booleans (represented as functions from natural numbers to booleans) that have infinitely many `false` values. The definition is direct and doesn't involve a proof. It simply introduces a name for a set defined by a first-order logic formula.

### Mathematical insight
The definition captures the notion of a sequence of booleans having infinitely many `false` entries. This is useful for representing digits that aren't just a finite string and therefore can be used to model uncountability using Cantor's diagonal argument.

### Dependencies
None


---

## UNCOUNTABLE_CANONICAL

### Name of formal statement
UNCOUNTABLE_CANONICAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNCOUNTABLE_CANONICAL = prove
 (`~countable canonical`,
  REWRITE_TAC[countable] THEN STRIP_TAC THEN
  MP_TAC (INST_TYPE [`:num`,`:A`] CANTOR_THM_UNIV) THEN
  REWRITE_TAC[CARD_NOT_LT] THEN
  MP_TAC(ISPECL [`canonical`; `repeating`] CARD_DISJOINT_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM;
                canonical; repeating; GE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `canonical UNION repeating = UNIV` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM;
                canonical; repeating; GE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC CARD_LE_TRANS `canonical +_c repeating` THEN
  ASM_SIMP_TAC[CARD_EQ_IMP_LE] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) +_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[countable; COUNTABLE_REPEATING; CARD_LE_ADD];
    MATCH_MP_TAC CARD_ADD_ABSORB_LE THEN
    REWRITE_TAC[num_INFINITE; CARD_LE_REFL]]);;
```

### Informal statement
The set of canonical numbers is not countable. Here, `canonical` and `repeating` are two given sets of numbers such that for every `x`, `x` is in the intersection of `canonical` and `repeating` if and only if `x` is in the empty set (i.e., the intersection is empty), and for every `x`, if `GE x 0` then `x` is in either `canonical` or `repeating`.

### Informal sketch
The proof proceeds as follows:
- Given the assumption that `canonical` is countable, derive a contradiction to show that `canonical` is uncountable.
- Apply Cantor's theorem (`CANTOR_THM_UNIV`) to show that the cardinality of the type `:num` is not less than the cardinality of its power set `:num -> bool`.
- Use the fact that `canonical` and `repeating` are disjoint (`CARD_DISJOINT_UNION`) and their union is the entire universe (`UNIV`) to deduce that `canonical +_c repeating` (cardinal sum) is equal to `UNIV`.
- Show that `canonical UNION repeating = UNIV` by proving that for all `x`, `x` is in `canonical UNION repeating` if and only if `x` is in `UNIV`. This relies on the properties of `canonical`, `repeating`, and the assumption that if `GE x 0` then `x` is in either `canonical` or `repeating`.
- Establish the chain of inequalities: `cardinal canonical` <= `cardinal (canonical UNION repeating)` = `cardinal UNIV` = `cardinal ((UNIV:num->bool) +_c (UNIV:num->bool))`.  This step uses the assumption that `canonical` is countable and the theorem `COUNTABLE_REPEATING`.
- Finally, show that because `canonical` is countable, the cardinality of `canonical` is less than or equal to the cardinality of `(UNIV:num->bool) +_c (UNIV:num->bool)`. Use theorem `CARD_ADD_ABSORB_LE` that allows us to deduce `FALSE` from the contradiction.

### Mathematical insight
The theorem formalizes that the defined set of `canonical` numbers is uncountable. This relies on constructing `canonical` such that together with its disjoint counterpart `repeating`, they constitute the entire universe of numbers. The strategic proof combines set-theoretic properties (disjointness, union), cardinality arguments (Cantor's theorem, cardinal sums), and the initial assumption of countability to arrive at a contradiction, thus proving uncountability.

### Dependencies
- `countable`
- `CANTOR_THM_UNIV`
- `CARD_NOT_LT`
- `CARD_DISJOINT_UNION`
- `EXTENSION`
- `IN_INTER`
- `NOT_IN_EMPTY`
- `IN_ELIM_THM`
- `canonical`
- `repeating`
- `GE`
- `IN_UNION`
- `IN_UNIV`
- `CARD_LE_TRANS`
- `CARD_EQ_IMP_LE`
- `num_INFINITE`
- `CARD_LE_REFL`
- `COUNTABLE_REPEATING`
- `CARD_LE_ADD`
- `CARD_ADD_ABSORB_LE`


---

## SUMINF_INJ_LEMMA

### Name of formal statement
SUMINF_INJ_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMINF_INJ_LEMMA = prove
 (`!s t n. ~(s n) /\ t n /\
           (!m. m < n ==> (s(m) <=> t(m))) /\
           (!n. ?m. m >= n /\ ~(s m))
           ==> suminf(\n. if s n then inv (&2 pow n) else &0)
                < suminf(\n. if t n then inv (&2 pow n) else &0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\k:num. sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)`;
      `\n:num. sum(0,n) (\n. if t n then inv (&2 pow n) else &0)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GE; LE_EXISTS] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM ADD1] THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_ADDR; SUM_BINSEQUENCE_LBOUND]] THEN
  ASM_REWRITE_TAC[GSYM SUM_SPLIT; SUM_1; ADD_CLAUSES] THEN
  UNDISCH_THEN `!n:num. ?m. m >= n /\ ~s m` (MP_TAC o SPEC `n + 1`) THEN
  REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
    `sum(0,m) (\n. if s n then inv (&2 pow n) else &0) + inv(&2 pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\n:num. sum(0,n) (\n. if s n then inv (&2 pow n) else &0)`;
      `\k:num. sum(0,m) (\n. if s n then inv(&2 pow n) else &0) +
               inv(&2 pow m)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD; ADD_CLAUSES] THEN
    DISJ_CASES_THEN SUBST_ALL_TAC (ARITH_RULE `p = 0 \/ p = 1 + PRE p`) THEN
    SIMP_TAC[sum; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    ASM_REWRITE_TAC[SUM_1; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &2 pow (m + 1)` THEN
    REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_LE] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; SUM_1; REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c < e - d ==> (a + c) + d < b + e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[LE_0; ADD_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &2 pow (n + 1) - &2 / &2 pow ((n + 1) + r)` THEN
  REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_SHARP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ d < c ==> a - c < b - d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REAL_FIELD `&0 < inv(x) ==> inv(x) < &2 / x`) THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]]);;
```

### Informal statement
For all boolean sequences `s` and `t`, and for all natural numbers `n`, if the following conditions hold:
1. `s(n)` is false and `t(n)` is true.
2. For all natural numbers `m`, if `m` is less than `n`, then `s(m)` is equivalent to `t(m)`.
3. For all natural numbers `n`, there exists a natural number `m` such that `m` is greater than or equal to `n` and `s(m)` is false.

Then, the infinite sum of `inv(&2 pow n)` where `n` ranges over all natural numbers such that `s(n)` is true, is strictly less than the infinite sum of `inv(&2 pow n)` where `n` ranges over all natural numbers such that `t(n)` is true.

### Informal sketch
The proof proceeds by showing that under the given conditions, the infinite sum associated with `s` is strictly less than that associated with `t`.

- It leverages `REAL_LTE_TRANS` to introduce an intermediate sum, `sum(0, n+1) (\n. if t n then inv (&2 pow n) else &0)`.
- It uses properties of convergent sequences and their sums (`SEQ_LE`, `SEQ_CONST`, `sums`, `SUMS_BINSEQUENCE`).
- It utilizes `SUM_SPLIT` and `SUM_1` to manipulate finite sums and simplify expressions.
- It exploits the condition that for any `n`, there exists an `m >= n` where `s(m)` is false.
- It utilizes inequalities and algebraic manipulations on sums and real numbers, specifically leveraging bounds on the sum of the binary sequence (`SUM_BINSEQUENCE_UBOUND_SHARP`, `SUM_BINSEQUENCE_UBOUND_LE`).
- By carefully bounding the sums and exploiting condition 1 (that `s(n)` is false while `t(n)` is true), the proof establishes the desired strict inequality between the two infinite sums.

### Mathematical insight
This theorem demonstrates an injectivity-like property for representing real numbers in [0,1] using binary expansions. It shows that distinct boolean sequences sufficiently represent different subsets of `N` will result in distinct sums of the form `suminf (\n. if s n then inv (&2 pow n) else &0)`. Specifically, if sequences `s` and `t` differ at some point `n` where `s(n)` is `F` and `t(n)` is `T`, and `s` has infinitely many `F` values, then the sum from `s` is less than the sum from `t`. This is important for reasoning about the uniqueness of binary representations and their corresponding real numbers.

### Dependencies

**Theorems/Definitions:**
- `Library/analysis.ml`
- `REAL_LTE_TRANS`
- `SEQ_LE`
- `SEQ_CONST`
- `sums`
- `SUMS_BINSEQUENCE`
- `SUM_SPLIT`
- `SUM_1`
- `REAL_LET_TRANS`
- `SUM_BINSEQUENCE_UBOUND_SHARP`
- `SUM_BINSEQUENCE_UBOUND_LE`
- `REAL_ARITH`
- `REAL_FIELD`
- `SUM_EQ`
- `LE_0`
- `ADD_CLAUSES`

**Lemmas:**
- `SUM_BINSEQUENCE_LBOUND`
- `SUMMABLE_BINSEQUENCE`
- `SUMMABLE_SUM`

### Porting notes (optional)
- The proof relies heavily on real number arithmetic and inequalities. Ensure that the target proof assistant has adequate support for automation with real numbers.
- HOL Light's `REAL_ARITH` tactic is particularly powerful; reconstructing its behavior may be necessary in other systems.
- The usage of `EXISTS_TAC` followed by arithmetic simplifications is a common pattern. Ensure the target system can handle existential instantiation and subsequent simplification steps efficiently.
- The conversion from `summable` to `sums` and `convergent` should be checked against the definition of these lemmas.


---

## UNCOUNTABLE_REALS

### Name of formal statement
UNCOUNTABLE_REALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNCOUNTABLE_REALS = prove
 (`~countable(UNIV:real->bool)`,
  MP_TAC UNCOUNTABLE_CANONICAL THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  REWRITE_TAC[countable] THEN DISCH_TAC THEN
  TRANS_TAC CARD_LE_TRANS `UNIV:real->bool` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC `\s. suminf(\n. if s(n) then inv(&2 pow n) else &0)` THEN
  REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  REWRITE_TAC[canonical; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_REWRITE_TAC I [MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `n = minimal x. ~(s x <=> t x)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_var o rhs o concl)) THEN
  ASM_CASES_TAC `(t:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> a = b ==> F`);
    MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`)] THEN
  MATCH_MP_TAC SUMINF_INJ_LEMMA THEN ASM_MESON_TAC[]);;
```
### Informal statement
The set of functions from natural numbers to Booleans, i.e., `real -> bool`, is not countable.

### Informal sketch
The proof demonstrates that the set of all functions from natural numbers to Booleans is uncountable, using a diagonalization argument.
- First, the proof assumes that the set of functions from natural numbers to Booleans is countable.
- Then, it considers an arbitrary enumeration of these functions and constructs a real number in the interval `[0, 1]` using an infinite sum based on the values of each function in the enumeration. Namely, for each function `s`, we consider `suminf(\n. if s(n) then inv(&2 pow n) else &0)`.
- The proof then shows that this mapping from functions to real numbers is injective, meaning that distinct functions map to distinct real numbers. It does this by case-splitting on whether `t n` holds, where `n` is the minimal number such that `s n` and `t n` differ.
- Using `SUMINF_INJ_LEMMA`, the proof constructs a contradiction thus showing that the assumption of countability must be false.

### Mathematical insight
This theorem demonstrates the uncountability of the real numbers by showing that the set of functions from natural numbers to booleans (which can be regarded as the set of subsets of natural numbers) is uncountable, and then mapping these to the real numbers via a convergent sum. The core idea is to use diagonalization to construct a real number that differs from every real number in a hypothetical enumeration. This theorem is a fundamental result in set theory and analysis.

### Dependencies
- `countable`
- `UNCOUNTABLE_CANONICAL` (used by `MP_TAC`)
- `CONTRAPOS_THM`
- `CARD_LE_TRANS`
- `le_c`
- `IN_UNIV`
- `canonical`
- `IN_ELIM_THM`
- `FUN_EQ_THM`
- `MINIMAL`
- `SUMINF_INJ_LEMMA`
- `REAL_ARITH`


---

