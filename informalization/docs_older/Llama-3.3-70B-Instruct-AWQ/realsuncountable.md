# realsuncountable.ml

## Overview

Number of statements: 12

The `realsuncountable.ml` file formalizes the proof of the non-denumerability of the continuum, also known as the uncountability of the real numbers. It builds upon concepts from cardinality theory and real analysis, as indicated by its imports from `card.ml` and `analysis.ml`. The file defines and proves key theorems related to this fundamental result in set theory. Its purpose is to establish the uncountability of the real numbers within the HOL Light system.

## countable

### Name of formal statement
countable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let countable = new_definition `countable s <=> s <=_c (UNIV:num->bool)`;;
```

### Informal statement
A set `s` is countable if and only if `s` is less than or equal to the set of all natural numbers to booleans (`UNIV:num->bool`) in terms of cardinality.

### Informal sketch
* The definition of `countable` relies on the concept of cardinality comparison (`<=_c`).
* It involves comparing the cardinality of any set `s` with that of the set of all functions from natural numbers to booleans (`UNIV:num->bool`).
* The key idea is to establish a condition under which a set is considered countable, which is fundamental in understanding the size of infinite sets.

### Mathematical insight
This definition is crucial in set theory and real analysis, as it provides a way to distinguish between countable and uncountable sets. The concept of countability is central in understanding the nature of infinite sets and their properties. This definition, in particular, relates to the broader context of comparing the sizes of infinite sets, which is essential in various areas of mathematics, including topology and measure theory.

### Dependencies
* `new_definition`
* `<=_c`
* `UNIV:num->bool`

### Porting notes
When translating this definition into another proof assistant, pay close attention to how cardinality comparisons are handled, as different systems may have different notations or constructs for this concept. For example, in Lean, you might use `≤` for cardinality comparison, while in Coq, you might need to use a specific library or module that deals with cardinalities of sets. Ensure that the translation accurately reflects the original intention and mathematical structure of the HOL Light definition.

---

## repeating

### Name of formal statement
repeating

### Type of the formal statement
new_definition

### Formal Content
```ocaml
repeating = {s:num->bool | ?n. !m. m >= n ==> s m}
```

### Informal statement
The `repeating` set is defined as the collection of all functions `s` from natural numbers to boolean values, such that there exists a natural number `n` and for all natural numbers `m` greater than or equal to `n`, `s m` holds true.

### Informal sketch
* The definition involves an existential quantifier `?n` to assert the existence of a threshold `n`.
* For any `m` greater than or equal to this threshold `n`, the function `s` applied to `m` yields `true`.
* The universal quantifier `!m` ensures this condition holds for all `m` meeting the threshold condition.
* The definition does not specify how `s` behaves for values of `m` less than `n`, only that there exists an `n` after which `s m` is always `true`.

### Mathematical insight
The `repeating` definition captures the concept of a function that, after a certain point, consistently returns `true` for all subsequent inputs. This is a fundamental idea in defining repeating or periodic behaviors in discrete mathematics and can be crucial in various proofs and constructions, especially those involving limits, sequences, or recursive functions.

### Dependencies
* `num`: the type of natural numbers
* `bool`: the type of boolean values
* Implicit dependencies on basic logical and set theoretic constructs, such as existential and universal quantification, and function types.

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system represents functions, sets, and quantifiers. Specifically, the use of `?n` for existential quantification and `!m` for universal quantification may be represented differently. For example, in Lean, this might be expressed using `∃ n, ∀ m ≥ n, s m`. Additionally, ensure that the target system's type system and logic can naturally express the concept of a function from natural numbers to booleans and the subset definition as given.

---

## BINARY_BOUND

### Name of formal statement
BINARY_BOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BINARY_BOUND = prove
(`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_0; EXP_ADD; EXP_1; EXP] THEN
  ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `2` raised to the power of `i` if `b(i)` is true, otherwise `0`, is less than `2` raised to the power of `n + 1`.

### Informal sketch
* The proof proceeds by induction on `n`.
* The base case is established using `COND_CASES_TAC` and `REWRITE_TAC[ARITH]`.
* The inductive step involves rewriting the sum using `NSUM_CLAUSES_NUMSEG` and applying `INDUCT_TAC`.
* The `POP_ASSUM MP_TAC` and `REWRITE_TAC[LE_0; EXP_ADD; EXP_1; EXP]` steps are used to simplify the expression and apply properties of exponentiation.
* Finally, `ARITH_TAC` is used to complete the proof.

### Mathematical insight
This theorem provides a bound on the sum of a sequence of powers of 2, which is useful in various applications such as combinatorics and computer science. The proof illustrates the use of induction and properties of arithmetic operations to establish the bound.

### Dependencies
* `NSUM_CLAUSES_NUMSEG`
* `EXP_ADD`
* `EXP_1`
* `EXP`
* `LE_0`
* `ARITH`

### Porting notes
When porting this theorem to another proof assistant, note that the `INDUCT_TAC` and `REWRITE_TAC` tactics may need to be replaced with equivalent constructs. Additionally, the `ARITH_TAC` tactic may need to be replaced with a more general arithmetic solver or a custom implementation. The `COND_CASES_TAC` tactic may also require special handling, depending on the target proof assistant's support for conditional expressions.

---

## BINARY_DIV_POW2

### Name of formal statement
BINARY_DIV_POW2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BINARY_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0`,
  SIMP_TAC[ADD1; DIV_LT; BINARY_BOUND])
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `2` raised to the power of `i` if `b(i)` is true, otherwise `0`, divided by `2` raised to the power of `n+1`, equals `0`.

### Informal sketch
* The proof involves showing that the sum of terms `2` raised to the power of `i` (if `b(i)` is true) from `0` to `n` is less than `2` raised to the power of `n+1`.
* This is achieved by using the `SIMP_TAC` tactic with theorems `ADD1`, `DIV_LT`, and `BINARY_BOUND`.
* The `SIMP_TAC` tactic is used to simplify the expression by applying the given theorems.
* The `ADD1` theorem is likely used to handle the sum, `DIV_LT` for division properties, and `BINARY_BOUND` for bounds related to binary representation.

### Mathematical insight
This theorem is important because it provides a property about the divisibility of sums of powers of 2 by higher powers of 2, which can be crucial in number theory and computer science, especially in contexts involving binary arithmetic.

### Dependencies
* Theorems:
  + `ADD1`
  + `DIV_LT`
  + `BINARY_BOUND`

### Porting notes
When porting this theorem to another proof assistant, pay special attention to how the `nsum` function and the `DIV` operation are handled, as different systems may have varying levels of support for these constructs. Additionally, the `SIMP_TAC` tactic and its parameters may need to be translated into equivalent tactics or simplification strategies in the target system.

---

## PLUS_MOD_REFL

### Name of formal statement
PLUS_MOD_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PLUS_MOD_REFL = prove
 (`!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_EQ THEN MESON_TAC[MULT_CLAUSES])
```

### Informal statement
For all integers `a` and `b`, if `b` is not equal to 0, then the remainder of `a + b` divided by `b` is equal to the remainder of `a` divided by `b`.

### Informal sketch
* The proof starts by assuming `b` is not equal to 0.
* It then applies the `MOD_EQ` theorem to establish the equality of the remainders.
* The `REPEAT STRIP_TAC` tactic is used to strip away any universal quantifiers and implications.
* The `MATCH_MP_TAC` tactic is used to apply the `MOD_EQ` theorem.
* Finally, `MESON_TAC` is used with `MULT_CLAUSES` to simplify and derive the desired conclusion.

### Mathematical insight
This theorem provides a fundamental property of modular arithmetic, which is crucial in many areas of mathematics and computer science. It states that adding a multiple of the modulus to a number does not change its remainder when divided by the modulus.

### Dependencies
* Theorems: `MOD_EQ`
* Definitions: `MULT_CLAUSES`

### Porting notes
When porting this theorem to other proof assistants, note that the `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics or strategies. Additionally, the `MESON_TAC` tactic with `MULT_CLAUSES` may require manual rewriting or the use of a similar automation mechanism.

---

## BINARY_PLUS_DIV_POW2

### Name of formal statement
BINARY_PLUS_DIV_POW2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BINARY_PLUS_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` THEN
  ASM_REWRITE_TAC[BINARY_BOUND; ADD1] THEN
  REWRITE_TAC[ADD_AC; MULT_CLAUSES])
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `2` raised to the power of `i` if `b(i)` is true, otherwise `0`, plus `2` raised to the power of `n+1`, divided by `2` raised to the power of `n+1`, equals `1`.

### Informal sketch
* The proof starts by generalizing the statement for all `n` using `GEN_TAC`.
* It then applies `MATCH_MP_TAC` with `DIV_UNIQ` to establish the uniqueness of the divisor.
* The existence of the sum `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` is asserted using `EXISTS_TAC`.
* The proof then applies `ASM_REWRITE_TAC` with `BINARY_BOUND` and `ADD1` to simplify the expression.
* Finally, `REWRITE_TAC` is applied with `ADD_AC` and `MULT_CLAUSES` to further simplify and establish the equality.

### Mathematical insight
This theorem appears to be related to properties of binary numbers and their representation. The statement involves a sum of powers of `2` conditioned on a predicate `b(i)`, which suggests a connection to binary digits or bits. The division by `2` raised to the power of `n+1` implies a normalization or scaling of the sum. Understanding this theorem requires insight into binary arithmetic and the properties of divisibility.

### Dependencies
* Theorems:
	+ `DIV_UNIQ`
* Definitions:
	+ `BINARY_BOUND`
	+ `ADD1`
	+ `ADD_AC`
	+ `MULT_CLAUSES`
* Other:
	+ `nsum` (a function for summing over a range)
	+ `b` (a predicate function)

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of the `nsum` function, the predicate `b(i)`, and the use of `GEN_TAC` and `MATCH_MP_TAC` for generalization and applying theorems. Additionally, the `EXISTS_TAC` and `ASM_REWRITE_TAC` tactics may require careful handling to ensure that the same mathematical structure and reasoning are preserved.

---

## BINARY_UNIQUE_LEMMA

### Name of formal statement
BINARY_UNIQUE_LEMMA

### Type of the formal statement
Theorem

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
    ASM_MESON_TAC[LE_REFL]])
```

### Informal statement
For all natural numbers `n`, if the sum from `0` to `n` of `2` raised to the power of `i` when `b(i)` is true (otherwise `0`) equals the sum from `0` to `n` of `2` raised to the power of `i` when `c(i)` is true (otherwise `0`), then for all `i` less than or equal to `n`, `b(i)` is true if and only if `c(i)` is true.

### Informal sketch
* The proof starts by applying `INDUCT_TAC`, indicating a proof by induction.
* It then applies `REWRITE_TAC` with `NSUM_CLAUSES_NUMSEG` to rewrite the summation.
* The proof proceeds with case analysis using `COND_CASES_TAC` and simplification with `SIMP_TAC` and `ASM_REWRITE_TAC`.
* Key steps involve using `AP_TERM` to apply properties of division and modulo operations, specifically with `BINARY_DIV_POW2` and `BINARY_PLUS_DIV_POW2`.
* The proof concludes by combining results from these analyses to establish the equivalence of `b(i)` and `c(i)` for all `i` within the given range.

### Mathematical insight
This theorem establishes a unique representation property for binary sequences encoded as sums of powers of 2. It states that if two sequences `b` and `c` have the same sum of `2` raised to the power of `i` over a range `0` to `n`, then the sequences must be identical over that range. This is crucial in binary arithmetic and coding theory, where unique representations are fundamental.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`
- `LE`
- `ARITH`
- `ADD_CLAUSES`
- `BINARY_DIV_POW2`
- `BINARY_PLUS_DIV_POW2`
- `BINARY_BOUND`
- `MOD_LT`
- `PLUS_MOD_REFL`
- `EXP_EQ_0`
- `ADD1`
- `LE_REFL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of `nsum` (which might be represented as a summation or a fold), the `AP_TERM` tactic (which applies a term to an assumption), and the various arithmetic properties (`BINARY_DIV_POW2`, etc.). The induction and case analysis steps should be straightforward to translate, but the specific tactics for rewriting and simplification may vary between systems.

---

## COUNTABLE_REPEATING

### Name of formal statement
COUNTABLE_REPEATING

### Type of the formal statement
Theorem

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
   ASM_MESON_TAC[LE_CASES])
```

### Informal statement
The theorem `COUNTABLE_REPEATING` states that there exists a countable set that is repeating. This involves proving that the cardinality of the set of natural numbers to booleans (`UNIV:num->bool`) is less than or equal to the cardinality of the set of natural numbers to booleans squared (`(UNIV:num->bool) *_c (UNIV:num->bool)`). The proof constructs a specific set `s` and uses the `minimal` function to find a natural number `n` such that for all `m` greater than or equal to `n`, `s(m)` holds. It then shows that this set satisfies the `repeating` property.

### Informal sketch
* The proof begins by rewriting the `countable` definition and applying the `TRANS_TAC` tactic to establish a cardinality relationship.
* It then uses `CONJ_TAC` to split the goal into two parts, one of which involves `MATCH_MP_TAC` with `CARD_EQ_IMP_LE` to relate cardinalities.
* The proof constructs a set `s` using the `EXISTS_TAC` tactic and defines `n` as the minimal natural number such that `s(m)` holds for all `m` greater than or equal to `n`.
* The `repeating` property is then established through a series of rewrites and case analyses, including the use of `ASM_CASES_TAC` and `FIRST_X_ASSUM`.
* Key steps involve applying `MINIMAL` to find `k` and `l`, and using `BINARY_UNIQUE_LEMMA` to conclude the proof.

### Mathematical insight
The `COUNTABLE_REPEATING` theorem is significant because it establishes the existence of a countable set that exhibits a repeating pattern. This has implications for understanding the properties of countable sets and their relationships to other mathematical structures. The use of the `minimal` function and the `repeating` property highlights the importance of these concepts in the proof.

### Dependencies
* `countable`
* `CARD_EQ_IMP_LE`
* `CARD_SQUARE_NUM`
* `le_c`
* `repeating`
* `IN_ELIM_THM`
* `mul_c`
* `IN_UNIV`
* `MINIMAL`
* `BINARY_UNIQUE_LEMMA`
* `LE_CASES`

### Porting notes
When translating this theorem into other proof assistants, careful attention should be paid to the handling of cardinalities and the `minimal` function. The use of `EXISTS_TAC` and `CONJ_TAC` may require equivalent tactics in the target system. Additionally, the `repeating` property and its relationship to the constructed set `s` should be carefully preserved. Differences in automation and tactic application between HOL Light and the target system may require adjustments to the proof strategy.

---

## canonical

### Name of formal statement
canonical

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let canonical = new_definition
 `canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)};;
```

### Informal statement
The `canonical` set is defined as the set of all functions `s` from natural numbers to boolean values, such that for all natural numbers `n`, there exists a natural number `m` greater than or equal to `n`, for which `s(m)` is false.

### Informal sketch
* The definition involves a universal quantification over all natural numbers `n`.
* For each `n`, an existential quantification is applied to find a natural number `m` that satisfies two conditions: `m` is greater than or equal to `n`, and `s(m)` is false.
* The use of `!n` (for all `n`) and `?m` (there exists an `m`) indicates a nested quantification structure.
* The condition `~(s m)` implies that the function `s` evaluated at `m` yields `false`.

### Mathematical insight
The `canonical` definition captures the concept of a function from natural numbers to boolean values that has infinitely many `false` values, in the sense that for any given `n`, there is always a larger `m` where the function evaluates to `false`. This definition is important in the context of discussing uncountability, as it provides a way to characterize certain properties of infinite sets.

### Dependencies
* `num`: the type of natural numbers
* `bool`: the type of boolean values
* Basic properties of quantifiers (`!` and `?`)

### Porting notes
When translating this definition into other proof assistants, pay attention to how they handle function types and quantifiers. For example, in Lean, this definition might involve using the `∀` and `∃` quantifiers, along with the `→` function type. In Coq, the definition might use `forall` and `exists` for quantification, and `->` for function types. Ensure that the target system's handling of binders and automation does not introduce unintended changes to the definition's meaning.

---

## UNCOUNTABLE_CANONICAL

### Name of formal statement
UNCOUNTABLE_CANONICAL

### Type of the formal statement
Theorem

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
    REWRITE_TAC[num_INFINITE; CARD_LE_REFL]])
```

### Informal statement
It is not the case that the set `canonical` is countable.

### Informal sketch
* The proof begins by assuming the negation of the goal, i.e., `countable canonical`, and then applies `REWRITE_TAC` with `countable` to unfold the definition of countability.
* It then uses `MP_TAC` with `CANTOR_THM_UNIV` (a theorem about the cardinality of the universe) to derive a contradiction.
* The proof proceeds by showing that `canonical` and `repeating` are disjoint and that their union is the universe, using `CARD_DISJOINT_UNION` and `SUBGOAL_THEN`.
* The tactic `TRANS_TAC` is used with `CARD_LE_TRANS` to establish a series of inequalities between cardinalities, ultimately leading to a contradiction.
* Key steps involve simplifying with `ASM_SIMP_TAC` and using `CONJ_TAC` to split the goal into two parts, one of which involves `MATCH_MP_TAC` with `CARD_ADD_ABSORB_LE`.

### Mathematical insight
This theorem is important because it establishes that the `canonical` set is uncountable, which has significant implications in set theory and real analysis. The proof relies on the properties of cardinalities, particularly the `CANTOR_THM_UNIV` theorem, to derive a contradiction with the assumption of countability.

### Dependencies
* Theorems:
 + `CANTOR_THM_UNIV`
 + `CARD_DISJOINT_UNION`
 + `CARD_NOT_LT`
 + `CARD_LE_TRANS`
 + `CARD_ADD_ABSORB_LE`
* Definitions:
 + `countable`
 + `canonical`
 + `repeating`
 + `num_INFINITE`
 + `IN_UNIV`
 + `EXTENSION`
 + `IN_INTER`
 + `NOT_IN_EMPTY`
 + `IN_ELIM_THM`
 + `GE`
 + `IN_UNION` 

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of cardinalities and the `CANTOR_THM_UNIV` theorem, as these may be represented differently. Additionally, the use of `REWRITE_TAC` and `MP_TAC` may need to be adapted to the target system's rewriting and modus ponens mechanisms.

---

## SUMINF_INJ_LEMMA

### Name of formal statement
SUMINF_INJ_LEMMA

### Type of the formal statement
Theorem

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
     [`\n:num. sum(0,n) (\n. if s n then inv(&2 pow n) else &0)`;
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
    SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]])
```

### Informal statement
For all sequences `s` and `t` and for all natural numbers `n`, if `s(n)` is false, `t(n)` is true, and for all `m` less than `n`, `s(m)` is equivalent to `t(m)`, and for all `n`, there exists a natural number `m` greater than or equal to `n` such that `s(m)` is false, then the sum of the infinite series of `1/2^n` if `s(n)` is true and `0` otherwise is less than the sum of the infinite series of `1/2^n` if `t(n)` is true and `0` otherwise.

### Informal sketch
* The proof starts by applying `REAL_LTE_TRANS` to establish a transitive relationship between the sums of two infinite series.
* It then uses `MATCH_MP_TAC` with `SEQ_LE` to compare the sums of the series up to `n+1` and `n`.
* The `SUMS_BINSEQUENCE` theorem is used to relate the sum of the infinite series to the sum of the first `n` terms.
* The proof then proceeds by case analysis on `p`, where `p` is either `0` or `1 + PRE p`, to establish the inequality between the sums.
* The `REAL_LE_TRANS` tactic is used again to establish the final inequality.
* Key HOL Light terms used include `SUMINF`, `sum`, `SEQ_LE`, `REAL_LTE_TRANS`, `SUMS_BINSEQUENCE`, and `REAL_LE_INV_EQ`.

### Mathematical insight
This theorem provides a way to compare the sums of infinite series based on the properties of the sequences `s` and `t`. The key idea is to use the transitive property of inequality to establish a relationship between the sums of the series. The theorem relies on the `SUMS_BINSEQUENCE` theorem, which relates the sum of an infinite series to the sum of its first `n` terms. The proof also uses case analysis and properties of inequalities to establish the final result.

### Dependencies
* Theorems:
	+ `REAL_LTE_TRANS`
	+ `SEQ_LE`
	+ `SUMS_BINSEQUENCE`
	+ `REAL_LE_INV_EQ`
	+ `SUM_BINSEQUENCE_UBOUND_SHARP`
	+ `SUM_BINSEQUENCE_LBOUND`
* Definitions:
	+ `SUMINF`
	+ `sum`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the exact relationships between the sequences `s` and `t` and the sums of the infinite series. The use of `MATCH_MP_TAC` and `REAL_LTE_TRANS` may need to be adapted to the target system's tactic language. Additionally, the `SUMS_BINSEQUENCE` theorem and its dependencies may need to be ported or re-proved in the target system.

---

## UNCOUNTABLE_REALS

### Name of formal statement
UNCOUNTABLE_REALS

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC SUMINF_INJ_LEMMA THEN ASM_MESON_TAC[])
```

### Informal statement
The theorem `UNCOUNTABLE_REALS` states that the set of all real numbers is uncountable. Formally, it proves `~countable(UNIV:real->bool)`, where `UNIV:real->bool` represents the set of all real numbers. This statement involves the negation of the `countable` property applied to the universe of real numbers, indicating that there does not exist a bijection between the natural numbers and the real numbers.

### Informal sketch
* The proof begins by assuming the contrary, i.e., that the set of real numbers is countable, and then derives a contradiction.
* It utilizes the `UNCOUNTABLE_CANONICAL` theorem and applies several rewriting tactics to transform the statement into a more manageable form.
* The proof then proceeds by cases, considering two real-valued sequences `s` and `t`, and leveraging the `canonical` representation of real numbers.
* A key step involves defining a function `n` as the minimal index where `s` and `t` differ, and then using this `n` to construct a contradiction.
* The `SUMINF_INJ_LEMMA` is used to establish the injectivity of a certain summation function, which is crucial for deriving the contradiction.
* Throughout the proof, various logical equivalences and arithmetic properties are applied to simplify and reorganize the statements.

### Mathematical insight
The theorem `UNCOUNTABLE_REALS` is fundamental in establishing the uncountability of the real numbers, a result that has far-reaching implications in mathematics, particularly in real analysis and set theory. The proof relies on a diagonalization argument, which is a common technique used to demonstrate the uncountability of infinite sets. The construction of the real numbers as infinite sequences and the use of the `SUMINF_INJ_LEMMA` highlight the intricate properties of real analysis that underpin this result.

### Dependencies
#### Theorems
* `UNCOUNTABLE_CANONICAL`
* `CONTRAPOS_THM`
* `SUMINF_INJ_LEMMA`
* `REAL_ARITH`
#### Definitions
* `countable`
* `canonical`
* `IN_UNIV`
* `IN_ELIM_THM`
* `FUN_EQ_THM`
* `MINIMAL`

---

