# ratcountable.ml

## Overview

Number of statements: 6

The `ratcountable.ml` file proves Theorem 3, which establishes the countability of rational numbers. It relies on the `card.ml` library, suggesting a connection to cardinality and set theory. The file's content is focused on formalizing the concept of countability in the context of rational numbers, providing a foundation for further results in number theory or real analysis. The proven theorem is a fundamental result in mathematics, making this file a crucial component of the larger library.

## rational

### Name of formal statement
rational

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rational = new_definition
  `rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)`
```

### Informal statement
The predicate `rational(r)` is defined to be true if and only if there exist integers `p` and `q`, where `q` is not equal to 0, such that the absolute value of `r` is equal to `p` divided by `q`.

### Informal sketch
* The definition of `rational(r)` involves existential quantification over integers `p` and `q`.
* The condition `~(q = 0)` ensures that `q` is non-zero, which is necessary for the division `&p / &q` to be well-defined.
* The use of `abs(r)` implies that the definition is concerned with the absolute value of `r`, rather than its signed value.
* The `new_definition` tactic is used to introduce this definition into the theory.

### Mathematical insight
This definition captures the standard mathematical notion of a rational number, which is a number that can be expressed as the quotient of two integers. The use of absolute value ensures that the definition applies to both positive and negative rational numbers.

### Dependencies
* `new_definition`
* `abs`
* Arithmetic operations and predicates (e.g., `&p / &q`, `~(q = 0)`)

### Porting notes
When porting this definition to other proof assistants, note that the exact syntax for existential quantification and division may vary. Additionally, the treatment of absolute value and integer division may differ between systems, so care should be taken to ensure that the ported definition accurately captures the original mathematical intent.

---

## countable

### Name of formal statement
countable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;
```

### Informal statement
The set `s` is countable if and only if `s` is less than or equal to the set of all natural numbers to booleans (`UNIV:num->bool`) in terms of cardinality.

### Informal sketch
* The definition of `countable` involves a comparison of cardinalities between the set `s` and the set of all functions from natural numbers to booleans (`UNIV:num->bool`).
* The relation `<=_c` denotes a cardinality comparison, where `s <=_c t` means that the cardinality of `s` is less than or equal to the cardinality of `t`.
* To prove that a set `s` is countable, one would need to establish that there exists an injection from `s` into `UNIV:num->bool`, which demonstrates that `s` has a cardinality less than or equal to that of `UNIV:num->bool`.

### Mathematical insight
The concept of countability is fundamental in set theory and real analysis. A set is considered countable if its elements can be put into a one-to-one correspondence with the natural numbers. This definition in HOL Light formalizes countability in terms of cardinality comparison with the set of all functions from natural numbers to booleans, which serves as a representative for the set of natural numbers itself. This formulation is crucial for various mathematical proofs and constructions, especially those involving infinite sets and sequences.

### Dependencies
* `new_definition`
* `<=_c`
* `UNIV:num->bool`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles cardinality comparisons and the representation of the set of natural numbers. Specifically, ensure that the translation preserves the one-to-one correspondence nature of countability and correctly represents the cardinality relation `<=_c`. Additionally, consider the specific constructs or tactics available in the target system for defining and working with countable sets.

---

## COUNTABLE_RATIONALS

### Name of formal statement
COUNTABLE_RATIONALS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COUNTABLE_RATIONALS = prove
 (`countable { x:real | rational(x)}`,
  REWRITE_TAC[countable] THEN TRANS_TAC CARD_LE_TRANS
   `{ x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_C; EXISTS_PAIR_THM; mul_c] THEN
    EXISTS_TAC `\(x,b). if b = 0 then x else --x` THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_ELIM_THM; rational; IN_UNIV; PAIR_EQ] THEN
    MESON_TAC[REAL_ARITH `(abs(x) = a) ==> (x = a) \/ x = --a`];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_MUL_ABSORB_LE THEN REWRITE_TAC[num_INFINITE] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV *_c UNIV):num#num->bool` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_C; EXISTS_PAIR_THM; mul_c; IN_UNIV] THEN
    EXISTS_TAC `\(p,q). &p / &q` THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_ELIM_THM; rational] THEN MESON_TAC[];
    MESON_TAC[CARD_MUL_ABSORB_LE; CARD_LE_REFL; num_INFINITE]])
```

### Informal statement
The set of all real numbers `x` such that `x` is rational is countable. This is proven by showing that the cardinality of the set of rational numbers is less than or equal to the cardinality of the set of natural numbers, which is known to be countable.

### Informal sketch
* The proof starts by applying the `countable` definition and then uses `TRANS_TAC` to establish a chain of inequalities involving cardinalities.
* It then uses `CONJ_TAC` to split the proof into two parts: one for the existence of a certain function and another for the cardinality comparison.
* The first part involves using `EXISTS_TAC` to introduce a function that maps each rational number to a pair of natural numbers, utilizing `GEN_BETA_CONV` for conversion and `MESON_TAC` for deduction.
* The second part applies `MATCH_MP_TAC` with `CARD_MUL_ABSORB_LE` to establish the cardinality comparison, leveraging `num_INFINITE` and further deductions with `MESON_TAC`.
* Key steps involve recognizing the set of rational numbers can be put into a one-to-one correspondence with a subset of the natural numbers, thus showing it is countable.

### Mathematical insight
This theorem is important because it establishes that the set of rational numbers, despite being dense in the real numbers, is countable. This means that every rational number can be uniquely associated with a natural number, which has significant implications in real analysis and the study of infinite sets.

### Dependencies
#### Theorems
* `countable`
* `CARD_MUL_ABSORB_LE`
* `CARD_LE_REFL`
* `num_INFINITE`
#### Definitions
* `rational`
* `countable`
* `LE_C`
* `EXISTS_PAIR_THM`
* `mul_c`
* `IN_ELIM_THM`
* `IN_UNIV`
* `PAIR_EQ`

---

## denumerable

### Name of formal statement
denumerable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let denumerable = new_definition
  `denumerable s <=> s =_c (UNIV:num->bool)`;;
```

### Informal statement
The `denumerable` property of a set `s` holds if and only if `s` is equal to the set of all natural numbers (`UNIV:num->bool`), where equality is considered up to cardinality (`=_c`).

### Informal sketch
* The definition of `denumerable` involves checking if a given set `s` has the same cardinality as the set of all natural numbers.
* This comparison is done using the `_c` equality relation, which considers two sets equal if they have the same cardinality.
* To prove that a set is `denumerable`, one would need to establish a bijection between the set and the natural numbers, leveraging the `UNIV:num->bool` set.

### Mathematical insight
The `denumerable` definition captures the concept of a set being countably infinite, meaning its elements can be put into a one-to-one correspondence with the natural numbers. This is a fundamental concept in set theory and is crucial for understanding various properties of infinite sets.

### Dependencies
#### Definitions
* `=_c`
* `UNIV:num->bool`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles set equality and cardinality. Specifically, ensure that the equivalent of `_c` equality is properly defined and used. Additionally, the representation of the set of all natural numbers (`UNIV:num->bool`) might differ, so it's essential to identify the correct counterpart in the target system.

---

## DENUMERABLE_RATIONALS

### Name of formal statement
DENUMERABLE_RATIONALS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DENUMERABLE_RATIONALS = prove
 (`denumerable { x:real | rational(x)}`,
  REWRITE_TAC[denumerable; GSYM CARD_LE_ANTISYM] THEN
  REWRITE_TAC[GSYM countable; COUNTABLE_RATIONALS] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `&` THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; REAL_OF_NUM_EQ; rational] THEN
  X_GEN_TAC `p:num` THEN MAP_EVERY EXISTS_TAC [`p:num`; `1`] THEN
  REWRITE_TAC[REAL_DIV_1; REAL_ABS_NUM; ARITH_EQ])
```

### Informal statement
The set of all real numbers that are rational is denumerable.

### Informal sketch
* The proof begins by applying the `REWRITE_TAC` with `denumerable` and `GSYM CARD_LE_ANTISYM` to establish the denumerability of the set of rational real numbers.
* It then uses `REWRITE_TAC` with `GSYM countable` and `COUNTABLE_RATIONALS` to relate denumerability to countability, leveraging the known countability of rational numbers.
* The proof proceeds with `REWRITE_TAC` using `le_c` to address the relationship between denumerability and a specific countable set.
* The `EXISTS_TAC `&`` tactic is used to introduce an existential quantifier, which is then followed by `SIMP_TAC` to simplify the statement using several theorems (`IN_ELIM_THM`, `IN_UNIV`, `REAL_OF_NUM_EQ`, and `rational`).
* The `X_GEN_TAC `p:num`` introduces a generic term `p` of type `num`, which is then used in `MAP_EVERY EXISTS_TAC` to instantiate existential quantifiers with `p` and `1`.
* Finally, `REWRITE_TAC` is applied with `REAL_DIV_1`, `REAL_ABS_NUM`, and `ARITH_EQ` to conclude the proof by simplifying arithmetic expressions.

### Mathematical insight
This theorem is important because it establishes that the set of all rational real numbers, despite being a subset of the uncountable set of real numbers, is itself denumerable (or countably infinite). This means that there exists a one-to-one correspondence between the rational numbers and the natural numbers, which is a fundamental property in real analysis and has implications for understanding the nature of infinity and the real number line.

### Dependencies
* Theorems:
  - `denumerable`
  - `GSYM CARD_LE_ANTISYM`
  - `COUNTABLE_RATIONALS`
  - `IN_ELIM_THM`
  - `IN_UNIV`
  - `REAL_OF_NUM_EQ`
  - `rational`
* Definitions:
  - `countable`
  - `le_c`
  - `REAL_DIV_1`
  - `REAL_ABS_NUM`
  - `ARITH_EQ`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles denumerability, countability, and the properties of rational numbers. The use of tactics like `REWRITE_TAC` and `EXISTS_TAC` may have direct counterparts or require rephrasing in terms of the target system's tactics and strategic mechanisms. Additionally, ensuring that the ported version correctly captures the existential quantification and the generic introduction of terms (like `p:num`) will be crucial for maintaining the proof's validity.

---

## DENUMERABLE_RATIONALS_EXPAND

### Name of formal statement
DENUMERABLE_RATIONALS_EXPAND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DENUMERABLE_RATIONALS_EXPAND = prove
 (`?rat:num->real. (!n. rational(rat n)) /\
                   (!x. rational x ==> ?!n. x = rat n)`,
  MP_TAC DENUMERABLE_RATIONALS THEN REWRITE_TAC[denumerable] THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[eq_c] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;
```

### Informal statement
There exists a function `rat` from natural numbers to real numbers such that for all natural numbers `n`, `rat n` is rational, and for all rational numbers `x`, there exists a unique natural number `n` such that `x` equals `rat n`.

### Informal sketch
* The proof starts by applying the `DENUMERABLE_RATIONALS` theorem using `MP_TAC`.
* It then expands the `denumerable` definition using `REWRITE_TAC`.
* The `CARD_EQ_SYM` and `eq_c` theorems are applied to simplify the cardinality comparison.
* The `IN_UNIV` and `IN_ELIM_THM` theorems are used to rewrite the membership and elimination rules.
* The `MONO_EXISTS` theorem is applied using `MATCH_MP_TAC` to establish the existence of a unique `n` for each rational `x`.
* Finally, `MESON_TAC` is used to derive the conclusion.

### Mathematical insight
This theorem establishes the existence of a bijection between the natural numbers and the rational numbers, which is a fundamental result in set theory and real analysis. The `DENUMERABLE_RATIONALS_EXPAND` theorem provides an explicit construction of this bijection, which is essential for various applications in mathematics and computer science.

### Dependencies
* Theorems:
	+ `DENUMERABLE_RATIONALS`
	+ `CARD_EQ_SYM`
	+ `eq_c`
	+ `IN_UNIV`
	+ `IN_ELIM_THM`
	+ `MONO_EXISTS`
* Definitions:
	+ `denumerable`
	+ `rational`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of binders and quantifiers. The `?rat` and `!n` quantifiers may need to be explicitly defined or bounded in the target system. Additionally, the `REWRITE_TAC` and `MATCH_MP_TAC` tactics may have different counterparts in other systems, and the `MESON_TAC` tactic may require manual instantiation of the `MONO_EXISTS` theorem.

---

