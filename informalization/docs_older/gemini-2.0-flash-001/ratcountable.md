# ratcountable.ml

## Overview

Number of statements: 6

`ratcountable.ml` formalizes the countability of the set of rational numbers. It resides within the HOL Light library and relies on the cardinality theory from `card.ml`. The file likely contains definitions and theorems related to bijections between the natural numbers and the rational numbers, demonstrating their equinumerosity.


## rational

### Name of formal statement
rational

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rational = new_definition
  `rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)`;;
```

### Informal statement
The real number `r` is rational if and only if there exist natural numbers `p` and `q` such that `q` is not equal to 0 and the absolute value of `r` equals the real number `p` divided by the real number `q`.

### Informal sketch
The definition introduces the concept of a rational number. It asserts that a real number `r` is rational if there exists two natural numbers `p` and `q` such that `q` is non-zero, and the absolute value of `r` can be expressed as the real number `p` divided by the real number `q`. The core idea is to formally capture the notion of a fraction `p/q`. Note that natural numbers `p` and `q` are converted into real numbers `&p` and `&q` using the `&` injection from natural numbers to real numbers.

### Mathematical insight
This definition formalizes the standard mathematical definition of a rational number. It is important because it provides a rigorous basis for reasoning about rational numbers within the formal system. The use of `abs(r)` ensures that both positive and negative rational numbers are included. Representing `p` and `q` as natural numbers is standard when defining rationals. `q` must be shown to be non-zero to avoid division by zero.

### Dependencies
- **Files**: `Library/card.ml`
- **Theorems/Definitions**: `abs`, `/`, `&`

### Porting notes (optional)
- In other proof assistants like Coq or Lean, the definition of rational numbers might already exist in the standard library. If so, this definition can be used to prove equivalence with any existing definition. When porting, ensure that the division operator is defined appropriately for real numbers and that there's a mechanism to inject natural numbers into real numbers (similar to HOL Light's `&` operator). The handling of quantifiers and the non-zero constraint on `q` should be straightforward in most proof assistants.


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
For any set `s`, `countable s` is defined to be true if and only if `s` is cardinally less than or equal to the set of all functions from natural numbers to booleans (i.e., `UNIV:num->bool`).

### Informal sketch
- The definition introduces the concept of countability by comparing the cardinality of a set `s` to the cardinality of the set of all functions from natural numbers to booleans.
- The relation `<=_c` represents the cardinal inequality.
- `(UNIV:num->bool)` represents the universe of all functions from natural numbers (`num`) to booleans (`bool`), which has the same cardinality as the power set of natural numbers. Therefore, a set `s` is countable if its cardinality is less than or equal to the cardinality of the power set of natural numbers.

### Mathematical insight
This definition formalizes the notion of countability by stating that a set is countable if it is no larger in cardinality than the set of all functions from natural numbers to booleans, which is equivalent to the power set of natural numbers. Sets that are cardinally less than or equal to the power set of naturals are, by definition, at most countable.

### Dependencies
- Definition: `cardinal_le` (denoted here as `<=_c`)


---

## COUNTABLE_RATIONALS

### Name of formal statement
COUNTABLE_RATIONALS

### Type of the formal statement
theorem

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
    MESON_TAC[CARD_MUL_ABSORB_LE; CARD_LE_REFL; num_INFINITE]]);;
```
### Informal statement
The set of real numbers that are rational is countable.

### Informal sketch
The proof demonstrates that the set of rational real numbers is countable by showing that it has the same cardinality as a subset of the natural numbers and then showing the cardinality is infinite.
- First, use the fact that the set of real numbers `x` such that `rational(x)` is countable (using the theorem `countable`). Then, use the fact that the cardinality of a set is preserved under a cardinality less than or equal to another set.
- Show that the set `{ x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)` (the cartesian product of the real numbers equal to a rational with the boolean universe)
- Break this into two subgoals
  - First, show that `countable { x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)` . This is achieved by rewriting with lemmas about the cardinality of cartesian products and the existence of pairs, demonstrating that the absolute value function maps pairs to rational numbers, and applying `REAL_ARITH`.
  - Second, show that the cardinality of `{ x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)` is less than or equal to the cardinality of the natural number universe crossed with itself.
- Apply a theorem stating that the cardinality of something that absorbs multiplication is less than or equal to another, rewriting with the fact that the number universe is infinite, and transition with another cardinality less than or equal to another statement, specifically `(UNIV *_c UNIV):num#num->bool)`.
- Split into two subgoals again:
  - The first subgoal requires showing `(UNIV:num#num) <=c { x:real | rational x }`. This is accomplished by rewriting with lemmas about cardinality, existence of pairs, and the fact that everything is in the universe, applying an existential quantifier to `\(p,q). &p / &q`, beta reducing, rewriting with `rational`, and using Meson.
  - The second subgoal requires showing `(UNIV:num#num) <=c (UNIV:num) *_c (UNIV:bool)`. This is accomplished by using Meson with `CARD_MUL_ABSORB_LE`, `CARD_LE_REFL`, and `num_INFINITE`.

### Mathematical insight
The theorem formalizes the well-known mathematical fact that the set of rational numbers is countable, meaning that it can be put into a one-to-one correspondence with the set of natural numbers. This is a foundational result in real analysis and set theory.

### Dependencies
- `countable`
- `CARD_LE_TRANS`
- `LE_C`
- `EXISTS_PAIR_THM`
- `mul_c`
- `IN_ELIM_THM`
- `rational`
- `IN_UNIV`
- `PAIR_EQ`
- `REAL_ARITH`
- `CARD_MUL_ABSORB_LE`
- `num_INFINITE`
- `CARD_LE_REFL`


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
For any set `s`, `denumerable s` is true if and only if `s` is in bijection with the set of all functions from natural numbers to booleans (`UNIV:num->bool`).

### Informal sketch
- The definition introduces a predicate `denumerable` that characterizes sets that have the same cardinality as `(UNIV:num->bool)`.
- The definition directly equates `denumerable s` with the condition that `s` is in bijection with `(UNIV:num->bool)` using the `=_c` operator, which denotes equipotence (same cardinality).

### Mathematical insight
This definition characterizes sets that have the cardinality of the power set of the natural numbers, namely, the cardinality of the continuum. It is defining what it means for a set to be "denumerable" in the sense that it can be put into a one-to-one correspondence with the set of all functions from natural numbers to Booleans. This is a non-standard use of the term "denumerable", which usually means "countable". A more appropriate name for this predicate would be `uncountable`.

### Dependencies
- `=_c` (equipotence relation)
- `UNIV:num->bool` (the set of all functions from natural numbers to booleans.)


---

## DENUMERABLE_RATIONALS

### Name of formal statement
DENUMERABLE_RATIONALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DENUMERABLE_RATIONALS = prove
 (`denumerable { x:real | rational(x)}`,
  REWRITE_TAC[denumerable; GSYM CARD_LE_ANTISYM] THEN
  REWRITE_TAC[GSYM countable; COUNTABLE_RATIONALS] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `&` THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; REAL_OF_NUM_EQ; rational] THEN
  X_GEN_TAC `p:num` THEN MAP_EVERY EXISTS_TAC [`p:num`; `1`] THEN
  REWRITE_TAC[REAL_DIV_1; REAL_ABS_NUM; ARITH_EQ]);;
```
### Informal statement
The set of real numbers that are rational is denumerable.

### Informal sketch
The proof demonstrates that the set of rational real numbers is denumerable.
- It starts by using the fact that a set is denumerable if it is countable and infinite.
- It then uses the theorem `COUNTABLE_RATIONALS`, which states that the set of rationals is countable.
- The proof establishes that there is a real number `&` (which is 0) that is rational.
- It proceeds to show that for any natural number `p`, the real number `p/1` is rational.
- Finally, it uses rewrite rules to simplify `p/1` to `abs(p)`, which further simplifies to `p`.

### Mathematical insight
The theorem `DENUMERABLE_RATIONALS` formally states a fundamental property of the rational numbers, namely, that they can be put into a one-to-one correspondence with the natural numbers. This is a foundational result in set theory and analysis, demonstrating that even though rationals are dense in the reals, their cardinality is the same as that of the natural numbers.

### Dependencies
- Theorems: `denumerable`, `CARD_LE_ANTISYM`, `countable`, `COUNTABLE_RATIONALS`, `le_c`, `IN_ELIM_THM`, `IN_UNIV`, `REAL_OF_NUM_EQ`, `rational`, `REAL_DIV_1`, `REAL_ABS_NUM`, `ARITH_EQ`


---

## DENUMERABLE_RATIONALS_EXPAND

### Name of formal statement
DENUMERABLE_RATIONALS_EXPAND

### Type of the formal statement
theorem

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
There exists a function `rat` from natural numbers to real numbers such that every `rat n` is a rational number, and for every rational number `x`, there exists a natural number `n` such that `x = rat n`.

### Informal sketch
The proof demonstrates that the set of rational numbers is denumerable by expanding the cardinal comparison definitions for explicitness.
- Apply the theorem `DENUMERABLE_RATIONALS`, which establishes that the cardinality of the set of rational numbers is equal to the cardinality of the set of natural numbers.
- Rewrite using the definition `denumerable`, which states that a set is denumerable if it is equinumerous with the entire universe `UNIV`.
- Rewrite the cardinal equality `CARD_EQ_SYM` to orient it in the preferred direction.
- Rewrite using the definition `eq_c`, which likely expands cardinal equality into existence of a bijection.
- Rewrite using `IN_UNIV` (everything is in the universe) and `IN_ELIM_THM` to clarify set membership.
- Apply `MONO_EXISTS` and then use `MESON_TAC` to complete the proof.

### Mathematical insight
This theorem explicitly constructs a function that enumerates the rational numbers. It formalizes the well-known mathematical fact that the set of rational numbers is countable, meaning it can be put into a one-to-one correspondence with the natural numbers. The expansion of cardinal comparison definitions provides a more explicit representation of this enumeration.

### Dependencies
- Theorems: `DENUMERABLE_RATIONALS`
- Definitions: `denumerable`, `eq_c`
- Theorems/Rules: `IN_UNIV`, `IN_ELIM_THM`, `CARD_EQ_SYM`, `MONO_EXISTS`


---

