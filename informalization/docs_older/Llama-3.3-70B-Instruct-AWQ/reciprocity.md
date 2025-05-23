# reciprocity.ml

## Overview

Number of statements: 38

The `reciprocity.ml` file formalizes the concept of quadratic reciprocity, a fundamental theorem in number theory. It builds upon definitions and results imported from `prime.ml`, `pocklington.ml`, and `products.ml`, suggesting a focus on prime numbers, primality tests, and algebraic constructions. The file likely contains theorems and proofs related to the quadratic reciprocity law, which describes the relationship between the Legendre symbols of two numbers. Its purpose is to provide a formal foundation for quadratic reciprocity within the HOL Light library.

## IN_NUMSEG_1

### Name of formal statement
IN_NUMSEG_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IN_NUMSEG_1 = prove
 (`!p i. i IN 1..p - 1 <=> 0 < i /\ i < p`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC)
```

### Informal statement
For all integers `p` and `i`, `i` is an element of the set `{1, 2, ..., p-1}` if and only if `0` is less than `i` and `i` is less than `p`.

### Informal sketch
* The proof involves rewriting the statement using the `IN_NUMSEG` definition.
* Then, it applies arithmetic tactics (`ARITH_TAC`) to simplify and prove the equivalence.
* The key step is transforming the set membership `i IN 1..p - 1` into a logical statement about inequalities.
* The `REWRITE_TAC` with `IN_NUMSEG` helps to express set membership in terms of inequalities, which can then be directly compared using arithmetic properties.

### Mathematical insight
This theorem provides a basic property of finite segments of integers, relating set notation to inequality expressions. It's essential for further developments involving integer sequences, arithmetic progressions, or combinatorial arguments.

### Dependencies
* `IN_NUMSEG`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles arithmetic and set membership. Specifically, ensure that the equivalent of `IN_NUMSEG` is defined and that arithmetic tactics or simplification procedures are applied correctly to prove the equivalence. Note that the automation level and the specific tactics available might differ between systems.

---

## EVEN_DIV

### Name of formal statement
EVEN_DIV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EVEN_DIV = prove
 (`!n. EVEN n <=> n = 2 * (n DIV 2)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_MOD] THEN
  MP_TAC(SPEC `n:num` (MATCH_MP DIVISION (ARITH_RULE `~(2 = 0)`))) THEN
  ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, `n` is even if and only if `n` is equal to 2 times the integer division of `n` by 2.

### Informal sketch
* The proof starts by assuming an arbitrary natural number `n`.
* It then applies a rewriting step using the `EVEN_MOD` rule to transform the statement about evenness into a form that can be manipulated algebraically.
* The `DIVISION` rule is applied, specifically tailored for `n` and the fact that 2 is not equal to 0, to introduce the concept of integer division.
* Finally, arithmetic manipulation (`ARITH_TAC`) is used to establish the equivalence between the original statement of evenness and the expression involving integer division.

### Mathematical insight
This theorem provides a fundamental property of even numbers, relating the concept of evenness to the operation of integer division. It's crucial for establishing various arithmetic properties and is a basic building block in number theory, showcasing how a number's evenness can be characterized through division by 2.

### Dependencies
#### Theorems and definitions
* `EVEN`
* `EVEN_MOD`
* `DIVISION`
* `ARITH_RULE`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles arithmetic, especially integer division and the representation of even numbers. The `EVEN_MOD` rule and the `DIVISION` theorem may need to be reformulated or replaced with equivalent constructs in the target system. Additionally, the automation level and tactic structure might differ, requiring adjustments to achieve a similar proof flow.

---

## CONG_MINUS1_SQUARE

### Name of formal statement
CONG_MINUS1_SQUARE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONG_MINUS1_SQUARE = prove
 (`2 <= p ==> ((p - 1) * (p - 1) == 1) (mod p)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cong; nat_mod; ARITH_RULE `(2 + x) - 1 = x + 1`] THEN
  MAP_EVERY EXISTS_TAC [`0`; `d:num`] THEN ARITH_TAC)
```

### Informal statement
For all `p`, if `2` is less than or equal to `p`, then `(p - 1) * (p - 1)` is congruent to `1` modulo `p`.

### Informal sketch
* Start with the assumption that `2` is less than or equal to `p`.
* Use `SIMP_TAC` to simplify the implication and `LE_EXISTS` and `LEFT_IMP_EXISTS_THM` to handle existential quantification.
* Apply `REPEAT STRIP_TAC` to remove any universal quantifiers and implications.
* Employ `REWRITE_TAC` to rewrite the expression using the definitions of `cong`, `nat_mod`, and an arithmetic rule to simplify expressions like `(2 + x) - 1`.
* Introduce existential witnesses `0` and `d` of type `num` using `MAP_EVERY EXISTS_TAC`.
* Finally, use `ARITH_TAC` to perform arithmetic simplifications to reach the conclusion.

### Mathematical insight
This theorem provides insight into the properties of modular arithmetic, specifically concerning the behavior of numbers under multiplication and congruence modulo `p`. The statement is significant because it relates the square of `p-1` to `1` modulo `p`, which has implications in number theory and cryptography.

### Dependencies
#### Theorems
* `LE_EXISTS`
* `LEFT_IMP_EXISTS_THM`
* `cong`
#### Definitions
* `nat_mod`
* `ARITH_RULE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles modular arithmetic, existential quantification, and arithmetic simplifications. The `ARITH_TAC` and `SIMP_TAC` tactics have counterparts in other systems, but their application and the specific rules used (like `LE_EXISTS` and `LEFT_IMP_EXISTS_THM`) may need to be adapted. Additionally, the introduction of existential witnesses may be handled differently, requiring adjustments to the proof strategy.

---

## CONG_EXP_MINUS1

### Name of formal statement
CONG_EXP_MINUS1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONG_EXP_MINUS1 = prove
 (`!p n. 2 <= p ==> ((p - 1) EXP n == if EVEN n then 1 else p - 1) (mod p)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH; CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `(p - 1) * (if EVEN n then 1 else p - 1)` THEN
  ASM_SIMP_TAC[CONG_MULT; CONG_REFL; EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; CONG_REFL; CONG_MINUS1_SQUARE])
```

### Informal statement
For all prime numbers `p` greater than or equal to 2 and for all natural numbers `n`, the congruence `((p - 1) EXP n == if n is even then 1 else p - 1) (mod p)` holds.

### Informal sketch
* The proof starts by assuming `2 <= p`, which sets the context for `p` being a prime number greater than or equal to 2.
* It then proceeds by induction on `n`, which suggests that the proof for the statement involves showing a base case and an inductive step.
* The use of `REWRITE_TAC[RIGHT_FORALL_IMP_THM]` and `GEN_TAC` indicates that the proof involves generalizing over `p` and `n` and then applying a rewrite rule to simplify the statement.
* The application of `MATCH_MP_TAC CONG_TRANS` implies that the proof involves using a congruence transitivity property to establish the desired congruence.
* The `EXISTS_TAC` and subsequent simplifications suggest that the proof constructs a specific value to satisfy the congruence relation, leveraging properties of even numbers (`EVEN n`) and modular arithmetic.
* The final steps involve case analysis on whether `n` is even or odd, applying various simplification rules (`ASM_SIMP_TAC`) to reach the conclusion.

### Mathematical insight
This theorem appears to be related to Fermat's Little Theorem, which states that if `p` is a prime number, then for any integer `a` not divisible by `p`, `a` raised to the power of `p-1` is congruent to 1 modulo `p`. The current theorem extends or modifies this idea by considering the case where `a = p - 1` and examining the behavior for even and odd exponents `n`.

### Dependencies
* Theorems:
  - `CONG_TRANS`
  - `CONG_REFL`
  - `CONG_MULT`
  - `CONG_MINUS1_SQUARE`
* Definitions:
  - `EXP`
  - `EVEN`
  - `ARITH`
  - `RIGHT_FORALL_IMP_THM`
  - `MULT_CLAUSES`
  - `CONG_REFL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles modular arithmetic, induction, and congruence relations. Specifically, the use of `MATCH_MP_TAC` and `EXISTS_TAC` might need to be adapted to the target system's tactic language or proof scripting mechanisms. Additionally, the representation of the `if-then-else` construct and the handling of even and odd cases might vary between systems.

---

## NOT_CONG_MINUS1

### Name of formal statement
NOT_CONG_MINUS1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_CONG_MINUS1 = prove
 (`!p. 3 <= p ==> ~(p - 1 == 1) (mod p)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `(2 == 0) (mod p)` MP_TAC THENL
   [MATCH_MP_TAC CONG_ADD_LCANCEL THEN EXISTS_TAC `p - 1` THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `3 <= p ==> (p - 1) + 2 = p + 1`] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `0 + 1` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_ADD THEN
    MESON_TAC[CONG_0; CONG_SYM; DIVIDES_REFL; CONG_REFL];
    REWRITE_TAC[CONG_0] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC])
```

### Informal statement
For all integers `p` such that `3` is less than or equal to `p`, it is not the case that `p - 1` is congruent to `1` modulo `p`.

### Informal sketch
* The proof starts by assuming `3 <= p` and aims to show that `(p - 1) mod p` is not equal to `1 mod p`.
* It uses the `CONG_ADD_LCANCEL` theorem to establish a relationship between `p - 1` and `1` modulo `p`.
* The `CONG_TRANS` theorem is applied to introduce an intermediate value `0 + 1`, facilitating the use of `CONG_ADD` to simplify the congruence.
* The proof also employs `ASM_SIMP_TAC` and `ASM_MESON_TAC` to simplify arithmetic expressions and apply basic properties of congruences, such as `CONG_0`, `CONG_SYM`, and `DIVIDES_REFL`.
* An alternative branch of the proof uses `REWRITE_TAC` with `CONG_0` and applies `DIVIDES_LE` to derive a contradiction.

### Mathematical insight
This theorem is important because it establishes a fundamental property of modular arithmetic, specifically that for any integer `p` greater than or equal to `3`, `p - 1` is not congruent to `1` modulo `p`. This result has implications for various applications in number theory and cryptography.

### Dependencies
* Theorems:
  + `CONG_ADD_LCANCEL`
  + `CONG_TRANS`
  + `CONG_ADD`
  + `CONG_0`
  + `CONG_SYM`
  + `DIVIDES_REFL`
  + `DIVIDES_LE`
* Definitions:
  + `CONG` (congruence modulo `p`)

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of modular arithmetic and congruences. Some systems may require explicit definitions or lemmas for `CONG` and related properties. Additionally, the use of `ASM_SIMP_TAC` and `ASM_MESON_TAC` may need to be replaced with equivalent simplification and proof search mechanisms in the target system.

---

## CONG_COND_LEMMA

### Name of formal statement
CONG_COND_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONG_COND_LEMMA = prove
 (`!p x y. 3 <= p /\
           ((if x then 1 else p - 1) == (if y then 1 else p - 1)) (mod p)
           ==> (x <=> y)`,
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[CONG_SYM; NOT_CONG_MINUS1])
```

### Informal statement
For all natural numbers `p`, `x`, and `y`, if `p` is greater than or equal to 3, and the expression `(if x then 1 else p - 1)` is congruent to `(if y then 1 else p - 1)` modulo `p`, then `x` is equivalent to `y`.

### Informal sketch
* The proof starts by assuming the conditions `3 <= p` and the congruence relation between the two conditional expressions.
* It then proceeds to consider cases based on the truth values of `x` and `y` using `COND_CASES_TAC`.
* In each case, it applies `ASM_REWRITE_TAC` to simplify the expressions and bring them into a form where the congruence can be directly compared.
* The proof concludes by applying `ASM_MESON_TAC` with the theorems `CONG_SYM` and `NOT_CONG_MINUS1` to establish the equivalence between `x` and `y`.

### Mathematical insight
This theorem provides a condition under which two boolean values `x` and `y` can be considered equivalent based on their congruence modulo `p` under specific conditional expressions. The condition `3 <= p` ensures that the modulo operation has a certain "buffer" to work with, allowing the conditional expressions to be meaningfully compared. The theorem is likely important in cryptographic or number-theoretic contexts where such congruences are crucial.

### Dependencies
* Theorems:
  - `CONG_SYM`
  - `NOT_CONG_MINUS1`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how conditional expressions and modulo operations are handled. The use of `COND_CASES_TAC` and `ASM_REWRITE_TAC` suggests that the proof assistant should be able to efficiently handle case analysis and rewriting. Additionally, ensure that the target system has equivalents for `CONG_SYM` and `NOT_CONG_MINUS1`, or can derive them as needed.

---

## FINITE_SUBCROSS

### Name of formal statement
FINITE_SUBCROSS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_SUBCROSS = prove
 (`!s:A->bool t:B->bool.
       FINITE s /\ FINITE t ==> FINITE {x,y | x IN s /\ y IN t /\ P x y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(s:A->bool) CROSS (t:B->bool)` THEN
  ASM_SIMP_TAC[FINITE_CROSS; SUBSET; IN_CROSS; FORALL_PAIR_THM;
               IN_ELIM_PAIR_THM])
```

### Informal statement
For all sets `s` of type `A->bool` and `t` of type `B->bool`, if `s` is finite and `t` is finite, then the set of all pairs `(x, y)` such that `x` is in `s`, `y` is in `t`, and `P x y` holds, is also finite.

### Informal sketch
* The proof starts by assuming `s` and `t` are finite sets.
* It then constructs the Cartesian product `(s:A->bool) CROSS (t:B->bool)`, which is known to be finite due to the `FINITE_CROSS` property.
* The `MATCH_MP_TAC FINITE_SUBSET` tactic is applied to show that any subset of a finite set is finite.
* The subset in question is defined by the predicate `{x,y | x IN s /\ y IN t /\ P x y}`, which selects pairs from the Cartesian product where `P x y` holds.
* The proof then simplifies using `ASM_SIMP_TAC` with various theorems (`FINITE_CROSS`, `SUBSET`, `IN_CROSS`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`) to establish that this subset is indeed finite.

### Mathematical insight
This theorem is important because it establishes a condition under which the set of pairs satisfying a certain property `P` is finite, given that the sets from which the pairs are drawn are finite. This is useful in various mathematical contexts where finiteness needs to be preserved under certain operations or relations.

### Dependencies
* Theorems:
  + `FINITE_SUBSET`
  + `FINITE_CROSS`
  + `SUBSET`
  + `IN_CROSS`
  + `FORALL_PAIR_THM`
  + `IN_ELIM_PAIR_THM`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle finite sets and subsets, as well as how they express the Cartesian product and the predicate `P x y`. The `MATCH_MP_TAC` and `ASM_SIMP_TAC` tactics may have direct counterparts or may require manual unfolding of the proof steps to achieve the same effect. Additionally, the `REPEAT STRIP_TAC` might be handled differently depending on the system's support for automatic proof simplification.

---

## CARD_SUBCROSS_DETERMINATE

### Name of formal statement
CARD_SUBCROSS_DETERMINATE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CARD_SUBCROSS_DETERMINATE = prove
 (`FINITE s /\ FINITE t /\ (!x. x IN s /\ p(x) ==> f(x) IN t)
   ==> CARD {(x:A),(y:B) | x IN s /\ y IN t /\ y = f x /\ p x} =
       CARD {x | x IN s /\ p(x)}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN EXISTS_TAC `\(x:A,y:B). x` THEN
  ASM_SIMP_TAC[FINITE_SUBCROSS; FORALL_PAIR_THM; EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[])
```

### Informal statement
For all finite sets `s` and `t`, and for all predicates `p` and functions `f`, if for every `x` in `s` such that `p(x)` holds, `f(x)` is in `t`, then the cardinality of the set of pairs `(x, y)` where `x` is in `s`, `y` is in `t`, `y` equals `f(x)`, and `p(x)` holds, is equal to the cardinality of the set of `x` in `s` such that `p(x)` holds.

### Informal sketch
* The proof starts by assuming the premises: `s` and `t` are finite, and for all `x` in `s`, if `p(x)` then `f(x)` is in `t`.
* It then applies the `CARD_IMAGE_INJ_EQ` theorem, which states that the cardinality of the image of a set under an injective function is equal to the cardinality of the original set.
* The `EXISTS_TAC` tactic is used to introduce a witness, in this case, the function `\x. x`, which is used to establish the injectivity of the function `f`.
* The proof then simplifies the expression using various theorems, including `FINITE_SUBCROSS`, `FORALL_PAIR_THM`, `EXISTS_UNIQUE_THM`, `EXISTS_PAIR_THM`, `IN_ELIM_PAIR_THM`, `IN_ELIM_THM`, and `PAIR_EQ`.
* The final step uses `ASM_MESON_TAC` to combine the assumptions and derive the conclusion.

### Mathematical insight
This theorem provides a way to reason about the cardinality of sets defined using predicates and functions. It allows us to conclude that the size of the set of pairs satisfying certain conditions is equal to the size of the set of elements satisfying a related condition. This is useful in a variety of mathematical contexts, such as combinatorics and category theory.

### Dependencies
* Theorems:
  + `CARD_IMAGE_INJ_EQ`
  + `FINITE_SUBCROSS`
  + `FORALL_PAIR_THM`
  + `EXISTS_UNIQUE_THM`
  + `EXISTS_PAIR_THM`
  + `IN_ELIM_PAIR_THM`
  + `IN_ELIM_THM`
  + `PAIR_EQ`
* Definitions:
  + `FINITE`
  + `CARD`
  + `IN`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `CARD` function is defined and behaves similarly. Additionally, the `FINITE` predicate and the `IN` relation may need to be defined or imported from a library. The `EXISTS_TAC` and `ASM_MESON_TAC` tactics may not have direct equivalents in other proof assistants, so alternative tactics or strategies may need to be used to achieve the same result.

---

## CARD_SUBCROSS_SWAP

### Name of formal statement
CARD_SUBCROSS_SWAP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CARD_SUBCROSS_SWAP = prove
 (`CARD {y,x | y IN 1..m /\ x IN 1..n /\ P x y} =
   CARD {x,y | x IN 1..n /\ y IN 1..m /\ P x y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `\(x:num,y:num). (y,x)` THEN
  ASM_SIMP_TAC[FINITE_SUBCROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  SIMP_TAC[IN_ELIM_PAIR_THM; PAIR_EQ] THEN MESON_TAC[])
```

### Informal statement
The cardinality of the set of pairs `(y, x)` where `y` is in the range `1` to `m` and `x` is in the range `1` to `n` and `P(x, y)` holds, is equal to the cardinality of the set of pairs `(x, y)` where `x` is in the range `1` to `n` and `y` is in the range `1` to `m` and `P(x, y)` holds.

### Informal sketch
* The proof starts by applying `STRIP_TAC` to remove any universal quantifiers and implications, preparing the goal for further manipulation.
* It then applies `MATCH_MP_TAC` with `CARD_IMAGE_INJ_EQ` to relate the cardinalities of the two sets, assuming an injective mapping between them.
* The existence of such a mapping is demonstrated using `EXISTS_TAC` with the function `\((x:num,y:num). (y,x)``, essentially swapping the components of the pairs.
* The proof continues by applying `ASM_SIMP_TAC` with `FINITE_SUBCROSS` and `FINITE_NUMSEG` to establish the finiteness of the sets involved, which is crucial for comparing their cardinalities.
* Further simplifications are made using `REWRITE_TAC` with several theorems (`EXISTS_UNIQUE_THM`, `FORALL_PAIR_THM`, `EXISTS_PAIR_THM`) to handle the existential and universal quantifiers in the context of pairs.
* The `SIMP_TAC` step with `IN_ELIM_PAIR_THM` and `PAIR_EQ` simplifies the expressions involving pairs and their membership.
* Finally, `MESON_TAC` is applied to derive the conclusion from the simplified expressions.

### Mathematical insight
This theorem essentially states that the cardinality of a set of pairs does not change when the order of the components in the pairs is swapped, given that the relation `P` defining the set is appropriately respected. This is intuitive because swapping the components of pairs does not change the number of pairs, assuming the relation `P` is symmetric or its asymmetry is accounted for in the swapping process.

### Dependencies
* Theorems:
  - `CARD_IMAGE_INJ_EQ`
  - `EXISTS_UNIQUE_THM`
  - `FORALL_PAIR_THM`
  - `EXISTS_PAIR_THM`
  - `IN_ELIM_PAIR_THM`
  - `PAIR_EQ`
* Definitions:
  - `FINITE_SUBCROSS`
  - `FINITE_NUMSEG`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how pairs and their components are handled, as well as how cardinalities of finite sets are compared. The symmetry or asymmetry of the relation `P` and how it interacts with the swapping of pair components should also be carefully considered. Additionally, the equivalents of `STRIP_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, `ASM_SIMP_TAC`, `REWRITE_TAC`, `SIMP_TAC`, and `MESON_TAC` in the target proof assistant should be identified and applied appropriately to mirror the strategic flow of the original proof.

---

## IS_QUADRATIC_RESIDUE

### Name of formal statement
IS_QUADRATIC_RESIDUE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE = prove
 (`!a p. ~(p = 0) /\ ~(p divides a)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_quadratic_residue; EXP_2] THEN
  DISCH_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `x MOD p` THEN
  ASM_SIMP_TAC[DIVISION] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LT_NZ; GSYM DIVIDES_MOD; CONG_DIVIDES; DIVIDES_LMUL];
    UNDISCH_TAC `(x * x == a) (mod p)` THEN
    ASM_SIMP_TAC[CONG; MOD_MULT_MOD2]])
```

### Informal statement
For all integers `a` and prime numbers `p`, if `p` is not equal to 0 and `p` does not divide `a`, then `a` is a quadratic residue modulo `p` if and only if there exists an integer `x` such that `0 < x < p` and `x` squared is congruent to `a` modulo `p`.

### Informal sketch
* The proof starts by assuming the conditions `~(p = 0)` and `~(p divides a)`.
* It then applies `GEN_TAC` to generalize the statement for all `a` and `p`.
* The `REWRITE_TAC` tactic is used with `is_quadratic_residue` and `EXP_2` to rewrite the `is_quadratic_residue` relation.
* The proof proceeds by cases using `EQ_TAC`, considering both directions of the equivalence.
* In one direction, `DISCH_THEN` and `X_CHOOSE_TAC` are used to select an `x` such that `x` squared is congruent to `a` modulo `p`.
* The existence of such an `x` is then shown to satisfy the conditions `0 < x < p`.
* In the other direction, `UNDISCH_TAC` and `ASM_SIMP_TAC` are used to derive the congruence relation.
* Key steps involve using `ASM_MESON_TAC` to apply various properties, including `LT_NZ`, `GSYM DIVIDES_MOD`, `CONG_DIVIDES`, and `DIVIDES_LMUL`.

### Mathematical insight
This theorem provides a characterization of quadratic residues modulo a prime `p`. A quadratic residue is an integer `a` such that there exists an `x` whose square is congruent to `a` modulo `p`. The theorem shows that this is equivalent to the existence of an `x` in the range `0 < x < p` whose square is congruent to `a` modulo `p`. This is an important concept in number theory, with applications in cryptography and other areas.

### Dependencies
* `is_quadratic_residue`
* `EXP_2`
* `DIVISION`
* `CONG`
* `MOD_MULT_MOD2`
* `LT_NZ`
* `GSYM DIVIDES_MOD`
* `CONG_DIVIDES`
* `DIVIDES_LMUL`

### Porting notes
When porting this theorem to other proof assistants, care should be taken to ensure that the `is_quadratic_residue` relation is defined and used consistently. Additionally, the use of `MOD` and `EXP` may need to be adapted to the target system's notation and libraries. The `GEN_TAC` and `DISCH_TAC` tactics may also need to be replaced with equivalent constructs in the target system.

---

## IS_QUADRATIC_RESIDUE_COMMON

### Name of formal statement
IS_QUADRATIC_RESIDUE_COMMON

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE_COMMON = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IS_QUADRATIC_RESIDUE THEN
  ASM_MESON_TAC[COPRIME_PRIME; DIVIDES_REFL; PRIME_0])
```

### Informal statement
For all integers `a` and prime numbers `p`, if `a` and `p` are coprime, then `a` is a quadratic residue modulo `p` if and only if there exists an integer `x` such that `0 < x < p` and `x` squared is congruent to `a` modulo `p`.

### Informal sketch
* The proof starts by assuming `a` and `p` are coprime and `p` is prime.
* It then applies the `IS_QUADRATIC_RESIDUE` theorem to establish the relationship between `a` being a quadratic residue modulo `p` and the existence of `x` such that `x` squared is congruent to `a` modulo `p`.
* The `MATCH_MP_TAC` tactic is used to apply the `IS_QUADRATIC_RESIDUE` theorem, which likely involves a modus ponens step to instantiate the theorem with the given assumptions.
* The `ASM_MESON_TAC` tactic is then used with a list of theorems (`COPRIME_PRIME`, `DIVIDES_REFL`, `PRIME_0`) to automate the proof of the resulting goal, likely involving basic properties of coprime numbers, divisibility, and prime numbers.

### Mathematical insight
This theorem provides a fundamental characterization of quadratic residues in modular arithmetic, which is crucial in number theory. It essentially states that an integer `a` is a quadratic residue modulo a prime `p` if and only if there exists an integer `x` whose square gives `a` when taken modulo `p`, under the condition that `a` and `p` are coprime. This condition ensures that `a` has a multiplicative inverse modulo `p`, which is essential for the quadratic residue concept to be meaningful.

### Dependencies
* Theorems:
  + `IS_QUADRATIC_RESIDUE`
  + `COPRIME_PRIME`
  + `DIVIDES_REFL`
  + `PRIME_0`
* Definitions:
  + `is_quadratic_residue`
  + `coprime`
  + `prime`

### Porting notes
When porting this theorem to another proof assistant, pay special attention to how quadratic residues and coprime numbers are defined and handled. The `IS_QUADRATIC_RESIDUE` theorem and its dependencies will need to be translated or proven in the target system. Additionally, the automation provided by `ASM_MESON_TAC` may need to be replicated using the target system's proof automation mechanisms, which could involve different tactics or strategies.

---

## QUADRATIC_RESIDUE_PAIR_ADD

### Name of formal statement
QUADRATIC_RESIDUE_PAIR_ADD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR_ADD = prove
 (`!p x y. prime p
           ==> (((x + y) EXP 2 == x EXP 2) (mod p) <=>
                 p divides y \/ p divides (2 * x + y))`,
  REWRITE_TAC[NUM_RING `(x + y) EXP 2 = y * (y + 2 * x) + x EXP 2`] THEN
  SIMP_TAC[CONG_ADD_RCANCEL_EQ_0; CONG_0; PRIME_DIVPROD_EQ; ADD_SYM])
```

### Informal statement
For all prime numbers `p` and for all numbers `x` and `y`, the following holds: `(x + y)` squared is congruent to `x` squared modulo `p` if and only if `p` divides `y` or `p` divides `2 * x + y`.

### Informal sketch
* The proof starts by assuming a prime number `p` and arbitrary numbers `x` and `y`.
* It then expands the expression `(x + y)` squared using the `NUM_RING` theorem, which yields `y * (y + 2 * x) + x` squared.
* The next step involves simplifying the congruence relation using `SIMP_TAC` with several theorems: `CONG_ADD_RCANCEL_EQ_0`, `CONG_0`, `PRIME_DIVPROD_EQ`, and `ADD_SYM`.
* These simplifications lead to the conclusion that the original congruence holds if and only if `p` divides `y` or `p` divides `2 * x + y`.

### Mathematical insight
This theorem provides insight into the properties of quadratic residues modulo a prime number, which is a fundamental concept in number theory. It shows how the sum of two numbers affects their squares modulo a prime, which has implications for various number theoretic constructions and proofs.

### Dependencies
* `prime`
* `NUM_RING`
* `CONG_ADD_RCANCEL_EQ_0`
* `CONG_0`
* `PRIME_DIVPROD_EQ`
* `ADD_SYM`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how the `REWRITE_TAC` and `SIMP_TAC` tactics are handled, as different systems may have different mechanisms for rewriting and simplifying expressions. Additionally, the `NUM_RING` theorem and other dependencies may need to be ported or re-proven in the target system.

---

## QUADRATIC_RESIDUE_PAIR

### Name of formal statement
QUADRATIC_RESIDUE_PAIR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR = prove
 (`!p x y. prime p
           ==> ((x EXP 2 == y EXP 2) (mod p) <=>
                 p divides (x + y) \/ p divides (dist(x,y)))`,
  GEN_TAC THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[DIST_SYM; CONG_SYM; ADD_SYM]; ALL_TAC] THEN
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN ASM_SIMP_TAC[QUADRATIC_RESIDUE_PAIR_ADD] THEN
  REWRITE_TAC[DIST_RADD_0; ARITH_RULE `x + x + d = 2 * x + d`; DISJ_ACI])
```

### Informal statement
For all prime numbers $p$ and for all $x$ and $y$, $x^2$ is congruent to $y^2$ modulo $p$ if and only if $p$ divides $x + y$ or $p$ divides the distance between $x$ and $y$.

### Informal sketch
* The proof starts by assuming $p$ is a prime number and $x$ and $y$ are arbitrary.
* It then applies `WLOG_LE` to reduce the problem, followed by a case split using `CONJ_TAC`.
* One branch is solved using `MESON_TAC` with `DIST_SYM`, `CONG_SYM`, and `ADD_SYM`.
* The other branch involves rewriting using `LE_EXISTS`, stripping and rewriting with `ASM_REWRITE_TAC`, and simplifying with `ASM_SIMP_TAC` using `QUADRATIC_RESIDUE_PAIR_ADD`.
* Further rewriting is done with `DIST_RADD_0` and an arithmetic rule, and the proof concludes with `DISJ_ACI`.

### Mathematical insight
This theorem provides insight into the properties of quadratic residues modulo a prime number, relating the congruence of squares to divisibility conditions. It's a fundamental result in number theory, connecting algebraic properties of numbers to their arithmetic properties.

### Dependencies
* Theorems:
  + `WLOG_LE`
  + `DIST_SYM`
  + `CONG_SYM`
  + `ADD_SYM`
  + `QUADRATIC_RESIDUE_PAIR_ADD`
  + `DIST_RADD_0`
* Definitions:
  + `prime`
  + `EXP`
  + `mod`
  + `divides`
  + `dist`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of modular arithmetic, prime numbers, and the specific tactics used (e.g., `GEN_TAC`, `MATCH_MP_TAC`, `CONJ_TAC`). The `WLOG_LE` tactic and the use of `MESON_TAC` for solving one of the branches might require special attention due to differences in how various proof assistants handle case splits and automated reasoning.

---

## IS_QUADRATIC_RESIDUE_PAIR

### Name of formal statement
IS_QUADRATIC_RESIDUE_PAIR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE_PAIR = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x y. 0 < x /\ x < p /\ 0 < y /\ y < p /\ x + y = p /\
                       (x EXP 2 == a) (mod p) /\ (y EXP 2 == a) (mod p) /\
                       !z. 0 < z /\ z < p /\ (z EXP 2 == a) (mod p)
                           ==> z = x \/ z = y)`,
  SIMP_TAC[IS_QUADRATIC_RESIDUE_COMMON] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `p - x:num`] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `0 < x /\ x < p ==> 0 < p - x /\ p - x < p /\ x + (p - x) = p`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP QUADRATIC_RESIDUE_PAIR) THENL
   [DISCH_THEN(MP_TAC o SPECL [`x:num`; `p - x:num`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `x < p ==> x + (p - x) = p`; DIVIDES_REFL] THEN
    ASM_MESON_TAC[CONG_TRANS; CONG_SYM];
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `z:num`]) THEN
    SUBGOAL_THEN `(x EXP 2 == z EXP 2) (mod p)` (fun th -> SIMP_TAC[th]) THENL
     [ASM_MESON_TAC[CONG_TRANS; CONG_SYM]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP DIVIDES_CASES)) THEN
    REWRITE_TAC[ADD_EQ_0; DIST_EQ_0] THEN REWRITE_TAC[dist] THEN
    ASM_ARITH_TAC])
```

### Informal statement
For all `a` and prime `p` such that `a` and `p` are coprime, `a` is a quadratic residue modulo `p` if and only if there exist `x` and `y` such that `0 < x < p`, `0 < y < p`, `x + y = p`, `x` squared is congruent to `a` modulo `p`, `y` squared is congruent to `a` modulo `p`, and for all `z` such that `0 < z < p` and `z` squared is congruent to `a` modulo `p`, `z` is equal to `x` or `z` is equal to `y`.

### Informal sketch
* The proof starts by assuming `a` and `p` are coprime and `p` is prime.
* It then proceeds to prove the equivalence between `a` being a quadratic residue modulo `p` and the existence of `x` and `y` satisfying certain conditions.
* The forward direction involves using the `QUADRATIC_RESIDUE_PAIR` theorem to find suitable `x` and `y`.
* The reverse direction assumes the existence of `x` and `y` and uses properties of modular arithmetic and the `IS_QUADRATIC_RESIDUE_COMMON` definition to show `a` is a quadratic residue modulo `p`.
* Key steps involve using `SIMP_TAC`, `REPEAT STRIP_TAC`, and `EQ_TAC` to simplify and rearrange the assumptions and conclusions.
* The proof also uses `DISCH_THEN` and `MAP_EVERY EXISTS_TAC` to handle the existential quantifiers and introduce witnesses `x` and `y`.
* The `CONG_TRANS` and `CONG_SYM` theorems are used to reason about congruences.

### Mathematical insight
This theorem provides a characterization of quadratic residues modulo a prime `p`, which is crucial in number theory. It shows that `a` is a quadratic residue modulo `p` if and only if there are `x` and `y` less than `p` whose squares are both congruent to `a` modulo `p` and whose sum is `p`. This insight is important for understanding the distribution of quadratic residues and non-residues, which has implications for various number theoretic applications.

### Dependencies
* Theorems:
  + `QUADRATIC_RESIDUE_PAIR`
  + `IS_QUADRATIC_RESIDUE_COMMON`
  + `CONG_TRANS`
  + `CONG_SYM`
  + `DIVIDES_CASES`
* Definitions:
  + `is_quadratic_residue`
  + `coprime`
  + `prime`

---

## QUADRATIC_RESIDUE_PAIR_PRODUCT

### Name of formal statement
QUADRATIC_RESIDUE_PAIR_PRODUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR_PRODUCT = prove
 (`!p x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p)
         ==> (x * (p - x) == (p - 1) * a) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MP (ARITH_RULE `x < p ==> 1 <= p`)) THEN
  SUBGOAL_THEN `(x * (p - x) + x EXP 2 == a * (p - 1) + a * 1) (mod p)`
  MP_TAC THENL
   [ASM_SIMP_TAC[LEFT_SUB_DISTRIB; EXP_2; SUB_ADD;
                 LE_MULT_LCANCEL; LT_IMP_LE] THEN
    REWRITE_TAC[cong; nat_mod] THEN ASM_MESON_TAC[ADD_SYM; MULT_SYM];
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_MESON_TAC[CONG_ADD; CONG_TRANS; CONG_SYM; CONG_REFL; MULT_SYM;
                  CONG_ADD_RCANCEL]])
```

### Informal statement
For all primes $p$ and integers $x$, if $0 < x < p$ and $x^2 \equiv a \pmod{p}$, then $x(p-x) \equiv (p-1)a \pmod{p}$.

### Informal sketch
* The proof starts by assuming $0 < x < p$ and $x^2 \equiv a \pmod{p}$.
* It uses the `ARITH_RULE` to establish $1 \leq p$ from $x < p$.
* The proof then aims to show $x(p-x) + x^2 \equiv a(p-1) + a \pmod{p}$ by using `SUBGOAL_THEN`.
* Two main paths are explored:
  + The first involves simplification using `ASM_SIMP_TAC` with various theorems like `LEFT_SUB_DISTRIB`, `EXP_2`, and `SUB_ADD`, followed by applying `REWRITE_TAC` for `cong` and `nat_mod`, and concluding with `ASM_MESON_TAC` for combining the results with `ADD_SYM` and `MULT_SYM`.
  + The second path involves rewriting using `REWRITE_TAC` with `MULT_CLAUSES`, and then applying `ASM_MESON_TAC` with several congruence properties (`CONG_ADD`, `CONG_TRANS`, `CONG_SYM`, `CONG_REFL`, `MULT_SYM`, and `CONG_ADD_RCANCEL`).
* The overall strategy involves manipulating the initial equation to match the target form through a series of logical and algebraic steps.

### Mathematical insight
This theorem relates to quadratic residues and their properties modulo a prime $p$. It shows a relationship between a quadratic residue $a$ (such that $x^2 \equiv a \pmod{p}$ for some $x$) and the product of $x$ and its "complementary" value $p-x$. The insight here involves understanding how quadratic residues behave under multiplication and how their properties can be derived from basic modular arithmetic principles.

### Dependencies
* `ARITH_RULE`
* `LEFT_SUB_DISTRIB`
* `EXP_2`
* `SUB_ADD`
* `LE_MULT_LCANCEL`
* `LT_IMP_LE`
* `cong`
* `nat_mod`
* `ADD_SYM`
* `MULT_SYM`
* `MULT_CLAUSES`
* `CONG_ADD`
* `CONG_TRANS`
* `CONG_SYM`
* `CONG_REFL`
* `CONG_ADD_RCANCEL`

---

## legendre

### Name of formal statement
legendre

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let legendre = new_definition
 `(legendre:num#num->int)(a,p) =
        if ~(coprime(a,p)) then &0
        else if a is_quadratic_residue (mod p) then &1
        else --(&1)`
```

### Informal statement
The Legendre symbol is a function `legendre` that takes two arguments `a` and `p` of type `num` and returns an integer. It is defined as follows: if `a` and `p` are not coprime, then the Legendre symbol is 0. Otherwise, if `a` is a quadratic residue modulo `p`, then the Legendre symbol is 1; otherwise, it is -1.

### Informal sketch
* The definition first checks if `a` and `p` are coprime using the `coprime` predicate. If they are not, the function returns 0.
* If `a` and `p` are coprime, the definition then checks if `a` is a quadratic residue modulo `p` using the `is_quadratic_residue` predicate. If it is, the function returns 1.
* If `a` is not a quadratic residue modulo `p`, the function returns -1, which is computed as the negation of 1, denoted by `--(&1)`.

### Mathematical insight
The Legendre symbol is a fundamental concept in number theory, used to determine whether a number `a` is a quadratic residue modulo `p`, where `p` is a prime number. This definition captures the essence of the Legendre symbol, which is used to study the properties of quadratic residues and non-residues in modular arithmetic.

### Dependencies
* `coprime`
* `is_quadratic_residue`
* `num`

### Porting notes
When porting this definition to another proof assistant, note that the `coprime` and `is_quadratic_residue` predicates may need to be defined or imported separately. Additionally, the `--` operator may be represented differently in other systems, so care should be taken to ensure that the negation is correctly implemented.

---

## nproduct

### Name of formal statement
nproduct

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let nproduct = new_definition `nproduct = iterate ( * )`
```

### Informal statement
The `nproduct` is defined as the iteration of the multiplication operation.

### Informal sketch
* The definition relies on the `iterate` function, which applies a given operation (in this case, multiplication `*`) in a cumulative way to the elements of a sequence.
* The `iterate` function is used to generalize the concept of multiplication to sequences of numbers, allowing for the computation of the product of all elements in a sequence.

### Mathematical insight
The `nproduct` definition provides a concise way to express the product of a sequence of numbers, which is a fundamental operation in mathematics. This definition is important because it enables the generalization of arithmetic operations to sequences, facilitating the development of more complex mathematical structures and theorems.

### Dependencies
* `iterate`
* `*` 

### Porting notes
When porting this definition to other proof assistants, note that the equivalent of `iterate` may have different names or require additional setup. For example, in Lean, the `foldl` function can be used to achieve similar results, while in Coq, the `fold_left` function from the `List` module can be used. Additionally, the handling of sequences and multiplication operations may vary between systems, requiring adjustments to the definition.

---

## CONG_NPRODUCT

### Name of formal statement
CONG_NPRODUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONG_NPRODUCT = prove
 (`!f g s. FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
           ==> (nproduct s f == nproduct s g) (mod n)`,
  REWRITE_TAC[nproduct] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_RELATED MONOIDAL_MUL) THEN
  SIMP_TAC[CONG_REFL; CONG_MULT])
```

### Informal statement
For all functions `f` and `g` and for all sets `s`, if `s` is finite and for all `x` in `s`, `f(x)` is congruent to `g(x)` modulo `n`, then the product of `f` over `s` is congruent to the product of `g` over `s` modulo `n`.

### Informal sketch
* The proof starts by applying the `REWRITE_TAC` tactic to expand the definition of `nproduct`.
* It then applies `MATCH_MP_TAC` with `MATCH_MP ITERATE_RELATED MONOIDAL_MUL` to establish a relationship between the products of `f` and `g` over `s`, leveraging properties of monoidal multiplication.
* The `SIMP_TAC` tactic is used with `CONG_REFL` and `CONG_MULT` to simplify the resulting expression, exploiting congruence properties.

### Mathematical insight
This theorem is important because it allows us to reason about the product of functions over a set modulo `n`, which is crucial in number theory and algebra. The theorem essentially states that if two functions are congruent pointwise modulo `n` over a finite set, then their products over that set are also congruent modulo `n`. This provides a powerful tool for simplifying expressions involving products in modular arithmetic.

### Dependencies
* `nproduct`
* `FINITE`
* `CONG_REFL`
* `CONG_MULT`
* `ITERATE_RELATED`
* `MONOIDAL_MUL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles modular arithmetic, finite sets, and function products. The `REWRITE_TAC`, `MATCH_MP_TAC`, and `SIMP_TAC` tactics have counterparts in these systems, but the exact syntax and tactical structure may differ. Additionally, the treatment of congruence and monoidal properties might require adjustments based on the target system's libraries and built-in support for these concepts.

---

## NPRODUCT_DELTA_CONST

### Name of formal statement
NPRODUCT_DELTA_CONST

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NPRODUCT_DELTA_CONST = prove
 (`!c s. FINITE s
         ==> nproduct s (\x. if p(x) then c else 1) =
             c EXP (CARD {x | x IN s /\ p(x)})`,
  let lemma1 = prove
   (`{x | x IN a INSERT s /\ p(x)} =
     if p(a) then a INSERT {x | x IN s /\ p(x)}
     else {x | x IN s /\ p(x)}`,
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[])
  and lemma2 = prove
   (`FINITE s ==> FINITE {x | x IN s /\ p(x)}`,
    MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                FINITE_SUBSET) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; CARD_CLAUSES; EXP; NOT_IN_EMPTY;
           SET_RULE `{x | F} = {}`; lemma1] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; lemma2; EXP; MULT_CLAUSES])
```

### Informal statement
For all constants `c` and sets `s`, if `s` is finite, then the natural product over `s` of the function that maps each `x` to `c` if `p(x)` holds and to 1 otherwise, is equal to `c` raised to the power of the cardinality of the set of all `x` in `s` for which `p(x)` holds.

### Informal sketch
* The proof starts by applying `FINITE_INDUCT_STRONG` to establish the base case and the inductive step for the finiteness of `s`.
* It then uses `COND_CASES_TAC` to consider two cases based on whether `p(a)` holds for an element `a` in `s`.
* The `lemma1` is used to simplify the set comprehension involving `p(x)` and `a INSERT s`.
* `lemma2` is applied to establish the finiteness of the subset of `s` where `p(x)` holds.
* The proof then simplifies the natural product using `NPRODUCT_CLAUSES`, `CARD_CLAUSES`, `EXP`, and `MULT_CLAUSES`, leveraging the properties of exponentiation and cardinality.
* The `ASM_SIMP_TAC` and `REPEAT STRIP_TAC` are used to simplify and rearrange the terms to reach the final conclusion.

### Mathematical insight
This theorem provides a way to simplify the natural product over a finite set `s` when the terms of the product depend on a predicate `p(x)`. It shows that the product can be expressed as an exponential function of the cardinality of the subset of `s` where `p(x)` holds, which can be useful in various combinatorial and algebraic contexts.

### Dependencies
#### Theorems
* `FINITE_INDUCT_STRONG`
* `FINITE_SUBSET`
* `NPRODUCT_CLAUSES`
* `CARD_CLAUSES`
* `EXP`
* `MULT_CLAUSES`
#### Definitions
* `nproduct`
* `CARD`
* `EXP`
#### Lemmas
* `lemma1`
* `lemma2`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of finite sets, natural products, and the interaction between the `p(x)` predicate and the set comprehensions. The use of `COND_CASES_TAC` and `ASM_SIMP_TAC` may need to be adapted to the target system's tactics and simplification mechanisms. Additionally, the representation of finite sets and the `nproduct` function may vary between systems, requiring careful mapping to ensure the ported theorem is equivalent to the original.

---

## COPRIME_NPRODUCT

### Name of formal statement
COPRIME_NPRODUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COPRIME_NPRODUCT = prove
 (`!f p s. FINITE s /\ (!x. x IN s ==> coprime(p,f x))
           ==> coprime(p,nproduct s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; COPRIME_1; IN_INSERT; COPRIME_MUL])
```

### Informal statement
For all functions `f`, all numbers `p`, and all sets `s`, if `s` is finite and for all `x` in `s`, `p` is coprime to `f(x)`, then `p` is coprime to the product of `f(x)` for all `x` in `s`.

### Informal sketch
* The proof starts by assuming `s` is finite and that for every `x` in `s`, `p` and `f(x)` are coprime.
* It then applies `FINITE_INDUCT_STRONG` to induct over the elements of `s`, considering the base case where `s` is empty and the step case where an element is added to `s`.
* The `NPRODUCT_CLAUSES` are used to simplify the product of `f(x)` over `s`, and `COPRIME_1` and `COPRIME_MUL` are applied to maintain the coprimality condition through the induction.
* The `IN_INSERT` property is used to handle the insertion of elements into `s` during the inductive step.

### Mathematical insight
This theorem is important because it shows that if a number `p` is coprime to each element in a finite set `s` under a function `f`, then `p` is also coprime to the product of the images of all elements in `s` under `f`. This property has implications in number theory and algebra, particularly in contexts where coprimality and products of sets are crucial, such as in proving properties of Diophantine equations or in cryptographic applications.

### Dependencies
* Theorems:
  - `FINITE_INDUCT_STRONG`
  - `COPRIME_1`
  - `COPRIME_MUL`
* Definitions:
  - `NPRODUCT_CLAUSES`
  - `IN_INSERT`
* Inductive rules:
  - `FINITE_INDUCT_STRONG`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how coprimality and the product over a set are defined and handled. The use of `FINITE_INDUCT_STRONG` might need to be adapted based on the induction principles available in the target system. Additionally, the automation provided by `SIMP_TAC` and `MATCH_MP_TAC` might need to be manually replicated or adjusted according to the capabilities of the target proof assistant.

---

## FACT_NPRODUCT

### Name of formal statement
FACT_NPRODUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FACT_NPRODUCT = prove
 (`!n. FACT(n) = nproduct(1..n) (\i. i)`,
  INDUCT_TAC THEN
  REWRITE_TAC[FACT; NUMSEG_CLAUSES; ARITH; NPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; NPRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers n, the factorial of n is equal to the product of all numbers from 1 to n.

### Informal sketch
* The proof proceeds by induction on n.
* The base case is implicitly covered by the `INDUCT_TAC`.
* The inductive step involves rewriting the `FACT` and `nproduct` expressions using various definitions and clauses (`FACT`, `NUMSEG_CLAUSES`, `ARITH`, `NPRODUCT_CLAUSES`).
* Simplification and arithmetic manipulations are performed using `ASM_SIMP_TAC` and `ARITH_TAC`, leveraging properties such as `ARITH_RULE` and `FINITE_NUMSEG`.
* The `REWRITE_TAC` steps apply these rewrites to transform the goal into a form that can be directly proven by arithmetic.

### Mathematical insight
This theorem provides an alternative characterization of the factorial function in terms of a product of consecutive integers, which can be useful in various mathematical contexts, such as combinatorics and number theory. The factorial function is a fundamental concept in mathematics, and this representation can offer new insights or simplify certain proofs.

### Dependencies
#### Theorems and definitions
* `FACT`
* `nproduct`
* `NUMSEG_CLAUSES`
* `ARITH`
* `NPRODUCT_CLAUSES`
* `FINITE_NUMSEG`
* `IN_NUMSEG`

### Porting notes
When translating this theorem into another proof assistant, pay attention to the handling of induction, arithmetic, and product notation. The `INDUCT_TAC` and `REWRITE_TAC` may need to be replaced with equivalent tactics in the target system. Additionally, the `ARITH` and `NPRODUCT_CLAUSES` may require special care, as they involve arithmetic reasoning and product definitions that might be represented differently in other systems.

---

## NPRODUCT_PAIRUP_INDUCT

### Name of formal statement
NPRODUCT_PAIRUP_INDUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP_INDUCT = prove
 (`!f r n s k. s HAS_SIZE (2 * n) /\
               (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                      (f(x) * f(y) == k) (mod r))
               ==> (nproduct s f == k EXP n) (mod r)`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; HAS_SIZE_0; NPRODUCT_CLAUSES; EXP; CONG_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_MESON_TAC[HAS_SIZE_0; ARITH_RULE `2 * n = 0 <=> n = 0`; HAS_SIZE];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 < n`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `(a:A) IN s`] THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`(s DELETE a) DELETE (b:A)`; `k:num`]) THEN
  SUBGOAL_THEN `s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))`
   (ASSUME_TAC o SYM) THENL [ASM SET_TAC[]; ALL_TAC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(s:A->bool) HAS_SIZE 2 * n` THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
        [SYM th]) THEN
      SIMP_TAC[HAS_SIZE; FINITE_INSERT; CARD_CLAUSES; FINITE_DELETE;
               IMP_CONJ; IN_DELETE; IN_INSERT] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(b:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:A`; `x:A`] o CONJUNCT2) THEN
    ASM_MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  DISCH_TAC THEN EXPAND_TAC "s" THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[HAS_SIZE]) THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_DELETE] THEN
  REWRITE_TAC[IN_INSERT; IN_DELETE; MULT_CLAUSES] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP
   (ARITH_RULE `~(n = 0) ==> n = SUC(n - 1)`)) THEN
  ASM_REWRITE_TAC[MULT_ASSOC; EXP] THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all functions `f`, numbers `r`, `n`, sets `s`, and numbers `k`, if `s` has a size of `2 * n` and for every `x` in `s`, there exists a unique `y` in `s` such that `y` is not equal to `x` and the product of `f(x)` and `f(y)` is congruent to `k` modulo `r`, then the product of `f` over `s` is congruent to `k` raised to the power of `n` modulo `r`.

### Informal sketch
* The proof starts by considering the base case where `n = 0`, in which case the statement holds trivially.
* It then considers the case where `s` is empty, which also leads to a trivial conclusion.
* For non-empty `s` and `n > 0`, it selects an arbitrary element `a` from `s` and finds a unique `b` in `s` such that `f(a) * f(b)` is congruent to `k` modulo `r`.
* The proof then proceeds by induction on `n`, considering the set `s` with `a` and `b` removed, and uses the induction hypothesis to establish the result for `s`.
* Key steps involve using `MATCH_MP_TAC num_WF` for the induction, `ASM_CASES_TAC` for considering different cases, and `CONJ_TAC` for combining conclusions.
* The use of `EXISTS_UNIQUE` and `MONO_EXISTS` is crucial for handling the unique existence of `y` for each `x` in `s`.

### Mathematical insight
This theorem provides a way to reduce the computation of a product over a set `s` to a simpler form when the set can be paired up in a specific manner. The condition that for every `x` in `s`, there exists a unique `y` in `s` such that `f(x) * f(y)` is congruent to `k` modulo `r`, allows for a significant simplification of the product computation, turning it into a power of `k`. This is particularly useful in number theoretic contexts where such pairings can often be identified.

### Dependencies
* `num_WF`
* `MULT_CLAUSES`
* `HAS_SIZE_0`
* `NPRODUCT_CLAUSES`
* `EXP`
* `CONG_REFL`
* `ARITH_RULE`
* `MULT_ASSOC`
* `CONG_MULT`
* `EXISTS_UNIQUE`
* `MONO_EXISTS`
* `EXISTS_UNIQUE_THM`
* `MULT_SYM`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of the `EXISTS_UNIQUE` and `MONO_EXISTS` constructs, as well as the use of `MATCH_MP_TAC` and `CONJ_TAC`, which may have different equivalents in the target system. Additionally, the arithmetic rules and properties of congruence modulo `r` should be carefully translated to ensure that the proof steps are valid in the new context.

---

## QUADRATIC_NONRESIDUE_FACT

### Name of formal statement
QUADRATIC_NONRESIDUE_FACT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let QUADRATIC_NONRESIDUE_FACT = prove
 (`!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ ~(a is_quadratic_residue (mod p))
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 1)) (mod p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_NPRODUCT] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o
      GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    SIMP_TAC[SUC_SUB1; DIV_MULT; ARITH] THEN
    REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG; CARD_NUMSEG; ADD_SUB];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; ARITH_RULE `1 <= x <=> 0 < x`;
               ARITH_RULE `~(p = 0) ==> (x <= p - 1 <=> x < p)`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `p:num`; `x:num`] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[is_quadratic_residue; EXP_2])
```

### Informal statement
For all `a` and `p`, if `p` is prime, `p` is odd, `a` and `p` are coprime, and `a` is not a quadratic residue modulo `p`, then `a` raised to the power of `(p - 1) / 2` is congruent to the factorial of `p - 1` modulo `p`.

### Informal sketch
* The proof starts by assuming the conditions: `p` is prime, `p` is odd, `a` and `p` are coprime, and `a` is not a quadratic residue modulo `p`.
* It uses `REPEAT STRIP_TAC` to strip the quantifiers and implications, and then applies various rewriting and simplification tactics.
* The proof proceeds by cases, considering whether `p` is `0` or not. If `p` is `0`, it derives a contradiction using `PRIME_0`.
* For non-zero `p`, it applies `ASM_SIMP_TAC` to simplify arithmetic expressions and `CONG_SOLVE_UNIQUE_NONTRIVIAL` to establish a congruence relation.
* The proof then uses `MATCH_MP_TAC EQ_IMP` and `AP_TERM_TAC` to derive the final congruence relation.

### Mathematical insight
This theorem relates the concept of quadratic residues to the properties of prime numbers and modular arithmetic. It provides a condition under which a number `a` raised to a certain power is congruent to the factorial of `p - 1` modulo `p`, given that `a` is not a quadratic residue modulo `p`. This result has implications for number theory and cryptography.

### Dependencies
* Theorems:
 + `PRIME_0`
 + `CONG_SOLVE_UNIQUE_NONTRIVIAL`
 + `EQ_IMP`
* Definitions:
 + `is_quadratic_residue`
 + `coprime`
 + `prime`
 + `ODD`
 + `FACT`
 + `EXP`
* Inductive rules:
 + `NPRODUCT_PAIRUP_INDUCT`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of modular arithmetic, coprimality, and quadratic residues. The `CONG_SOLVE_UNIQUE_NONTRIVIAL` tactic may require special attention, as its equivalent may not be directly available in the target system. Additionally, the use of `REPEAT STRIP_TAC` and `ASM_SIMP_TAC` may need to be adapted to the target system's tactic language.

---

## QUADRATIC_RESIDUE_FACT

### Name of formal statement
QUADRATIC_RESIDUE_FACT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_FACT = prove
 (`!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ a is_quadratic_residue (mod p)
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 2)) (mod p)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  SUBGOAL_THEN `3 <= p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN UNDISCH_TAC `ODD(p)` THEN
    ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    UNDISCH_TAC `~(p = 2)` THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `a is_quadratic_residue (mod p)` THEN
  ASM_SIMP_TAC[EXP_2; IS_QUADRATIC_RESIDUE_PAIR; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:num = y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i:num. i`; `p:num`; `(p - 3) DIV 2`;
   `(1..p-1) DELETE x DELETE y`; `a:num`] NPRODUCT_PAIRUP_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG_1;
                 CARD_DELETE; IN_DELETE; CARD_NUMSEG_1] THEN
    SIMP_TAC[ARITH_RULE `p - 1 - 1 - 1 = p - 3`] THEN
    ASM_SIMP_TAC[GSYM EVEN_DIV; EVEN_SUB; ARITH; NOT_EVEN] THEN
    X_GEN_TAC `u:num` THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:num`; `p:num`; `u:num`] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_MESON_TAC[CONG_SOLVE_UNIQUE; PRIME_0; PRIME_COPRIME_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `x:num`] QUADRATIC_RESIDUE_PAIR_PRODUCT) THEN
  ASM_SIMP_TAC[EXP_2; IMP_IMP; ARITH_RULE `x + y = p ==> p - x = y`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_MULT) THEN
  ASM_SIMP_TAC[NPRODUCT_DELETE; GSYM MULT_ASSOC; IN_DELETE;
               FINITE_DELETE; IN_NUMSEG_1; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); GSYM FACT_NPRODUCT; ARITH_RULE
   `3 <= p ==> SUC((p - 3) DIV 2) = (p - 1) DIV 2`] THEN
  ASM_SIMP_TAC[FACT; ARITH_RULE `3 <= p ==> p - 1 = SUC(p - 2)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= p ==> SUC(p - 2) = p - 1`] THEN
  ASM_MESON_TAC[COPRIME_MINUS1; CONG_MULT_LCANCEL; CONG_SYM])
```

### Informal statement
For all `a` and `p`, if `p` is prime, `p` is odd, `a` and `p` are coprime, and `a` is a quadratic residue modulo `p`, then `a` raised to the power of `(p - 1) / 2` is congruent to the factorial of `p - 2` modulo `p`.

### Informal sketch
* The proof starts by assuming `3 <= p` and `p` is not equal to `0`, then uses `PRIME_GE_2` to establish that `p` is greater than or equal to `2`.
* It then considers the case when `p = 2` and uses `ARITH` and `ODD` to derive a contradiction, thus establishing that `p` must be greater than `2`.
* The proof then uses `IS_QUADRATIC_RESIDUE_PAIR` and `LEFT_IMP_EXISTS_THM` to establish the existence of `x` and `y` such that `x` and `y` are distinct, `x` and `y` are both less than `p`, and `x * y` is congruent to `a` modulo `p`.
* The proof then applies `NPRODUCT_PAIRUP_INDUCT` to establish the result for all `p` greater than or equal to `3`.
* The key steps involve using `CONG_SOLVE_UNIQUE_NONTRIVIAL` to establish the uniqueness of the solution, and `QUADRATIC_RESIDUE_PAIR_PRODUCT` to establish the product of the quadratic residues.
* The proof also uses various arithmetic properties, such as `EVEN_DIV`, `EVEN_SUB`, and `NOT_EVEN`, to simplify the expressions.

### Mathematical insight
This theorem provides a deep connection between quadratic residues and the properties of prime numbers. It shows that for a prime `p`, if `a` is a quadratic residue modulo `p`, then `a` raised to the power of `(p - 1) / 2` is congruent to the factorial of `p - 2` modulo `p`. This result has significant implications in number theory and cryptography.

### Dependencies
* Theorems:
	+ `PRIME_GE_2`
	+ `IS_QUADRATIC_RESIDUE_PAIR`
	+ `LEFT_IMP_EXISTS_THM`
	+ `NPRODUCT_PAIRUP_INDUCT`
	+ `CONG_SOLVE_UNIQUE_NONTRIVIAL`
	+ `QUADRATIC_RESIDUE_PAIR_PRODUCT`
	+ `COPRIME_MINUS1`
	+ `CONG_MULT_LCANCEL`
	+ `CONG_SYM`
* Definitions:
	+ `is_quadratic_residue`
	+ `coprime`
	+ `prime`
	+ `EXP`
	+ `FACT`
	+ `ODD`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of arithmetic properties, such as `EVEN_DIV` and `EVEN_SUB`, as well as the use of `CONG_SOLVE_UNIQUE_NONTRIVIAL` and `QUADRATIC_RESIDUE_PAIR_PRODUCT`. Additionally, the proof relies on the `NPRODUCT_PAIRUP_INDUCT` tactic, which may need to be reimplemented or replaced in the target proof assistant.

---

## WILSON_LEMMA

### Name of formal statement
WILSON_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WILSON_LEMMA = prove
 (`!p. prime(p) ==> (FACT(p - 2) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP PRIME_ODD)
  THENL [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC CONG_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `p:num`] QUADRATIC_RESIDUE_FACT) THEN
  ASM_MESON_TAC[is_quadratic_residue; COPRIME_SYM; COPRIME_1; CONG_REFL;
                EXP_ONE; CONG_SYM])
```

### Informal statement
For all prime numbers $p$, it holds that $(p-2)! \equiv 1 \pmod{p}$.

### Informal sketch
* The proof starts by assuming a prime number $p$ and aiming to show that $(p-2)! \equiv 1 \pmod{p}$.
* It utilizes the fact that $p$ is odd, as derived from `PRIME_ODD`, to establish a basis for further reasoning.
* The proof then applies the `QUADRATIC_RESIDUE_FACT` theorem, specifically for the case where the quadratic residue is $1$ and the modulus is $p$.
* Key steps involve using `CONV_TAC` with `NUM_REDUCE_CONV` and `CONG_CONV` to simplify expressions and apply congruence properties.
* The use of `ASM_MESON_TAC` with various theorems (`is_quadratic_residue`, `COPRIME_SYM`, `COPRIME_1`, `CONG_REFL`, `EXP_ONE`, `CONG_SYM`) helps in deriving the final congruence.

### Mathematical insight
This lemma is a part of Wilson's theorem, which states that for any prime number $p$, $(p-1)! \equiv -1 \pmod{p}$. The current lemma establishes a related but distinct property, focusing on $(p-2)!$ being congruent to $1$ modulo $p$. This highlights the intricate properties of factorials and their behavior with respect to modular arithmetic, especially in relation to prime numbers.

### Dependencies
* Theorems:
  - `PRIME_ODD`
  - `QUADRATIC_RESIDUE_FACT`
  - `is_quadratic_residue`
  - `COPRIME_SYM`
  - `COPRIME_1`
  - `CONG_REFL`
  - `EXP_ONE`
  - `CONG_SYM`
* Tactics and functions:
  - `REPEAT`
  - `STRIP_TAC`
  - `ONCE_REWRITE_TAC`
  - `CONG_SYM`
  - `FIRST_ASSUM`
  - `DISJ_CASES_THEN2`
  - `SUBST_ALL_TAC`
  - `ASSUME_TAC`
  - `MATCH_MP`
  - `CONV_TAC`
  - `NUM_REDUCE_CONV`
  - `CONG_CONV`
  - `MP_TAC`
  - `SPECL`
  - `ASM_MESON_TAC`

### Porting notes
When translating this lemma into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to the handling of modular arithmetic, the representation of prime numbers, and the implementation of the `QUADRATIC_RESIDUE_FACT` theorem. Additionally, the use of tacticals like `REPEAT`, `STRIP_TAC`, and `CONV_TAC` may need to be adapted to the target system's proof scripting language. It is also important to ensure that the ported version correctly captures the quantification over all prime numbers $p$ and maintains the precise logical structure of the original proof.

---

## WILSON_IMP

### Name of formal statement
WILSON_IMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WILSON_IMP = prove
 (`!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`,
  SIMP_TAC[FACT; PRIME_GE_2; ARITH_RULE `2 <= p ==> p - 1 = SUC(p - 2)`] THEN
  MESON_TAC[CONG_MULT; MULT_CLAUSES; WILSON_LEMMA; CONG_REFL])
```

### Informal statement
For all primes `p`, it holds that the factorial of `p-1` is congruent to `p-1` modulo `p`.

### Informal sketch
* The proof starts with the assumption that `p` is a prime number.
* It then simplifies the expression `FACT(p - 1)` using the `FACT` definition and properties of arithmetic, leveraging the fact that `p` is at least 2 (`PRIME_GE_2`).
* The `SIMP_TAC` tactic is used to simplify the expression `p - 1` to `SUC(p - 2)`, establishing a relationship between `p` and its predecessor.
* The `MESON_TAC` tactic is then applied with a set of relevant theorems, including `CONG_MULT`, `MULT_CLAUSES`, `WILSON_LEMMA`, and `CONG_REFL`, to establish the congruence relation `(FACT(p - 1) == p - 1) (mod p)`.

### Mathematical insight
This theorem is a formalization of Wilson's theorem, which states that a number `p` is prime if and only if `(p-1)!` is congruent to `-1` modulo `p`. This specific version, `WILSON_IMP`, focuses on one direction of the implication, assuming `p` is prime and deriving the congruence relation. The theorem is fundamental in number theory and is used in various proofs and applications.

### Dependencies
* Theorems:
  + `PRIME_GE_2`
  + `WILSON_LEMMA`
  + `CONG_MULT`
  + `MULT_CLAUSES`
  + `CONG_REFL`
* Definitions:
  + `FACT`
* Axioms and Rules:
  + `ARITH_RULE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to the handling of modular arithmetic and the factorial function. The `SIMP_TAC` and `MESON_TAC` tactics may not have direct counterparts, so the proof strategy might need to be adapted to the target system's proof automation and tactics. Additionally, the representation of prime numbers and the `WILSON_LEMMA` may require specific definitions or imports in the target system.

---

## WILSON

### Name of formal statement
WILSON

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WILSON = prove
 (`!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`,
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC[WILSON_IMP] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_LT] THEN ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `x < y ==> x <= y - 1`)) THEN
  ASM_SIMP_TAC[GSYM DIVIDES_FACT_PRIME] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `p divides FACT(n - 1) <=> p divides (n - 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_DIVIDES THEN
    MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides 1` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`];
    REWRITE_TAC[DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]])
```

### Informal statement
For all numbers `p`, if `p` is not equal to 1, then `p` is prime if and only if `(p-1)!` is congruent to `p-1` modulo `p`.

### Informal sketch
* The proof starts by assuming `~(p = 1)` and then proceeds to prove the equivalence between `prime p` and `(FACT(p - 1) == p - 1) (mod p)`.
* It uses `X_GEN_TAC` to introduce a generic number `n`, which is then discharged.
* The proof then applies `EQ_TAC` to split the equivalence into two separate implications.
* It utilizes `SIMP_TAC` with `WILSON_IMP` and applies `MATCH_MP` with `PRIME_FACTOR` to derive a key intermediate result.
* The proof then proceeds with case analysis on `n = 0` and `n = p`, using `ASM_CASES_TAC` and `ASM_REWRITE_TAC` to simplify the expressions.
* It leverages `DIVIDES_LE` and `CONG_DIVIDES` to establish relationships between divisibility and congruence.
* The proof concludes by deriving `p divides 1` and using `PRIME_1` to finalize the argument.

### Mathematical insight
This theorem provides a characterization of prime numbers in terms of the congruence of factorials. The statement is a formalization of Wilson's theorem, which states that a number `p` is prime if and only if `(p-1)!` is congruent to `-1` modulo `p`. The given formalization uses `p-1` instead of `-1`, which is equivalent due to the properties of modular arithmetic.

### Dependencies
* `PRIME_FACTOR`
* `DIVIDES_LE`
* `CONG_DIVIDES`
* `CONG_DIVIDES_MODULUS`
* `WILSON_IMP`
* `PRIME_1`
* `GSYM DIVIDES_FACT_PRIME`
* `ARITH_RULE`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of modular arithmetic, factorial functions, and the `DIVIDES` relation. The use of `X_GEN_TAC` and `DISCH_TAC` may need to be adapted to the target system's tactic language. Additionally, the `MATCH_MP` and `SIMP_TAC` tactics may have equivalents in other systems, but their exact usage might differ.

---

## EULER_CRITERION

### Name of formal statement
EULER_CRITERION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_CRITERION = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a EXP ((p - 1) DIV 2) ==
              (if a is_quadratic_residue (mod p) then 1 else p - 1)) (mod p)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP PRIME_ODD) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COND_ID; EXP; CONG_REFL] THEN
  ASM_MESON_TAC[WILSON_LEMMA; WILSON_IMP; CONG_TRANS; CONG_SYM;
                QUADRATIC_RESIDUE_FACT; QUADRATIC_NONRESIDUE_FACT])
```

### Informal statement
For all integers `a` and primes `p` such that `a` and `p` are coprime, it holds that `a` raised to the power of `(p - 1) / 2` is congruent modulo `p` to `1` if `a` is a quadratic residue modulo `p`, and to `p - 1` otherwise.

### Informal sketch
* The proof starts with the assumption that `p` is a prime number and `a` is coprime to `p`.
* It then applies `WILSON_LEMMA` and `WILSON_IMP` to establish a relationship between `a`, `p`, and the concept of quadratic residues.
* The proof uses `CONG_TRANS` and `CONG_SYM` to manipulate congruences and ultimately derive the desired result.
* Key steps involve case analysis based on whether `a` is a quadratic residue modulo `p` or not, leveraging `QUADRATIC_RESIDUE_FACT` and `QUADRATIC_NONRESIDUE_FACT`.

### Mathematical insight
The Euler criterion is a fundamental result in number theory that characterizes quadratic residues modulo a prime `p`. It states that an integer `a` is a quadratic residue modulo `p` if and only if `a` raised to the power of `(p - 1) / 2` is congruent to `1` modulo `p`. This criterion is essential for various applications in number theory, cryptography, and coding theory.

### Dependencies
* Theorems:
  * `WILSON_LEMMA`
  * `WILSON_IMP`
  * `QUADRATIC_RESIDUE_FACT`
  * `QUADRATIC_NONRESIDUE_FACT`
* Definitions:
  * `prime`
  * `coprime`
  * `is_quadratic_residue`
  * `EXP`
  * `CONG_REFL`
  * `COND_ID`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of modular arithmetic, quadratic residues, and the specific formulation of Wilson's lemma and its implications. Additionally, the use of `REPEAT STRIP_TAC` and `FIRST_ASSUM` may require equivalent tactics or strategies in the target system to manage assumptions and apply theorems effectively.

---

## GAUSS_LEMMA_1

### Name of formal statement
GAUSS_LEMMA_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_1 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> nproduct(1..r) (\x. let b = (a * x) MOD p in
                           if b <= r then b else p - b) =
       nproduct(1..r) (\x. x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
  REWRITE_TAC[I_DEF] THEN MATCH_MP_TAC NPRODUCT_INJECTION THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  ABBREV_TAC `f = \x. let b = (a * x) MOD p in
                      if b <= r then b else p - b` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[IN_NUMSEG] THEN
    LET_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THENL
     [ALL_TAC; EXPAND_TAC "p" THEN ARITH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[DIVISION; NOT_LE; SUB_EQ_0; PRIME_0]] THEN
    EXPAND_TAC "b" THEN ASM_SIMP_TAC[GSYM DIVIDES_MOD; PRIME_IMP_NZ] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1];
      ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 <= 0)`;
                    ARITH_RULE `~(2 * r + 1 <= i /\ i <= r)`]];
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `p:num` THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `i <= r ==> i < 2 * r + 1`] ; ALL_TAC]) THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a:num` THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `(if a then x else p - x) = (if b then y else p - y) ==> x < p /\ y < p
    ==> x = y \/ x + y = p`)) THEN ASM_SIMP_TAC[DIVISION] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[CONG]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(MOD)`) THEN
  ASM_SIMP_TAC[MOD_ADD_MOD] THEN ASM_SIMP_TAC[GSYM CONG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_DIVIDES) THEN
  ASM_SIMP_TAC[GSYM LEFT_ADD_DISTRIB; PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + j = 0)`] THEN
  MAP_EVERY UNDISCH_TAC [`i <= r`; `j <= r`; `2 * r + 1 = p`] THEN ARITH_TAC)
```

### Informal statement
For a prime number `p`, if `a` is coprime to `p` and `2 * r + 1 = p`, then the product from 1 to `r` of the function `f(x) = (a * x) MOD p` if `(a * x) MOD p` is less than or equal to `r`, otherwise `p - (a * x) MOD p`, is equal to the product from 1 to `r` of `x`. This statement involves the conditions that `p` is prime, `a` and `p` are coprime, and a specific relationship between `r` and `p`.

### Informal sketch
* The proof starts by assuming `p` is prime, `a` and `p` are coprime, and `2 * r + 1 = p`.
* It then applies various simplifications and properties of prime numbers, coprime numbers, and modular arithmetic to establish the equality of the two products.
* Key steps involve using the `NPRODUCT_INJECTION` theorem, properties of finite sequences (`FINITE_NUMSEG`), and modular arithmetic properties (`DIVIDES_MOD`, `PRIME_DIVPROD_EQ`).
* The proof also involves case analysis based on the value of `(a * x) MOD p` relative to `r`, and uses properties of congruence and divisibility.
* The `CONG_IMP_EQ` and `CONG_MULT_LCANCEL` theorems are used to establish congruences necessary for the proof.
* The `ABBREV_TAC` is used to define an auxiliary function `f` that simplifies the expression involving `(a * x) MOD p`.

### Mathematical insight
Gauss's Lemma is a fundamental result in number theory, relating the properties of prime numbers, coprime numbers, and modular arithmetic. This specific formulation involves a product of terms that depend on the relationship between `a`, `x`, and `p`, and shows that under certain conditions, this product simplifies to a product of natural numbers up to `r`. The lemma is crucial in various number theoretic proofs and applications, showcasing the deep connections between arithmetic properties and modular forms.

### Dependencies
* Theorems:
  + `PRIME_IMP_NZ`
  + `NPRODUCT_INJECTION`
  + `CONG_IMP_EQ`
  + `CONG_MULT_LCANCEL`
  + `PRIME_DIVPROD_EQ`
  + `DIVIDES_MOD`
* Definitions:
  + `nproduct`
  + `coprime`
  + `prime`
* Axioms and rules:
  + `ARITH_RULE`
  + `DIVISION`
  + `SUB_EQ_0`
  + `PRIME_0`
  + `PRIME_1`

### Porting notes
When porting this lemma to another proof assistant, special attention should be given to the handling of modular arithmetic, coprime numbers, and the properties of prime numbers. The `NPRODUCT_INJECTION` theorem and its equivalent in the target system will be crucial, as well as the ability to define and manipulate functions like `f` within the proof. Differences in how binders and quantifiers are handled may also require careful consideration. Additionally, the use of `ABBREV_TAC` for defining auxiliary functions might need to be adapted based on the target system's capabilities for defining and using such functions within proofs.

---

## GAUSS_LEMMA_2

### Name of formal statement
GAUSS_LEMMA_2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_2 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> (nproduct(1..r) (\x. let b = (a * x) MOD p in
                            if b <= r then b else p - b) ==
        (p - 1) EXP (CARD {x | x IN 1..r /\ r < (a * x) MOD p}) *
        a EXP r * nproduct(1..r) (\x. x)) (mod p)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {x | x IN 1..r /\ (a * x) MOD p <= r}` THEN
  MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC
   `nproduct(1..r) (\x. (if x IN s then 1 else p - 1) * (a * x) MOD p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_NPRODUCT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN LET_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; CONG_REFL] THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN MATCH_MP_TAC CONG_SUB THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; MULT_CLAUSES; CONG_REFL] THEN
    REWRITE_TAC[ARITH_RULE `b <= p /\ (1 <= p \/ b = 0) <=> b <= p`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    DISCH_THEN(MP_TAC o SPEC `a * i:num` o MATCH_MP DIVISION o
     MATCH_MP (ARITH_RULE `2 <= p ==> ~(p = 0)`)) THEN
    ASM_SIMP_TAC[LT_IMP_LE; cong; nat_mod] THEN DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b:num`; `1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC CONG_MULT THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
    SIMP_TAC[NPRODUCT_DELTA_CONST; FINITE_NUMSEG] THEN
    MATCH_MP_TAC EQ_IMP_CONG THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[NOT_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `nproduct(1..r) (\x. a * x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CONG_MOD; PRIME_IMP_NZ; CONG_NPRODUCT; FINITE_NUMSEG];
    SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG; NPRODUCT_CONST; CARD_NUMSEG_1] THEN
    REWRITE_TAC[CONG_REFL]])
```

### Informal statement
For a prime `p`, if `a` is coprime to `p` and `2 * r + 1 = p`, then the following congruence holds modulo `p`: the product from `1` to `r` of `(a * x) MOD p` if `(a * x) MOD p` is less than or equal to `r`, otherwise `p - (a * x) MOD p`, is equal to `(p - 1)` raised to the power of the cardinality of the set of `x` in `1..r` such that `r` is less than `(a * x) MOD p`, times `a` raised to the power of `r`, times the product from `1` to `r` of `x`.

### Informal sketch
* The proof starts by assuming `prime p`, `coprime(a, p)`, and `2 * r + 1 = p`.
* It then defines a set `s` as `{x | x IN 1..r /\ (a * x) MOD p <= r}` and applies `CONG_TRANS` to transform the product expression.
* The proof uses `MATCH_MP_TAC CONG_NPRODUCT` and `REWRITE_TAC` to simplify the product expression and apply properties of modular arithmetic.
* Key steps involve case analysis on whether `x` is in `s` or not, and using properties of `nproduct` and modular exponentiation.
* The proof concludes by applying `CONG_MULT` and simplifying the resulting expression to match the desired form.

### Mathematical insight
This theorem appears to be related to properties of quadratic residues and the behavior of modular arithmetic under certain conditions, specifically when `2 * r + 1 = p`, which suggests a connection to the properties of prime numbers and their relationship with quadratic residues.

### Dependencies
* Theorems:
  + `PRIME_GE_2`
  + `CONG_TRANS`
  + `CONG_NPRODUCT`
  + `CONG_MULT`
  + `PRIME_IMP_NZ`
* Definitions:
  + `nproduct`
  + `coprime`
  + `prime`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of modular arithmetic and the properties of `nproduct`. The use of `MATCH_MP_TAC` and `REWRITE_TAC` suggests that the proof relies on the ability to apply theorems and rewrite terms in a flexible manner, which may require careful handling in other systems. Additionally, the definition of the set `s` and its role in the proof may need to be carefully translated to ensure that the resulting proof is correct and efficient.

---

## GAUSS_LEMMA_3

### Name of formal statement
GAUSS_LEMMA_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_3 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
   `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * a EXP r` THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
    SUBGOAL_THEN `r = (p - 1) DIV 2`
     (fun th -> ASM_SIMP_TAC[th; EULER_CRITERION]) THEN
    EXPAND_TAC "p" THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_MULT_RCANCEL THEN
  EXISTS_TAC `nproduct (1..r) (\x. x)` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; GSYM MULT_ASSOC;
               SIMP_RULE[GAUSS_LEMMA_1] GAUSS_LEMMA_2] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_NPRODUCT THEN
  REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)
```

### Informal statement
For a prime `p`, if `a` is coprime to `p` and `2 * r + 1 = p`, then the following congruence holds modulo `p`: `((p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * (if a is_quadratic_residue mod p then 1 else p - 1)) == 1`. This statement involves conditions on `p`, `a`, and `r`, and it relates to properties of quadratic residues and the cardinality of specific sets.

### Informal sketch
* The proof begins by applying `CONG_TRANS` and introducing a new expression `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * a EXP r`.
* It then proceeds with case analysis, using `CONJ_TAC` to split into two subgoals.
* One subgoal involves applying `CONG_MULT` and using properties of congruence and quadratic residues, including `EULER_CRITERION`.
* The other subgoal involves `CONG_MULT_RCANCEL`, introducing a product over a range, and applying various simplification rules, including `GAUSS_LEMMA_1` and `GAUSS_LEMMA_2`.
* The proof further uses `COPRIME_NPRODUCT` and `PRIME_COPRIME_LT` to establish the necessary conditions for coprimality and the properties of prime numbers.
* Key steps involve manipulating congruences, using properties of quadratic residues, and applying arithmetic and algebraic simplifications.

### Mathematical insight
This theorem, `GAUSS_LEMMA_3`, is part of a broader theory related to quadratic residues and the properties of prime numbers. It specifically addresses conditions under which certain congruences hold, involving the cardinality of sets defined by modular arithmetic conditions and properties of quadratic residues. The theorem is likely a component in a larger proof or theory, possibly related to the properties of primes, quadratic residues, or the distribution of certain numbers within modular arithmetic.

### Dependencies
#### Theorems
* `CONG_TRANS`
* `CONG_MULT`
* `CONG_REFL`
* `EULER_CRITERION`
* `CONG_MULT_RCANCEL`
* `COPRIME_NPRODUCT`
* `PRIME_COPRIME_LT`
* `GAUSS_LEMMA_1`
* `GAUSS_LEMMA_2`
#### Definitions
* `prime`
* `coprime`
* `is_quadratic_residue`
* `nproduct`
* `CARD`
* `IN_NUMSEG`
* `FINITE_NUMSEG`

---

## GAUSS_LEMMA_4

### Name of formal statement
GAUSS_LEMMA_4

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_4 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((if EVEN(CARD{x | x IN 1..r /\ r < (a * x) MOD p}) then 1 else p - 1) *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
              (if a is_quadratic_residue mod p then 1 else p - 1)` THEN
  ASM_SIMP_TAC[GAUSS_LEMMA_3] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  ASM_SIMP_TAC[CONG_EXP_MINUS1; CONG_MULT; CONG_REFL; PRIME_GE_2])
```

### Informal statement
For all prime numbers `p`, all integers `a` that are coprime to `p`, and all integers `r` such that `2 * r + 1 = p`, if the cardinality of the set of `x` in `1..r` where `r` is less than `(a * x) MOD p` is even, then the product of `1` and the `Legendre symbol` of `a` modulo `p` is congruent to `1` modulo `p`. Otherwise, the product of `p - 1` and the `Legendre symbol` of `a` modulo `p` is congruent to `1` modulo `p`.

### Informal sketch
* The proof starts by assuming `prime p`, `coprime(a, p)`, and `2 * r + 1 = p`.
* It then considers the set of `x` in `1..r` where `r < (a * x) MOD p` and determines whether its cardinality is even or odd.
* Depending on the parity, it applies different cases to simplify the expression involving the `Legendre symbol` of `a` modulo `p`.
* The `CONG_TRANS` tactic is used to establish a congruence relation, and `EXISTS_TAC` is used to introduce a witness for this relation.
* The proof then simplifies the expression using properties of congruence, such as `CONG_EXP_MINUS1`, `CONG_MULT`, and `CONG_REFL`, and applies `GAUSS_LEMMA_3` to reach the final conclusion.

### Mathematical insight
This lemma appears to be related to quadratic reciprocity, a fundamental result in number theory. The `Legendre symbol` is used to denote whether a number is a quadratic residue modulo `p`. The lemma provides a condition under which the product of certain terms is congruent to `1` modulo `p`, which can be useful in establishing more general results about quadratic residues.

### Dependencies
* `GAUSS_LEMMA_3`
* `CONG_TRANS`
* `CONG_EXP_MINUS1`
* `CONG_MULT`
* `CONG_REFL`
* `PRIME_GE_2`

### Porting notes
When porting this lemma to another proof assistant, special attention should be paid to the handling of the `Legendre symbol` and the `CONG` predicates, as these may be represented differently in other systems. Additionally, the use of `EXISTS_TAC` and `MATCH_MP_TAC` may need to be adapted to the target system's tactic language.

---

## GAUSS_LEMMA

### Name of formal statement
GAUSS_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA = prove
 (`!a p r. prime p /\ coprime(a,p) /\ 2 * r + 1 = p
           ==> (a is_quadratic_residue (mod p) <=>
                EVEN(CARD {x | x IN 1..r /\ r < (a * x) MOD p}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_COND_LEMMA THEN EXISTS_TAC `p:num` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "p" THEN ASM_CASES_TAC `r = 0` THENL
     [REWRITE_TAC[ASSUME `r = 0`; ARITH; PRIME_1];
      UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP GAUSS_LEMMA_4) THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[CONG_REFL]) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[CONG_SYM])
```

### Informal statement
For all numbers $a$, prime numbers $p$, and numbers $r$, if $p$ is prime, $a$ and $p$ are coprime, and $2r + 1 = p$, then $a$ is a quadratic residue modulo $p$ if and only if the number of $x$ in the range $1$ to $r$ such that $r < (a \cdot x) \mod p$ is even.

### Informal sketch
* The proof starts by assuming the premises: $p$ is prime, $a$ and $p$ are coprime, and $2r + 1 = p$.
* It then applies the `CONG_COND_LEMMA` to establish a congruence relation, introducing $p$ as a key component.
* The proof proceeds by cases, considering whether $r = 0$ or $r \neq 0$, and uses `ARITH` and `PRIME_1` to handle the $r = 0$ case.
* For $r \neq 0$, it utilizes `GAUSS_LEMMA_4` and applies conditional cases, simplifying with `CONG_REFL` and `MULT_CLAUSES`, and finally applying `CONG_SYM` to reach the conclusion.
* The use of `MATCH_MP_TAC`, `EXISTS_TAC`, and `CONJ_TAC` indicates a structured approach to applying lemmas and establishing the existence of key elements.

### Mathematical insight
The Gauss Lemma is a fundamental result in number theory, providing a criterion for determining whether a number $a$ is a quadratic residue modulo a prime $p$. This lemma is crucial in many applications, including the law of quadratic reciprocity. The formalization of this lemma in HOL Light demonstrates the power of formal proof assistants in capturing intricate mathematical reasoning.

### Dependencies
* `prime`
* `coprime`
* `is_quadratic_residue`
* `CONG_COND_LEMMA`
* `GAUSS_LEMMA_4`
* `CONG_REFL`
* `MULT_CLAUSES`
* `CONG_SYM`

### Porting notes
When porting this lemma to another proof assistant, special attention should be given to the handling of modular arithmetic, coprimality, and the quadratic residue predicate. The `MATCH_MP_TAC` and `EXISTS_TAC` tactics may need to be translated into equivalent constructs in the target system, potentially involving different strategies for applying lemmas and introducing witnesses. Additionally, the conditional cases and arithmetic reasoning may require careful translation to ensure that the proof structure is preserved.

---

## GAUSS_LEMMA_SYM

### Name of formal statement
GAUSS_LEMMA_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_SYM = prove
 (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (q is_quadratic_residue (mod p) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   q * x < p * y /\ p * y <= q * x + r}))`,
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `p:num`; `r:num`] GAUSS_LEMMA) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `CARD {x,y | x IN 1..r /\ y IN 1..s /\
                y = (q * x) DIV p + 1 /\ r < (q * x) MOD p}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBCROSS_DETERMINATE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; ARITH_RULE `1 <= x + 1`] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p * (q * x) DIV p + r < q * r` MP_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `q * x` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ; LT_ADD_LCANCEL; DIVISION];
      MAP_EVERY EXPAND_TAC ["p"; "q"] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (ARITH_RULE `(2 * r + 1) * d + r < (2 * s + 1) * r
                    ==> (2 * r) * d < (2 * r) * s`)) THEN
      SIMP_TAC[LT_MULT_LCANCEL; ARITH_RULE `x < y ==> x + 1 <= y`]];
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o SPEC `q * x` o MATCH_MP DIVISION) THEN
      FIRST_ASSUM(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      UNDISCH_TAC `2 * r + 1 = p` THEN ARITH_TAC;
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [ALL_TAC;
        DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC(ARITH_RULE
         `!p d. 2 * r + 1 = p /\ p * (d + 1) <= (d * p + m) + r ==> r < m`) THEN
        MAP_EVERY EXISTS_TAC [`p:num`; `(q * x) DIV p`] THEN
        ASM_MESON_TAC[DIVISION; PRIME_IMP_NZ]] THEN
      MATCH_MP_TAC(ARITH_RULE `~(x <= y) /\ ~(y + 2 <= x) ==> x = y + 1`) THEN
      REPEAT STRIP_TAC THENL
       [SUBGOAL_THEN `y * p <= ((q * x) DIV p) * p` MP_TAC THENL
         [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC];
        SUBGOAL_THEN `((q * x) DIV p + 2) * p <= y * p` MP_TAC THENL
         [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC]] THEN
      MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o SPEC `q * x` o MATCH_MP DIVISION) THEN
      ASM_ARITH_TAC])
```

### Informal statement
For all primes `p` and `q` that are coprime, and for all natural numbers `r` and `s` such that `2 * r + 1 = p` and `2 * s + 1 = q`, it holds that `q` is a quadratic residue modulo `p` if and only if the cardinality of the set of pairs `(x, y)` where `x` is in `1..r`, `y` is in `1..s`, `q * x < p * y`, and `p * y <= q * x + r` is even.

### Informal sketch
The proof involves several key steps:
* Applying the `GAUSS_LEMMA` theorem with specific instantiations to relate the quadratic residuosity of `q` modulo `p` to a counting problem involving pairs `(x, y)` that satisfy certain inequalities.
* Using `COPRIME_SYM` to exploit the symmetry of coprimality between `p` and `q`.
* Employing various arithmetic and logical manipulations to transform the counting problem into a more manageable form, including the use of `CARD_SUBCROSS_DETERMINATE` and `DIVISION`.
* Utilizing properties of primes, such as `PRIME_IMP_NZ`, and arithmetic rules to simplify and derive necessary inequalities.
* Applying `EQ_TRANS` and `EVEN` to conclude the equivalence between the quadratic residuosity condition and the parity of the cardinality of a specific set.

### Mathematical insight
This theorem provides a symmetrical version of a lemma related to Gauss's work on quadratic residues, offering a condition under which a number `q` is a quadratic residue modulo another prime `p`, in terms of a counting argument involving pairs of numbers satisfying certain inequalities. The symmetrical nature of the statement, facilitated by the use of coprime numbers, simplifies the expression and potentially its application in further proofs.

### Dependencies
* Theorems:
  + `GAUSS_LEMMA`
  + `COPRIME_SYM`
  + `CARD_SUBCROSS_DETERMINATE`
  + `DIVISION`
  + `PRIME_IMP_NZ`
* Definitions:
  + `is_quadratic_residue`
  + `coprime`
  + `prime` 

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of:
- Quantifiers and their scopes
- The `coprime` and `prime` predicates
- Arithmetic and logical manipulations, ensuring that the target system's libraries support similar rules and theorems (e.g., `DIVISION`, `PRIME_IMP_NZ`)
- The definition and usage of `is_quadratic_residue`, which might require adjustments based on the specific formalization of quadratic residues in the target system.

---

## GAUSS_LEMMA_SYM'

### Name of formal statement
GAUSS_LEMMA_SYM'

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_SYM' = prove
 (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (p is_quadratic_residue (mod q) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   p * y < q * x /\ q * x <= p * y + s}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `p:num`; `s:num`; `r:num`] GAUSS_LEMMA_SYM) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CARD_SUBCROSS_SWAP] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; CONJ_ACI])
```

### Informal statement
For all primes `p` and `q` that are coprime, and for all natural numbers `r` and `s` such that `2 * r + 1 = p` and `2 * s + 1 = q`, the following equivalence holds: `p` is a quadratic residue modulo `q` if and only if the cardinality of the set of pairs `(x, y)` with `x` in `1..r` and `y` in `1..s` such that `p * y < q * x` and `q * x <= p * y + s` is even.

### Informal sketch
* The proof starts by assuming `p` and `q` are prime and coprime, and `r` and `s` satisfy the given conditions.
* It then applies the `GAUSS_LEMMA_SYM` theorem with specific instantiations for `p`, `q`, `s`, and `r`.
* The `COPRIME_SYM` property is used to rewrite the coprime condition.
* The proof involves a series of rewritings and simplifications using various theorems and properties, including `CARD_SUBCROSS_SWAP`, `EXTENSION`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`, and `CONJ_ACI`.
* The key steps involve manipulating the set of pairs `(x, y)` and applying properties of cardinality and quadratic residues.

### Mathematical insight
This theorem provides a condition for determining whether a prime `p` is a quadratic residue modulo another prime `q`, in terms of the parity of the cardinality of a specific set of pairs `(x, y)`. This is a significant result in number theory, as it relates to the distribution of quadratic residues and the properties of prime numbers.

### Dependencies
* Theorems:
	+ `GAUSS_LEMMA_SYM`
	+ `COPRIME_SYM`
	+ `CARD_SUBCROSS_SWAP`
	+ `EXTENSION`
	+ `FORALL_PAIR_THM`
	+ `IN_ELIM_PAIR_THM`
	+ `CONJ_ACI`
* Definitions:
	+ `prime`
	+ `coprime`
	+ `is_quadratic_residue`
	+ `CARD` 

### Porting notes
When porting this theorem to other proof assistants, pay attention to the handling of binders, quantifiers, and the `CARD` function, as these may be represented differently. Additionally, the `GAUSS_LEMMA_SYM` theorem and other dependencies may need to be ported or re-proved in the target system.

---

## RECIPROCITY_SET_LEMMA

### Name of formal statement
RECIPROCITY_SET_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RECIPROCITY_SET_LEMMA = prove
(`!a b c d r s.
        a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
        PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
        ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(a:num#num->bool) + CARD(b:num#num->bool) +
                CARD(c:num#num->bool) + CARD(d:num#num->bool) = r * s`
   (fun th -> MP_TAC(AP_TERM `EVEN` th) THEN
              ASM_REWRITE_TAC[EVEN_ADD; GSYM NOT_EVEN; EVEN_MULT] THEN
              CONV_TAC TAUT) THEN
  SUBGOAL_THEN
   `FINITE(a:num#num->bool) /\ FINITE(b:num#num->bool) /\
    FINITE(c:num#num->bool) /\ FINITE(d:num#num->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(1..r) CROSS (1..s)` THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `CARD:(num#num->bool)->num`) THEN
  SIMP_TAC[CARD_CROSS; CARD_NUMSEG_1; FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PAIRWISE]) THEN
  REWRITE_TAC[PAIRWISE; DISJOINT; ALL] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; SET_RULE
    `a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}`])
```

### Informal statement
For all sets `a`, `b`, `c`, `d` and numbers `r` and `s`, if the union of `a`, `b`, `c`, and `d` equals the Cartesian product of the sets `(1..r)` and `(1..s)`, and `b` and `c` are disjoint from `a` and `d` and from each other, and the cardinality of `b` equals the cardinality of `c`, then the following equivalence holds: the parity (evenness or oddness) of the cardinality of `a` is the same as the parity of the cardinality of `d` if and only if it is not the case that both `r` and `s` are odd.

### Informal sketch
* The proof begins by assuming the premise that `a UNION b UNION c UNION d = (1..r) CROSS (1..s)` and that `PAIRWISE DISJOINT [a;b;c;d]` and `CARD b = CARD c`.
* It then derives the equation `CARD(a) + CARD(b) + CARD(c) + CARD(d) = r * s` using the properties of cardinalities and the given premise.
* The proof uses the `EVEN` property and its relationship with addition and multiplication to simplify the condition `EVEN(CARD a) <=> EVEN(CARD d)`.
* It leverages the `FINITE` property of the sets and the `PAIRWISE` disjointness to apply various set-theoretic rules and theorems, including `CARD_UNION` and `FINITE_UNION`.
* Key steps involve using `MP_TAC`, `AP_TERM`, `ASM_REWRITE_TAC`, and `CONV_TAC` to manipulate the logical expressions and apply relevant theorems.

### Mathematical insight
This theorem explores the relationship between the cardinalities of sets `a` and `d` and the dimensions `r` and `s` of a Cartesian product, under certain conditions of disjointness and equality of cardinalities among the sets `b` and `c`. It provides insight into how the parity of the cardinalities of `a` and `d` relates to the parities of `r` and `s`, which can be useful in various combinatorial and set-theoretic arguments.

### Dependencies
* Theorems:
  + `EVEN_ADD`
  + `GSYM NOT_EVEN`
  + `EVEN_MULT`
  + `FINITE_CROSS`
  + `FINITE_NUMSEG`
  + `CARD_CROSS`
  + `CARD_NUMSEG_1`
  + `CARD_UNION`
  + `FINITE_UNION`
* Definitions:
  + `PAIRWISE`
  + `DISJOINT`
  + `EVEN`
  + `CARD`
* Tactics and rules:
  + `REPEAT STRIP_TAC`
  + `SUBGOAL_THEN`
  + `MP_TAC`
  + `AP_TERM`
  + `ASM_REWRITE_TAC`
  + `CONV_TAC`
  + `MATCH_MP_TAC`
  + `GEN_REWRITE_RULE`

---

## RECIPROCITY_SIMPLE

### Name of formal statement
RECIPROCITY_SIMPLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RECIPROCITY_SIMPLE = prove
 (`!p q r s.
        prime p /\
        prime q /\
        coprime (p,q) /\
        2 * r + 1 = p /\
        2 * s + 1 = q
        ==> ((q is_quadratic_residue (mod p) <=>
              p is_quadratic_residue (mod q)) <=>
             ~(ODD r /\ ODD s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] GAUSS_LEMMA_SYM) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] GAUSS_LEMMA_SYM') THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN MATCH_MP_TAC RECIPROCITY_SET_LEMMA THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ q * x + r < p * y}` THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ p * y + s < q * x}` THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[PAIRWISE; DISJOINT; EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM;
              ALL; IN_UNION; IN_CROSS; IN_ELIM_PAIR_THM; IN_INTER]
  THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`x IN 1..r`; `y IN 1..s`] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(q * x = p * y)` (fun th -> MP_TAC th THEN ARITH_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(divides) p`) THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[DIVIDES_REFL; PRIME_1; coprime]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `x IN 1..r` THEN REWRITE_TAC[IN_NUMSEG] THEN
    EXPAND_TAC "p" THEN ARITH_TAC;
    ARITH_TAC;
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    REPEAT(EXISTS_TAC `\(x,y). (r + 1) - x,(s + 1) - y`) THEN
    SIMP_TAC[FINITE_SUBCROSS; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG; PAIR_EQ] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    SIMP_TAC[ARITH_RULE `x <= y ==> (y + 1) - ((y + 1) - x) = x`] THEN
    SIMP_TAC[ARITH_RULE
     `1 <= x /\ x <= y ==> 1 <= (y + 1) - x /\ (y + 1) - x <= y`] THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ v + y + z < x + u ==> (y - x) + z < u - v`) THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `x <= r ==> x <= r + 1`] THEN
    REWRITE_TAC[ARITH_RULE `a + x < y + a <=> x < y`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_ARITH_TAC])
```

### Informal statement
For all primes `p` and `q` such that `p` and `q` are coprime, and for all integers `r` and `s` such that `2 * r + 1 = p` and `2 * s + 1 = q`, the following statement holds: `q` is a quadratic residue modulo `p` if and only if `p` is a quadratic residue modulo `q`, if and only if it is not the case that both `r` and `s` are odd.

### Informal sketch
* The proof starts by assuming the given conditions: `p` and `q` are prime, `p` and `q` are coprime, and the relationships between `p`, `q`, `r`, and `s` hold.
* It then applies `GAUSS_LEMMA_SYM` and `GAUSS_LEMMA_SYM'` to establish a connection between the quadratic residues.
* The proof proceeds by rewriting and simplifying the expressions using various properties such as `COPRIME_SYM`, `PAIRWISE`, `DISJOINT`, and `EXTENSION`.
* It then uses `RECIPROCITY_SET_LEMMA` to establish the existence of certain sets that satisfy specific conditions.
* The proof continues by applying various tactics such as `MAP_EVERY X_GEN_TAC`, `MAP_EVERY ASM_CASES_TAC`, and `SUBGOAL_THEN` to derive the desired conclusion.
* Key steps involve using `DIVIDES_LE` and `BIJECTIONS_CARD_EQ` to establish the relationships between the sets and their cardinalities.
* The proof concludes by applying `ARITH_TAC` and `ASM_ARITH_TAC` to finalize the arithmetic arguments.

### Mathematical insight
This theorem establishes a reciprocity relationship between the quadratic residues of two coprime primes `p` and `q`. The condition `2 * r + 1 = p` and `2 * s + 1 = q` implies that `p` and `q` are odd primes, and the theorem provides a criterion for determining whether `q` is a quadratic residue modulo `p` and vice versa. The theorem has implications for number theory, particularly in the study of quadratic residues and reciprocity laws.

### Dependencies
* `GAUSS_LEMMA_SYM`
* `GAUSS_LEMMA_SYM'`
* `RECIPROCITY_SET_LEMMA`
* `DIVIDES_LE`
* `BIJECTIONS_CARD_EQ`
* `PRIME_DIVPROD_EQ`
* `COPRIME_SYM`
* `PAIRWISE`
* `DISJOINT`
* `EXTENSION`
* `IN_NUMSEG`
* `FINITE_SUBCROSS`
* `FINITE_NUMSEG`
* `FORALL_PAIR_THM`
* `IN_ELIM_PAIR_THM`
* `IN_UNION`
* `IN_CROSS`
* `IN_INTER`
* `ARITH_RULE` 

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of binders, arithmetic, and set operations. The use of `MAP_EVERY X_GEN_TAC` and `MAP_EVERY ASM_CASES_TAC` may require special attention, as these tactics are specific to HOL Light. Additionally, the `SUBGOAL_THEN` tactic and the `ARITH_TAC` and `ASM_ARITH_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant. The `RECIPROCITY_SET_LEMMA` and other dependencies should be ported or proven in the target system before attempting to port this theorem.

---

## RECIPROCITY_LEGENDRE

### Name of formal statement
RECIPROCITY_LEGENDRE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RECIPROCITY_LEGENDRE = prove
 (`!p q. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q)
         ==> legendre(p,q) * legendre(q,p) =
             --(&1) pow ((p - 1) DIV 2 * (q - 1) DIV 2)`,
  REPEAT STRIP_TAC THEN MAP_EVERY UNDISCH_TAC [`ODD q`; `ODD p`] THEN
  REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN REWRITE_TAC[ADD1] THEN
  REPEAT(DISCH_THEN (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))) THEN
  REWRITE_TAC[ARITH_RULE `((2 * s + 1) - 1) DIV 2 = s`] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] RECIPROCITY_SIMPLE) THEN
  ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME; INT_POW_NEG; EVEN_MULT; legendre] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_ODD; INT_POW_ONE] THEN
  MAP_EVERY ASM_CASES_TAC [`EVEN r`; `EVEN s`] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[TAUT `~(a <=> b) <=> (a <=> ~b)`] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `p is_quadratic_residue (mod q)` THEN
  ASM_REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG; INT_MUL_LID])
```

### Informal statement
For all prime numbers `p` and `q`, if `p` and `q` are odd, `p` is not equal to `q`, then the product of the Legendre symbols `legendre(p,q)` and `legendre(q,p)` is equal to `-1` raised to the power of the product of the integer divisions of `p-1` and `q-1` by 2.

### Informal sketch
* The proof starts by assuming the premises: `p` and `q` are prime, odd, and distinct.
* It then applies various tactics to simplify and manipulate the expressions involving the Legendre symbol, including `REWRITE_TAC` and `ASM_SIMP_TAC`.
* The proof uses the `RECIPROCITY_SIMPLE` theorem and applies it to the specific case of `p`, `q`, `r`, and `s`.
* It also employs case analysis on the parity of `r` and `s`, and whether `p` is a quadratic residue modulo `q`.
* Key steps involve rewriting and simplifying expressions using properties of arithmetic, such as `DE_MORGAN_THM` and `INT_POW_NEG`.
* The proof concludes by applying `DISCH_THEN` and `ASM_REWRITE_TAC` to reach the final statement.

### Mathematical insight
This theorem establishes a fundamental property of the Legendre symbol, which is crucial in number theory. The Legendre symbol `legendre(a,p)` indicates whether `a` is a quadratic residue modulo `p`. This theorem shows that for distinct odd primes `p` and `q`, the product of the Legendre symbols `legendre(p,q)` and `legendre(q,p)` can be expressed in terms of the powers of `-1`, depending on the parities of `p` and `q`. This has significant implications for understanding quadratic reciprocity and its applications in number theory.

### Dependencies
* Theorems:
  + `RECIPROCITY_SIMPLE`
  + `DISTINCT_PRIME_COPRIME`
  + `INT_POW_NEG`
  + `EVEN_MULT`
  + `legendre`
* Definitions:
  + `ODD`
  + `prime`
  + `legendre`
  + `is_quadratic_residue`
* Tactics and rules:
  + `REPEAT`
  + `STRIP_TAC`
  + `MAP_EVERY`
  + `UNDISCH_TAC`
  + `REWRITE_TAC`
  + `X_GEN_TAC`
  + `SUBST1_TAC`
  + `ASSUME_TAC`
  + `SYM`
  + `MP_TAC`
  + `ASM_SIMP_TAC`
  + `ASM_CASES_TAC`
  + `DISCH_THEN`
  + `K`
  + `ALL_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to the handling of binders, especially in the context of the `X_GEN_TAC` and `SUBST1_TAC` tactics. Additionally, the `REPEAT` and `MAP_EVERY` tactics might need to be replaced with equivalent constructs in the target system. The `legendre` function and related theorems like `RECIPROCITY_SIMPLE` should be defined and proven in the target system before attempting to port this theorem. Differences in arithmetic and modular arithmetic handling between HOL Light and the target system may also require special attention.

---

