# cantor.ml

## Overview

Number of statements: 10

The `cantor.ml` file formalizes Cantor's theorem, a fundamental result in set theory. It provides an ad hoc version of the theorem for the whole type, suggesting a specialized implementation. The file's content is self-contained, with no external dependencies, and is likely used to establish a foundational result in the library. The theorem proved in this file is a key concept in set theory, demonstrating the uncountability of certain sets.

## CANTOR_THM_INJ

### Name of formal statement
CANTOR_THM_INJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_THM_INJ = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:(A->bool)->A`; `g:A->(A->bool)`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[])
```

### Informal statement
It is not the case that there exists a function `f` from the set of functions from `A` to `bool` to `A`, such that for all `x` and `y` in the domain of `f`, if `f(x)` equals `f(y)`, then `x` equals `y`.

### Informal sketch
* The proof starts by assuming the existence of a function `f` that maps functions from `A` to `bool` to elements of `A`.
* It then uses the `REWRITE_TAC` tactic to apply the `INJECTIVE_LEFT_INVERSE` and `NOT_EXISTS_THM` theorems, which helps to rewrite the statement in terms of injectivity.
* The `MAP_EVERY X_GEN_TAC` tactic is used to introduce the functions `f` and `g`, where `g` is a function from `A` to the set of functions from `A` to `bool`.
* The proof then proceeds by assuming the existence of an `x` in `A` such that `g x x` does not hold, and uses the `DISCH_THEN` and `MP_TAC` tactics to derive a contradiction.
* The `MESON_TAC` tactic is used to automatically prove the resulting goal, which shows that the initial assumption of the existence of `f` leads to a contradiction.

### Mathematical insight
This theorem is a version of Cantor's theorem, which states that there is no surjection from a set to its power set. The theorem is important because it shows that the power set of a set is always larger than the set itself, which has significant implications for the foundations of mathematics, particularly in set theory.

### Dependencies
* Theorems:
	+ `INJECTIVE_LEFT_INVERSE`
	+ `NOT_EXISTS_THM`
* Definitions:
	+ None
* Inductive rules:
	+ None

### Porting notes
When porting this theorem to other proof assistants, care should be taken to ensure that the `INJECTIVE_LEFT_INVERSE` and `NOT_EXISTS_THM` theorems are properly translated and applied. Additionally, the use of `MAP_EVERY X_GEN_TAC` and `DISCH_THEN` tactics may require special attention, as the exact equivalent tactics may not be available in the target proof assistant.

---

## CANTOR_THM_SURJ

### Name of formal statement
CANTOR_THM_SURJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_THM_SURJ = prove
 (`~(?f:A->(A->bool). !s. ?x. f x = s)`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:A->(A->bool)`; `f:(A->bool)->A`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;
```

### Informal statement
There does not exist a function `f` from `A` to the set of functions from `A` to boolean such that for all functions `s` from `A` to boolean, there exists an `x` in `A` where `f x` equals `s`.

### Informal sketch
* The proof starts by assuming the existence of a function `f` that maps elements of `A` to functions from `A` to boolean, such that every function `s` from `A` to boolean is in the range of `f`.
* It then uses the `REWRITE_TAC` tactic to apply the `SURJECTIVE_RIGHT_INVERSE` and `NOT_EXISTS_THM` theorems, which likely involve rewriting the statement in terms of surjectivity and handling the negation of existential quantification.
* The `MAP_EVERY X_GEN_TAC` tactic is applied to introduce variables `g` of type `A->(A->bool)` and `f` of type `(A->bool)->A`, setting up the proof to work with these functions.
* The `DISCH_THEN` tactic, combined with `MP_TAC` and `SPEC`, is used to discharge assumptions and apply a specific instantiation, in this case, `\x:A. ~(g x x)`, which involves a diagonalization argument by considering a function `g` such that `g(x)` is a function from `A` to boolean that is different from `f(x)` at `x`.
* Finally, `MESON_TAC` is applied to automatically prove the resulting goal, which likely involves straightforward logical deductions given the setup.

### Mathematical insight
This theorem is related to Cantor's theorem, which states that there is no surjection from a set to its power set. The formal item `CANTOR_THM_SURJ` specifically addresses the non-existence of a surjective function from a set `A` to the set of functions from `A` to boolean (which can be seen as a subset of the power set of `A`), highlighting the fundamental limitations on the size of sets and their power sets.

### Dependencies
* Theorems:
  - `SURJECTIVE_RIGHT_INVERSE`
  - `NOT_EXISTS_THM`
* Definitions and types:
  - `A` (type of the set in question)
  - `bool` (type representing boolean values)

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how surjectivity and the negation of existential quantification are handled. The diagonalization argument used in the proof is a common technique in set theory and should be directly translatable. However, the specific tactics and their order might need adjustments based on the target proof assistant's automation and tactic language.

---

## CANTOR

### Name of formal statement
CANTOR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR = prove
 (`!s:A->bool. s <_c {t | t SUBSET s}`,
  GEN_TAC THEN REWRITE_TAC[lt_c] THEN CONJ_TAC THENL
   [REWRITE_TAC[le_c] THEN EXISTS_TAC `(=):A->A->bool` THEN
    REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM; SUBSET; IN] THEN MESON_TAC[];
    REWRITE_TAC[LE_C; IN_ELIM_THM; SURJECTIVE_RIGHT_INVERSE] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `g:A->(A->bool)` THEN
    DISCH_THEN(MP_TAC o SPEC `\x:A. s(x) /\ ~(g x x)`) THEN
    REWRITE_TAC[SUBSET; IN; FUN_EQ_THM] THEN MESON_TAC[]])
```

### Informal statement
For all subsets $s$ of a non-empty set $A$, there exists a subset $t$ of $s$ such that $s$ is strictly less than $t$ in cardinality, which can be formally expressed as $s <_c \{t \mid t \subseteq s\}$. This statement involves the cardinality comparison operator $<_c$, and the subset relation $\subseteq$.

### Informal sketch
* The proof starts by generalizing the statement for any subset $s$ of $A$, using `GEN_TAC`.
* It then rewrites the cardinality comparison $s <_c \{t \mid t \subseteq s\}$ using `REWRITE_TAC[lt_c]`, and proceeds with a case split using `CONJ_TAC`.
* In the first branch, it establishes the existence of a subset $t$ that is equal to $s$ itself, leveraging the equality relation `(=):A->A->bool` and properties of subset and membership.
* The second branch involves assuming the existence of a function $g:A->(A->bool)$ and deriving a contradiction by finding an element $x$ in $A$ such that $s(x)$ holds but $g(x)$ does not map $x$ to itself, utilizing `DISCH_THEN` and `MP_TAC` for the proof by contradiction.
* Key HOL Light terms involved include `lt_c`, `le_c`, `SUBSET`, `IN_ELIM_THM`, `FUN_EQ_THM`, and `SURJECTIVE_RIGHT_INVERSE`, which are crucial for manipulating cardinality relations, subset inclusions, and function properties.

### Mathematical insight
The Cantor theorem is fundamental in set theory, demonstrating that any set $A$ has a proper subset with the same cardinality as $A$. This theorem is essential for understanding the concept of infinite sets and their properties. The formalization provided here captures this idea in the context of HOL Light, relying on precise definitions of cardinality comparison and subset relations.

### Dependencies
#### Theorems
* `lt_c`
* `le_c`
* `FUN_EQ_THM`
* `IN_ELIM_THM`
* `SUBSET`
* `IN`
* `SURJECTIVE_RIGHT_INVERSE`
* `NOT_EXISTS_THM`
#### Definitions
* `(=):A->A->bool`
* `GEN_TAC`
* `CONJ_TAC`
* `REWRITE_TAC`
* `EXISTS_TAC`
* `DISCH_THEN`
* `MP_TAC`
* `X_GEN_TAC` 

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to the handling of cardinality comparisons, subset relations, and the use of tactics like `GEN_TAC`, `CONJ_TAC`, and `REWRITE_TAC`, as these may have different equivalents or requirements in the target system. Additionally, the porting process should ensure that the formalization maintains the same level of rigor and precision as the original HOL Light version.

---

## CANTOR_THM_INJ'

### Name of formal statement
CANTOR_THM_INJ'

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_THM_INJ' = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  STRIP_TAC THEN
  ABBREV_TAC `(g:A->A->bool) = \a. { b | !s. f(s) = a ==> b IN s}` THEN
  MP_TAC(ISPEC `g:A->A->bool`
   (REWRITE_RULE[NOT_EXISTS_THM] CANTOR_THM_SURJ)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
It is not the case that there exists a function `f` from sets of elements of type `A` to elements of type `A` such that for all `x` and `y` of type `A`, if `f(x)` equals `f(y)`, then `x` equals `y`.

### Informal sketch
* The proof starts by assuming the existence of a function `f` that maps sets of `A` to `A` and satisfies the condition that if `f(x)` equals `f(y)`, then `x` equals `y`.
* An auxiliary function `g` is defined, which maps elements `a` of `A` to sets of `A`, such that for any `b` in `A`, `b` is in the set `g(a)` if and only if for all sets `s` of `A`, if `f(s)` equals `a`, then `b` is in `s`.
* The `CANTOR_THM_SURJ` theorem is applied to `g`, which involves rewriting it using `NOT_EXISTS_THM` to handle the negation of existential quantification.
* The first assumption is then substituted into the proof using `SUBST_ALL_TAC`, and the symmetry of equality is applied.
* The proof then uses `ASM_REWRITE_TAC` to apply `EXTENSION` and `IN_ELIM_THM` to simplify the statement, and finally applies `ASM_MESON_TAC` to conclude the proof.
* Key steps involve using the `STRIP_TAC` to remove the outermost universal quantification, and using `ABBREV_TAC` to introduce the auxiliary function `g`.

### Mathematical insight
This theorem is a version of Cantor's theorem, which states that there is no surjection from a set to its power set. The specific formulation here involves the non-existence of an injective function from the power set of `A` to `A`, highlighting the fundamental difference in size between a set and its power set. This theorem is crucial in set theory, demonstrating the strict hierarchy of cardinalities in the universe of sets.

### Dependencies
* Theorems:
  * `CANTOR_THM_SURJ`
  * `NOT_EXISTS_THM`
  * `EXTENSION`
  * `IN_ELIM_THM`
* Definitions:
  None

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles existential quantification, especially in the context of negation (`NOT_EXISTS_THM`). Additionally, the introduction of the auxiliary function `g` and its properties might require careful handling of lambda abstraction and set comprehension, depending on the target system's syntax and semantics.

---

## CANTOR_LAWVERE

### Name of formal statement
CANTOR_LAWVERE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_LAWVERE = prove
 (`!h:A->(A->B). 
        (!f:A->B. ?x:A. h(x) = f) ==> !n:B->B. ?x. n(x) = x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g:A->B = \a. (n:B->B) (h a a)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN
  ASM_MESON_TAC[])
```

### Informal statement
For all functions `h` from `A` to the set of functions from `A` to `B`, if for every function `f` from `A` to `B` there exists an `x` in `A` such that `h(x)` equals `f`, then for all functions `n` from `B` to `B`, there exists an `x` in `B` such that `n(x)` equals `x`.

### Informal sketch
* The proof begins by assuming the premise that for all functions `f` from `A` to `B`, there exists an `x` in `A` such that `h(x)` equals `f`. This assumption is crucial for constructing a specific function that will lead to the conclusion.
* An abbreviation `g` is introduced, defined as `g(a) = n(h(a) a)`, which involves applying `n` to the result of `h(a)` applied to `a`. This step is key to linking the properties of `h` and `n`.
* The proof then applies `REWRITE_RULE` with `FUN_EQ_THM` to equate functions based on their pointwise equality, which is essential for handling function equality in the context of `h` and `n`.
* Finally, `ASM_MESON_TAC` is used to deduce the existence of an `x` in `B` such that `n(x)` equals `x`, leveraging the properties established through the previous steps.

### Mathematical insight
This theorem is related to Cantor's theorem and involves a diagonalization argument. It essentially states that if there's a way to enumerate all functions from `A` to `B` using a function `h` from `A` to the set of such functions, then there cannot be a surjection from `B` to `B` that is also a fixed-point operator, unless `B` has a fixed point under some function `n`. The theorem has implications for the cardinality of sets and the properties of functions between them.

### Dependencies
* `FUN_EQ_THM`: A theorem stating that two functions are equal if and only if they are equal pointwise.
* `REPEAT STRIP_TAC`, `ABBREV_TAC`, `RULE_ASSUM_TAC`, `ASM_MESON_TAC`: Tactics used in the proof for manipulating assumptions, defining abbreviations, and applying rules to deduce the conclusion.

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how functions and their equalities are handled, as well as how tactical proofs are structured. The use of `REWRITE_RULE` with `FUN_EQ_THM` and the application of `ASM_MESON_TAC` may require careful consideration of the target system's capabilities for equational reasoning and automated theorem proving. Additionally, the representation of functions from `A` to `B` and the set of such functions may vary between systems, affecting the translation of `h` and the overall structure of the proof.

---

## CANTOR

### Name of formal statement
CANTOR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR = prove
 (`!f:A->(A->bool). ~(!s. ?x. f x = s)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CANTOR_LAWVERE) THEN
  DISCH_THEN(MP_TAC o SPEC `(~)`) THEN MESON_TAC[]);;
```

### Informal statement
For all functions `f` from type `A` to functions from `A` to boolean, it is not the case that for all sets `s`, there exists an `x` such that `f x` equals `s`.

### Informal sketch
* The proof starts by generalizing over the function `f` using `GEN_TAC`.
* It then applies `CANTOR_LAWVERE` to discharge the assumption, using `MATCH_MP` to match the pattern and `DISCH_THEN` to handle the result.
* The `SPEC `(~)`` tactic is used to instantiate the variable with the negation operator, which is crucial for deriving the contradiction.
* Finally, `MESON_TAC` is applied to simplify and derive the conclusion, leveraging the previous steps to establish the theorem.

### Mathematical insight
The `CANTOR` theorem is related to Cantor's theorem, which states that there is no surjection from a set to its power set. This theorem is important in set theory and has implications for the cardinality of sets. The formal item `CANTOR` likely captures a specific aspect of this idea, using a function `f` from `A` to `A -> bool` (which can be thought of as a representation of subsets of `A`) to demonstrate a fundamental limit on the ability of such functions to "cover" all possible subsets.

### Dependencies
* `CANTOR_LAWVERE` 

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of the `GEN_TAC` and `DISCH_THEN` tactics, as well as the application of `MATCH_MP` with `CANTOR_LAWVERE`. The use of `SPEC` with the negation operator `(~)` is also crucial and may require careful handling in the target system. Additionally, the automation provided by `MESON_TAC` may need to be replicated or mimicked using the target system's tactics or proof search mechanisms.

---

## CANTOR_TAYLOR

### Name of formal statement
CANTOR_TAYLOR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_TAYLOR = prove
 (`!f:(A->bool)->A. ~(!x y. f(x) = f(y) ==> x = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\a:A.  { b:A | !s. f(s) = a ==> b IN s}`
   (REWRITE_RULE[NOT_EXISTS_THM] CANTOR)) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
For all functions `f` from `A` to `bool`, it is not the case that for all `x` and `y` in `A`, if `f(x)` equals `f(y)`, then `x` equals `y`.

### Informal sketch
* The proof starts by assuming a function `f` from `A` to `bool` and aims to show that `f` cannot be injective.
* It then defines a set using the `ISPEC` tactic, which is a specialization of a theorem to a specific term, here `\a:A.  { b:A | !s. f(s) = a ==> b IN s}`.
* The `REWRITE_RULE` with `NOT_EXISTS_THM` is applied to transform the statement, likely to move from an existential to a universal quantification.
* The `REWRITE_TAC` with `EXTENSION` and `IN_ELIM_THM` theorems is used to further simplify the statement, probably to handle set equality and membership.
* Finally, `ASM_MESON_TAC` is applied to conclude the proof, which is a tactic that uses meson (a theorem prover) to automatically prove the goal.

### Mathematical insight
This theorem is related to Cantor's theorem, which states that there is no surjection from a set to its power set. The intuition here is to show that for any function `f` from `A` to `bool` (which can be seen as a subset of the power set of `A`), there cannot exist a unique element in `A` that maps to each element in `bool` under `f`, implying that `f` cannot be injective if it's surjective.

### Dependencies
* Theorems:
  * `CANTOR`
  * `NOT_EXISTS_THM`
  * `EXTENSION`
  * `IN_ELIM_THM`
* Definitions:
  None explicitly mentioned, but the `ISPEC` and `REWRITE_RULE` tactics imply reliance on specific definitions and rules for function types, set operations, and possibly type `A` and `bool`.

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how functions from `A` to `bool` are represented and how set operations are handled. The `ISPEC` and `REWRITE_RULE` tactics may have direct counterparts, but the automation level and the specific rules applied (like `NOT_EXISTS_THM`, `EXTENSION`, and `IN_ELIM_THM`) might require adjustments to match the target system's libraries and proof strategies. Additionally, the use of `ASM_MESON_TAC` suggests that a degree of automation is expected; the porter should be prepared to use similar automation features in the target system or to manually fill in the proof steps if such automation is not available.

---

## SURJECTIVE_COMPOSE

### Name of formal statement
SURJECTIVE_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SURJECTIVE_COMPOSE = prove
 (`(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)`,
  MESON_TAC[o_THM])
```

### Informal statement
For all functions `f` and `g`, if for every `y` there exists an `x` such that `f(x) = y`, and for every `z` there exists a `y` such that `g(y) = z`, then for every `z` there exists an `x` such that `(g o f)(x) = z`. This statement asserts the surjectivity of the composition of two surjective functions.

### Informal sketch
* The proof starts by assuming the surjectivity of `f` and `g`, which means that every element in the codomain of `f` is the image of some element in the domain of `f`, and every element in the codomain of `g` is the image of some element in the domain of `g`.
* The goal is to show that the composition `g o f` is also surjective, meaning every element in the codomain of `g o f` is the image of some element in the domain of `f`.
* The `MESON_TAC` tactic is used to prove this implication, which likely involves applying basic properties of function composition and the definition of surjectivity.
* The key logical stage is recognizing that if `f` maps every element in its domain to the domain of `g`, and `g` maps every element in its domain onto its codomain, then their composition `g o f` will map every element in the domain of `f` onto the codomain of `g`.

### Mathematical insight
This theorem is important because it shows that the composition of surjective functions is also surjective. This property is crucial in various areas of mathematics, such as category theory, where it is used to define and study the properties of epimorphisms (surjective morphisms). The intuition behind this statement is straightforward: if `f` and `g` are both surjective, then every possible output of `g` can be reached from some input of `f` through the composition `g o f`.

### Dependencies
* `o_THM` (the theorem about function composition)

### Porting notes
When porting this theorem to another proof assistant, one should pay attention to how function composition and surjectivity are defined and handled. Specifically, the port should ensure that the definitions of surjectivity for `f` and `g`, and the definition of function composition, align with those in the target system. Additionally, the equivalent of `MESON_TAC` or a similar tactic for proving implications might be needed, depending on the proof assistant's automation capabilities and tactic language.

---

## INJECTIVE_SURJECTIVE_PREIMAGE

### Name of formal statement
INJECTIVE_SURJECTIVE_PREIMAGE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INJECTIVE_SURJECTIVE_PREIMAGE = prove
 (`!f:A->B. (!x y. f(x) = f(y) ==> x = y) ==> !t. ?s. {x | f(x) IN s} = t`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:A->B) t` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[])
```

### Informal statement
For all functions `f` from set `A` to set `B`, if `f` is injective (i.e., for all `x` and `y` in `A`, if `f(x)` equals `f(y)`, then `x` equals `y`), then for all subsets `t` of `B`, there exists a subset `s` of `A` such that the set of all `x` in `A` for which `f(x)` is in `t` equals `t` intersected with the image of `f`.

### Informal sketch
* The theorem starts by assuming `f` is injective, which implies that if `f(x) = f(y)`, then `x = y`.
* The goal is to show that for any subset `t` of `B`, there exists a subset `s` of `A` such that the preimage of `t` under `f` equals `t` intersected with the image of `f`.
* The proof involves using the `EXISTS_TAC` tactic to propose `IMAGE (f:A->B) t` as a candidate for `s`, and then applying `REWRITE_TAC` with `EXTENSION`, `IN_ELIM_THM`, and `IN_IMAGE` to establish the equality.
* The `ASM_MESON_TAC` is used to automate the proof of the resulting goals.

### Mathematical insight
This theorem is important because it relates the injectivity of a function to the existence of preimages for subsets of its codomain. It provides a way to "pull back" subsets of the codomain to the domain, which is crucial in various mathematical constructions, especially in topology and category theory.

### Dependencies
* `EXTENSION`
* `IN_ELIM_THM`
* `IN_IMAGE`

### Porting notes
When porting this theorem to another proof assistant, pay attention to how injectivity is defined and used, as well as how preimages and images are constructed. The `EXISTS_TAC` and `REWRITE_TAC` tactics may have direct counterparts, but `ASM_MESON_TAC` might require manual proof or the use of a different automation tactic. Additionally, the handling of set comprehensions and subset equalities may vary between systems.

---

## CANTOR_JOHNSTONE

### Name of formal statement
CANTOR_JOHNSTONE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CANTOR_JOHNSTONE = prove
 (`!i:B->S f:B->S->bool.
        ~((!x y. i(x) = i(y) ==> x = y) /\ (!s. ?z. f(z) = s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `(IMAGE (f:B->S->bool)) o (\s:S->bool. {x | i(x) IN s})`
    (REWRITE_RULE[NOT_EXISTS_THM] CANTOR)) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SURJECTIVE_COMPOSE THEN
  ASM_REWRITE_TAC[SURJECTIVE_IMAGE] THEN
  MATCH_MP_TAC INJECTIVE_SURJECTIVE_PREIMAGE THEN
  ASM_REWRITE_TAC[])
```

### Informal statement
For all functions `i` from type `B` to type `S` and for all functions `f` from `B` to `S` to `bool`, it is not the case that both of the following conditions hold: (1) for all `x` and `y` of type `B`, if `i(x)` equals `i(y)`, then `x` equals `y`, and (2) for all subsets `s` of `S`, there exists an element `z` of `B` such that `f(z)` equals `s`.

### Informal sketch
* The proof begins by assuming the negation of the statement to be proved and then applying `STRIP_TAC` to simplify the assumption.
* It then uses `MP_TAC` with a specific instantiation of the `CANTOR` theorem, rewritten using `NOT_EXISTS_THM`, to derive a contradiction.
* The proof continues by applying `REWRITE_TAC` and `MATCH_MP_TAC` with `SURJECTIVE_COMPOSE` to establish a relationship between the surjectivity of composed functions.
* Further steps involve applying `ASM_REWRITE_TAC` with `SURJECTIVE_IMAGE` and `MATCH_MP_TAC` with `INJECTIVE_SURJECTIVE_PREIMAGE` to derive the final contradiction, showing that the initial assumption is false.

### Mathematical insight
This theorem is related to the Cantor's theorem, which states that there is no surjection from a set to its power set. The `CANTOR_JOHNSTONE` theorem seems to generalize this idea, considering functions `i` and `f` with specific properties and showing that these properties lead to a contradiction, thus establishing a fundamental limit on the existence of certain kinds of mappings between sets and their power sets.

### Dependencies
#### Theorems
* `CANTOR`
* `SURJECTIVE_COMPOSE`
* `INJECTIVE_SURJECTIVE_PREIMAGE`
* `NOT_EXISTS_THM`
#### Definitions
* `SURJECTIVE_IMAGE` 
#### Tactics
* `REPEAT`
* `STRIP_TAC`
* `MP_TAC`
* `REWRITE_TAC`
* `MATCH_MP_TAC`
* `ASM_REWRITE_TAC`

---

