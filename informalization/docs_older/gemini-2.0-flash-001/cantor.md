# cantor.ml

## Overview

Number of statements: 10

`cantor.ml` formalizes Cantor's theorem within HOL Light. It provides an ad hoc version of the theorem specifically for the whole type. The file contains definitions and proofs related to this particular formalization of Cantor's theorem.


## CANTOR_THM_INJ

### Name of formal statement
CANTOR_THM_INJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CANTOR_THM_INJ = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:(A->bool)->A`; `g:A->(A->bool)`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;
```
### Informal statement
It is not the case that there exists a function `f` from sets (i.e. functions from a type `A` to booleans) to elements of `A`, such that `f` is injective (i.e., for all sets `x` and `y`, if `f(x) = f(y)` then `x = y`).

### Informal sketch
The proof proceeds as follows:
- We start by negating the statement: assume that there *does* exist an injective function `f:(A->bool)->A`.
- Introduce a function `g:A->(A->bool)` and then specialize `f` to the set defined by `\x:A. ~(g x x)`.
- Use the assumed injectivity of `f` to derive a contradiction using `MESON_TAC`.

### Mathematical insight
This is a version of Cantor's theorem, which states that there is no injection from the power set of a type `A` into `A`. This specific version of Cantor's theorem is specialized to the case where the power set is represented as the type `A->bool`, which is isomorphic to the power set of A in HOL Light. The result demonstrates that the cardinality of the power set of `A` is strictly greater than the cardinality of `A`.

### Dependencies
- Theorems: `INJECTIVE_LEFT_INVERSE`, `NOT_EXISTS_THM`


---

## CANTOR_THM_SURJ

### Name of formal statement
CANTOR_THM_SURJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CANTOR_THM_SURJ = prove
 (`~(?f:A->(A->bool). !s. ?x. f x = s)`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:A->(A->bool)`; `f:(A->bool)->A`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;
```

### Informal statement
It is not the case that there exists a function `f` from `A` to functions from `A` to booleans such that for all sets `s` of type `A -> bool`, there exists an element `x` in `A` such that `f x = s`. In other words, there is no surjection from `A` onto the set of functions from `A` to booleans.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting using `SURJECTIVE_RIGHT_INVERSE` and `NOT_EXISTS_THM`.
- Introduce a function `g` of type `A -> (A -> bool)` and a function `f` of type `(A -> bool) -> A` using universal generalization.
- Assume that for all `s:A -> bool`, there exists `x:A` such that `f x = s`.
- Assume also the hypothetical surjection `f: A -> (A->bool)`
- Instantiate `s` with a "diagonal" set defined by `\x:A . ~(g x x)`
- Apply a MESON_TAC to complete the proof. This step likely involves deriving a contradiction by considering the value of the function applied to itself, which is a common technique in diagonalization arguments.

### Mathematical insight
This theorem states Cantor's theorem, which proves that there is no surjection from a set `A` to its power set (represented here as functions from `A` to booleans). This means that the power set of any set `A` has a strictly greater cardinality than `A` itself. The proof generally involves a diagonalization argument.

### Dependencies
- `SURJECTIVE_RIGHT_INVERSE`
- `NOT_EXISTS_THM`

### Porting notes (optional)
The `MESON_TAC` is a powerful automated tactic in HOL Light. When porting this theorem, it may be necessary to manually reconstruct the derivation that `MESON_TAC` finds automatically. The key is the diagonalization argument: if `f` is assumed to be surjective, then for the set `s = {x | x not in f(x)}`, there must exist an element `a` such that `f(a) = s`. But then `a in f(a)` if and only if `a in s`, which is if and only if `a not in f(a)`, a contradiction.


---

## CANTOR

### Name of formal statement
CANTOR

### Type of the formal statement
theorem

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
    REWRITE_TAC[SUBSET; IN; FUN_EQ_THM] THEN MESON_TAC[]]);;
```

### Informal statement
For any set `s` of type `A -> bool`, `s` has strictly smaller cardinality than its power set `{t | t SUBSET s}`.

### Informal sketch
The proof demonstrates that for any set `s`, the cardinality of `s` is strictly less than the cardinality of its powerset. This is proven by showing that there exists an injection from `s` to its power set, but there is no surjection from `s` onto its power set.

- An injection is constructed by mapping each element `x` in `s` to the singleton set `{x}`.
- It is proven that any function `g` from `s` to its power set cannot be surjective. This employs a diagonalization argument. Assuming that `g` is a surjection from A to `A -> bool`, we construct the set `{x:A | s(x) /\ ~(g x x)}`. This set is necessarily in the powerset of `s`. By the assumption that 'g' is surjective, there must be an element 'z' such that `g z = {x:A | s(x) /\ ~(g x x)}`. However, `z` is an element of the set `g z` iff `s(z) /\ ~(g z z)`, i.e., `z IN (g z) = s(z) /\ ~(g z z)`. Substituting `g z` with  `{x:A | s(x) /\ ~(g x x)}` leads to a contradiction.

### Mathematical insight
This theorem expresses Cantor's theorem, which states that the power set of any set has a strictly greater cardinality than the set itself. This theorem has fundamental implications in set theory and cardinality theory. It implies that there is no largest set, and that the cardinality of the power set of a set is strictly greater than the cardinality of the original set.

### Dependencies
- `lt_c`
- `le_c`
- `FUN_EQ_THM`
- `IN_ELIM_THM`
- `SUBSET`
- `IN`
- `LE_C`
- `SURJECTIVE_RIGHT_INVERSE`
- `NOT_EXISTS_THM`


---

## CANTOR_THM_INJ'

### Name of formal statement
CANTOR_THM_INJ'

### Type of the formal statement
theorem

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
It is not the case that there exists a function `f` from sets of elements of type `A` to elements of type `A` such that `f` is injective. That is, there is no `f` such that for all sets `x` and `y`, if `f(x) = f(y)` then `x = y`.

### Informal sketch
The proof proceeds as follows:
- Assume, for the sake of contradiction, that there exists an injective function `f:(A->bool)->A`.
- Define a function `g:A->A->bool` such that `g a b` is true if and only if `b` is in the set `{ b | !s. f(s) = a ==> b IN s }`. In other words, `g a b` is true if and only if `b` is in some set `s` such that `f(s) = a`.
- Instantiate `CANTOR_THM_SURJ` with `g`. `CANTOR_THM_SURJ` states that there exists no surjective function from `A` to `A->bool`. The function `g` in this case takes the form `{b | ~(g b b)}`, or in our instantiation `{b | ~(!s. f(s) = b ==> b IN s)}`.
- Using substitution and rewriting based on `EXTENSION` and `IN_ELIM_THM`, use `ASM_MESON_TAC` to derive a contradiction. The contradiction arises from the assumption that `f` is injective when applied to the set defined using `g`.

### Mathematical insight
This theorem is a variant of Cantor's theorem, which demonstrates that the power set of a set (the set of all subsets) has a greater cardinality than the set itself. This version focuses on the absence of an injective function from the power set to the set, while the standard version proves the absence of a surjective function in the opposite direction. It utilizes a similar diagonal argument to derive a contradiction.

### Dependencies
- `EXTENSION`
- `IN_ELIM_THM`
- `NOT_EXISTS_THM`
- `CANTOR_THM_SURJ`


---

## CANTOR_LAWVERE

### Name of formal statement
CANTOR_LAWVERE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CANTOR_LAWVERE = prove
 (`!h:A->(A->B).
        (!f:A->B. ?x:A. h(x) = f) ==> !n:B->B. ?x. n(x) = x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g:A->B = \a. (n:B->B) (h a a)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN
  ASM_MESON_TAC[]);;
```
### Informal statement
For any `h` of type `A` to `A` to `B`, if for every `f` of type `A` to `B` there exists an `x` of type `A` such that `h(x)` equals `f`, then for every `n` of type `B` to `B` there exists an `x` of type `B` such that `n(x)` equals `x`.

### Informal sketch
The basic idea is to show that if every function from A to B is in the image of h: A -> (A -> B), then every function from B to B has a fixed point.
- Assume `forall f: A -> B. exists x: A. h(x) = f`
- Define `g: A -> B` as `\a. n (h a a)`
- From the assumption, there exists `x` such that `h(x) = g`
- Substitute definition of `g` we have `h(x) = \a. n (h a a)`
- Apply this equality to x: `h x x = n (h x x)` so `h x x` is fixed point of n

### Mathematical insight
This theorem provides a generalized form of Cantor's theorem using Lawvere's fixed point argument. It demonstrates that if a function `h` from `A` to functions from `A` to `B` is surjective, then any function from `B` to `B` has a fixed point. This result is significant in category theory and provides a connection between set theory and fixed-point theorems.

### Dependencies
- `FUN_EQ_THM`

### Porting notes (optional)
- The `ABBREV_TAC` is used for introducing local definitions for readability. This may need to be adapted based on the target proof assistant's mechanisms for local definitions.
- `ASM_MESON_TAC` performs automated reasoning. The specific details of the automation may need to be recreated using tactics or automated reasoners available in the target proof assistant.


---

## CANTOR

### Name of formal statement
CANTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CANTOR = prove
 (`!f:A->(A->bool). ~(!s. ?x. f x = s)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CANTOR_LAWVERE) THEN
  DISCH_THEN(MP_TAC o SPEC `(~)`) THEN MESON_TAC[]);;
```

### Informal statement
For any function `f` from a type `A` to functions from `A` to booleans, it is not the case that for all sets `s` there exists an `x` such that `f x` is equal to `s`.

### Informal sketch
The proof proceeds as follows:
- Assume, for the sake of contradiction, that there exists a function `f` from A to (A -> bool) such that for all sets `s` (of type `A -> bool`), there exists an element `x` of type `A` such that `f x = s`.
- Apply `CANTOR_LAWVERE`. This likely introduces some form of Russell's paradox, which contradicts the universal quantifier, `!s. ?x. f x = s`
- Specialize the universally quantified function resulting from the previous step with `~` (negation).
- Use `MESON_TAC` (a higher-order resolution prover) to derive a contradiction and discharge the initial assumption.

### Mathematical insight
This theorem expresses Cantor's theorem in a general form. It states that there is no surjection from a set `A` to its power set (represented as functions from `A` to `bool`). This is a generalization of the traditional Cantor's theorem, which says that the cardinality of a set is strictly less than the cardinality of its power set.  It is related to Lawvere's fixed point theorem, which provides an abstract condition for proving Cantor's theorem. `CANTOR_LAWVERE` likely embodies the core logical argument based on Lawvere's theorem.

### Dependencies
- `CANTOR_LAWVERE`


---

## CANTOR_TAYLOR

### Name of formal statement
CANTOR_TAYLOR

### Type of the formal statement
theorem

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
For any function `f` from type `A` to boolean, it is not the case that `f` is injective (i.e., it is not the case that for all `x` and `y`, if `f(x)` equals `f(y)`, then `x` equals `y`).

### Informal sketch
The proof proceeds by contradiction, using Cantor's theorem.

- Assume that there exists a function `f` from `A` to `bool` that is injective.
- Instantiate Cantor's theorem (`CANTOR`) with the set `{ b:A | !s. f(s) = a ==> b IN s}`, where `a` is a free variable of type `A`. The instantiated version of `CANTOR` states that `!a. ~(!s. (!t. t IN s ==> f(t) = a) ==> (f(s) = a))`. Rewriting using `NOT_EXISTS_THM` states that `!a. (?s. (!t. t IN s ==> f(t) = a) /\ (f(s) ~= a))`.
- Rewrite using `EXTENSION` and `IN_ELIM_THM` to transform set membership into equality.
- Apply `ASM_MESON_TAC[]` to derive a contradiction, thereby discharging the initial assumption.

### Mathematical insight
This theorem demonstrates that the power set of any set `A` has a strictly greater cardinality than `A` itself, when the power set is viewed as the set of boolean functions from `A`. It shows that no function from `A` to the power set of `A` can be surjective; in particular, there's no injection from `A` to the power set.

### Dependencies
- `CANTOR`
- `EXTENSION`
- `IN_ELIM_THM`
- `NOT_EXISTS_THM`


---

## SURJECTIVE_COMPOSE

### Name of formal statement
SURJECTIVE_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SURJECTIVE_COMPOSE = prove
 (`(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)`,
  MESON_TAC[o_THM]);;
```
### Informal statement
If the function `f` is surjective, meaning that for every `y` there exists an `x` such that `f(x) = y`, and the function `g` is surjective, meaning that for every `z` there exists a `y` such that `g(y) = z`, then the composition of `g` and `f` (denoted `g o f`) is surjective, meaning that for every `z` there exists an `x` such that `(g o f)(x) = z`.

### Informal sketch
The proof demonstrates that the composition of two surjective functions is surjective.
- Assume that `f` and `g` are surjective. That is, assume `!y. ?x. f(x) = y` and `!z. ?y. g(y) = z`.
- To prove that `g o f` is surjective, we must show `!z. ?x. (g o f) x = z`.
- Given `z`, because `g` is surjective, there exists a `y` such that `g(y) = z`.
- Because `f` is surjective, there exists an `x` such that `f(x) = y`.
- Therefore, `(g o f)(x) = g(f(x)) = g(y) = z`.
- Thus, for every `z`, there exists an `x` such that `(g o f)(x) = z`, hence `g o f` is surjective.
- The tactic `MESON_TAC[o_THM]` automatically discharges this proof using first-order logic reasoning and uses a theorem related to function composition.

### Mathematical insight
This theorem illustrates a fundamental property of surjective functions: the composition of surjective functions preserves surjectivity. This is a basic result in set theory and function theory, often used when reasoning about the properties of functions in various mathematical contexts.

### Dependencies
- `o_THM`


---

## INJECTIVE_SURJECTIVE_PREIMAGE

### Name of formal statement
INJECTIVE_SURJECTIVE_PREIMAGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INJECTIVE_SURJECTIVE_PREIMAGE = prove
 (`!f:A->B. (!x y. f(x) = f(y) ==> x = y) ==> !t. ?s. {x | f(x) IN s} = t`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:A->B) t` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[]);;
```
### Informal statement
For any function `f` from a set `A` to a set `B`, if `f` is injective (i.e., for all `x` and `y`, `f(x) = f(y)` implies `x = y`), then for any set `t`, there exists a set `s` such that the set of all `x` where `f(x)` is in `s` is equal to `t`.

### Informal sketch
The proof proceeds as follows:
- Assume that `f` is injective.
- Given a set `t`, we need to show the existence of a set `s` such that `{x | f(x) IN s} = t`.
- Choose `s` to be the image of `t` under `f` (i.e., `IMAGE (f:A->B) t`).
- Rewrite using the extensionality axiom `EXTENSION`, the definition of `IN_ELIM_THM` (membership), and the definition of `IN_IMAGE` to prove that `{x | f(x) IN IMAGE f t} = t`.
- Use `ASM_MESON_TAC[]` to discharge any remaining assumptions.

### Mathematical insight
This theorem demonstrates how injectivity of a function `f` allows constructing a suitable set `s` such that pre-image of `s` under `f` equals a given set `t`. This highlights a connection between injectivity and the ability to "reverse" the action of the function to some extent.

### Dependencies
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `IN_IMAGE`


---

## CANTOR_JOHNSTONE

### Name of formal statement
CANTOR_JOHNSTONE

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[]);;
```
### Informal statement
For any types `B` and `S`, and any functions `i: B -> S` and `f: B -> (S -> bool)`, it is not the case that `i` is injective and `f` is surjective.
More formally, it is not the case that the following two conditions hold simultaneously:
1.  For all `x` and `y` in `B`, if `i(x) = i(y)`, then `x = y`.
2.  For all `s` of type `S -> bool`, there exists a `z` in `B` such that `f(z) = s`.

### Informal sketch
The proof proceeds as follows:
- Assume (for the sake of contradiction using `REPEAT STRIP_TAC`) that `i` is injective and `f` is surjective.
- Apply the Cantor's theorem using `MP_TAC(ISPEC ... (REWRITE_RULE[NOT_EXISTS_THM] CANTOR))`. Here Cantor's theorem states that for any set `A`, there is no surjection from `A` to its powerset, i.e., `!(f:A->A->bool). ~(!s. ?x. f x = s)`. We specialize `A` to the image of `f` composed with a function mapping each element of `S` to its preimage under `i` represented by `(IMAGE (f:B->S->bool)) o (\s:S->bool. {x | i(x) IN s})`.
- Rewrite using `REWRITE_TAC[]`.
- Use `MATCH_MP_TAC SURJECTIVE_COMPOSE` to show that the composition of surjective functions is surjective.
- Then, use `ASM_REWRITE_TAC[SURJECTIVE_IMAGE]` to rewrite using the fact that the image of a function is surjective onto its image.
- Finally, apply `MATCH_MP_TAC INJECTIVE_SURJECTIVE_PREIMAGE` and `ASM_REWRITE_TAC[]` to get a contradiction.

### Mathematical insight
This theorem combines the result of Cantor's theorem (no set admits a surjection onto its power set) with properties of injections and surjections to derive a contradiction. It highlights that the combination of an injection `i` and a surjection `f` with the given types leads to logical inconsistency.

### Dependencies
- `NOT_EXISTS_THM`
- `CANTOR`
- `SURJECTIVE_COMPOSE`
- `SURJECTIVE_IMAGE`
- `INJECTIVE_SURJECTIVE_PREIMAGE`


---

