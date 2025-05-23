# cantor.ml

## Overview

Number of statements: 10

This file formalizes Cantor's theorem in HOL Light, proving that for any set, its power set has strictly greater cardinality. The implementation appears to be an ad hoc version that works with whole types rather than arbitrary sets. No external imports are required, suggesting this is a self-contained development using only core HOL Light functionality.

## CANTOR_THM_INJ

### CANTOR_THM_INJ
- CANTOR_THM_INJ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CANTOR_THM_INJ = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:(A->bool)->A`; `g:A->(A->bool)`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;
```

### Informal statement
This theorem states that there is no injective function from the power set of a type $A$ to $A$ itself. Formally:

$$\neg(\exists f : \mathcal{P}(A) \to A. \forall x, y. f(x) = f(y) \Rightarrow x = y)$$

In HOL Light, the power set of type $A$ is represented as the function type $(A \to \text{bool})$, which corresponds to characteristic functions of subsets of $A$.

### Informal proof
The proof follows Cantor's diagonal argument:

- We start by rewriting using the characterization of injectivity in terms of left inverses (`INJECTIVE_LEFT_INVERSE`) and then transforming the negated existential statement.
- We introduce universal quantifiers for both $f: \mathcal{P}(A) \to A$ and its potential left inverse $g: A \to \mathcal{P}(A)$.
- We construct a diagonal set $D = \{x \in A : x \notin g(x)\}$ using the lambda term $\lambda x:A. \neg(g(x)(x))$.
- The contradiction follows by considering what happens when we apply $f$ to this diagonal set $D$.
  - If $f(D) = a$ for some $a \in A$, then:
  - If $a \in D$, then by definition of $D$, $a \notin g(a)$.
  - But since $g$ is a left inverse of $f$, we have $g(a) = g(f(D)) = D$.
  - This leads to: $a \in D$ if and only if $a \notin g(a) = D$, which is a contradiction.
- The automated reasoner `MESON_TAC` completes the proof by finding this contradiction.

### Mathematical insight
This is Cantor's theorem, a fundamental result in set theory that demonstrates the hierarchy of infinite cardinalities. It shows that for any set, its power set has strictly greater cardinality than the set itself.

The theorem is proven by a diagonal argument, which is one of the most powerful techniques in set theory and logic. Cantor originally used this argument to prove that the real numbers are uncountable.

In the context of type theory and proof assistants, this theorem demonstrates that there are meaningful "sizes" of types even in a simple type theory where all types are inhabited. Although HOL Light doesn't have a native notion of cardinality for types, this theorem captures the essential insight about the relationship between a type and its power type.

### Dependencies
- `INJECTIVE_LEFT_INVERSE`: Characterizes injective functions as those having left inverses
- `NOT_EXISTS_THM`: Transforms negated existential statements into universal negations

### Porting notes
When porting this theorem:
- Ensure your target system can express the power set operation (in HOL Light this is done via the function type `A -> bool`).
- Be aware that different proof assistants have different automation capabilities - the `MESON_TAC` step may need to be expanded into more explicit reasoning in systems with less powerful automation.
- The diagonal construction is the key insight, and should translate well across systems.

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
For any non-empty type $A$, there does not exist a surjective function $f: A \rightarrow (A \rightarrow \text{bool})$.

In other words, there is no function $f$ from $A$ to the powerset of $A$ such that every subset of $A$ is the image of some element of $A$ under $f$.

### Informal proof
The proof uses Cantor's diagonal argument:

1. We begin by rewriting the statement using the right inverse characterization of surjectivity (`SURJECTIVE_RIGHT_INVERSE`) and manipulating the negations (`NOT_EXISTS_THM`).

2. This transforms our goal to show that for any functions $g: A \rightarrow (A \rightarrow \text{bool})$ and $f: (A \rightarrow \text{bool}) \rightarrow A$ (where $f$ would be the alleged right inverse of $g$), there exists a contradiction.

3. We construct a diagonal set $D = \{x \in A : x \not\in g(x)\}$, represented formally as $\lambda x:A. \neg(g(x)(x))$.

4. The proof then uses this diagonal set to derive a contradiction:
   - If $f$ were a right inverse of $g$, then for any set $s$, including our diagonal set $D$, we would have $g(f(s)) = s$.
   - For the element $a = f(D)$, we get a contradiction:
     - If $a \in D$, then by definition of $D$, $a \not\in g(a)$. But $g(a) = g(f(D)) = D$, so $a \not\in D$.
     - If $a \not\in D$, then $a \not\in g(f(D)) = D$, which means $a \in D$ by definition of $D$.

5. This contradiction completes the proof.

### Mathematical insight
This theorem is a formalization of Cantor's famous diagonal argument, which establishes that there is no surjection from a set to its power set. The result is foundational in set theory and has profound implications:

1. It demonstrates that the power set of $A$ always has strictly larger cardinality than $A$ itself.
2. This leads directly to the existence of an infinite hierarchy of increasingly larger infinite sets, rather than just one notion of "infinity."
3. In type theory, it shows that the type of functions from $A$ to bool (representing the power set of $A$) is in a sense "larger" than $A$.

The diagonal construction at the heart of the proof has influenced many areas of mathematics and computer science, including the proof of the undecidability of the halting problem.

### Dependencies
- `SURJECTIVE_RIGHT_INVERSE`: Characterizes surjective functions as having right inverses
- `NOT_EXISTS_THM`: Theorem for manipulating negated existential quantifiers
- The proof also relies on MESON automated reasoning tactics

### Porting notes
When porting to other systems:
- Be careful with the encoding of the powerset. In HOL Light, it's represented as functions to bool, but other systems might have native powerset types or different encodings.
- The diagonal construction is key - ensure that the logical formulation of $\{x : x \not\in g(x)\}$ is correctly expressed in the target system's syntax.
- The proof relies on automated reasoning (MESON_TAC), which may need to be replaced with more explicit reasoning in systems with different automation capabilities.

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
For any set $s$ of type $A \to \text{bool}$ (representing a set of elements of type $A$), we have $s <_c \{t \mid t \subseteq s\}$.

This states that the cardinality of any set $s$ is strictly less than the cardinality of its powerset (the set of all subsets of $s$), which is represented as $\{t \mid t \subseteq s\}$.

### Informal proof
This theorem proves Cantor's theorem that a set's cardinality is strictly less than that of its powerset. The proof proceeds in two main steps:

- First, we show that $s \leq_c \{t \mid t \subseteq s\}$ (the cardinality of $s$ is less than or equal to that of its powerset):
  - This is proven by exhibiting the identity function as an injection from $s$ to its powerset
  - For each element $a \in s$, we map it to the singleton set $\{a\}$, which is a subset of $s$
  - This mapping is clearly injective since different elements map to different singleton sets

- Second, we show that $\neg(s \geq_c \{t \mid t \subseteq s\})$ (the cardinality of $s$ is not greater than or equal to that of its powerset):
  - We prove this by contradiction, using the classic diagonal argument
  - Assume there exists a surjection $g: A \to (A \to \text{bool})$ from $s$ to its powerset
  - We construct a set $D = \{x \in s \mid x \not\in g(x)\}$, which is a subset of $s$
  - For any $y \in A$, we show that $g(y) \neq D$, which contradicts the assumed surjectivity of $g$

The proof uses MESON_TAC to handle the final contradiction in the diagonal argument, showing that no function from a set to its powerset can be surjective.

### Mathematical insight
This theorem is a formalization of Cantor's famous diagonal argument, which was first used to prove that the cardinality of the real numbers is strictly greater than the cardinality of the natural numbers. Here, it's generalized to show that for any set, its powerset has strictly greater cardinality.

The key insight is the diagonal argument: if we assume there's a surjection from a set to its powerset, we can construct a subset that can't be in the range of the surjection by "flipping" the membership of each element relative to its image. This demonstrates that the assumption leads to a contradiction.

This result is fundamental to set theory and has profound implications for the hierarchy of infinite cardinalities, establishing that there is no "largest" infinite set - given any infinite set, its powerset will always be strictly larger.

### Dependencies
- `lt_c` - Less-than relation for cardinalities
- `le_c` - Less-than-or-equal relation for cardinalities
- `LE_C` - Alternative formulation of cardinality comparison
- `SUBSET` - Subset relation
- `SURJECTIVE_RIGHT_INVERSE` - Theorem about surjective functions

### Porting notes
When porting this theorem:
1. Ensure your system can represent sets as functions to boolean (characteristic functions)
2. Make sure the cardinality comparison operations (`<_c` and `≤_c`) are properly defined
3. The diagonal argument is subtle - pay careful attention to the construction of the set that leads to the contradiction
4. In systems with a more direct set theory, you might be able to state this theorem more concisely as $|A| < |P(A)|$, where $P(A)$ is the power set

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
There does not exist an injective function $f : (A \to \text{bool}) \to A$, where injectivity means that for all $x, y$, if $f(x) = f(y)$ then $x = y$.

### Informal proof
We prove this by contradiction:
- Assume there exists an injective function $f : (A \to \text{bool}) \to A$.
- Define $g : A \to (A \to \text{bool})$ by $g(a) = \{b \mid \forall s. f(s) = a \Rightarrow b \in s\}$. This creates, for each $a \in A$, the set of elements that are in every set $s$ whose image under $f$ is $a$.
- Applying `CANTOR_THM_SURJ` to $g$, we know there cannot exist a surjection from $A$ to $(A \to \text{bool})$.
- However, our assumption about $f$ being injective actually implies that $g$ would be surjective (by the properties of injective functions and their inverses).
- This contradiction proves the theorem.

### Mathematical insight
This is another variant of Cantor's theorem, specifically formulated in terms of injectivity rather than surjectivity. It states that the powerset of a set $A$ (represented as $A \to \text{bool}$ in HOL Light) has strictly greater cardinality than $A$ itself, because there cannot be an injection from the powerset to $A$. This is fundamental to set theory and establishes that there is no "largest" cardinality - there is always a larger one.

This formulation is particularly useful in constructive mathematics, as mentioned in the comment, and appears in Paul Taylor's book. The construction of $g$ in the proof creates a diagonal-like set that leads to a direct contradiction with the assumed injectivity of $f$.

### Dependencies
- `CANTOR_THM_SURJ` - The theorem stating there is no surjection from $A$ to $(A \to \text{bool})$.

### Porting notes
When porting this theorem to other systems, note that:
1. The representation of sets as predicates ($A \to \text{bool}$) is specific to HOL Light; other systems may use different representations.
2. The proof relies on Cantor's diagonal argument which should be available in most systems, but the specific formulation might differ.
3. The proof constructs an explicit function $g$ which acts as a "would-be" inverse to the assumed function $f$, creating a direct contradiction with the known result `CANTOR_THM_SURJ`.

---

## CANTOR_LAWVERE

### CANTOR_LAWVERE
- The exact name of this formal item is `CANTOR_LAWVERE`

### Type of the formal statement
- theorem

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
For all functions $h: A \to (A \to B)$, if $h$ is surjective (i.e., for all functions $f: A \to B$, there exists an $x: A$ such that $h(x) = f$), then for all functions $n: B \to B$, there exists an $x: B$ such that $n(x) = x$.

In other words, if there exists a surjective map from $A$ to the function space $A \to B$, then every function from $B$ to itself has a fixed point.

### Informal proof
The proof is a constructive argument using Lawvere's fixed-point theorem:

* Start with a surjective function $h: A \to (A \to B)$ and a function $n: B \to B$.
* Define a function $g: A \to B$ by $g(a) = n(h(a)(a))$ for all $a \in A$.
* Since $h$ is surjective, there exists some $x \in A$ such that $h(x) = g$.
* By function extensionality (represented by `FUN_EQ_THM` in the proof), we know $h(x)(y) = g(y)$ for all $y \in A$.
* In particular, $h(x)(x) = g(x) = n(h(x)(x))$.
* Setting $z = h(x)(x) \in B$, we get $n(z) = z$, which proves the existence of a fixed point for $n$.

The HOL Light proof uses `ASM_MESON_TAC` to automatically reason through the final steps after setting up the necessary definitions and applying function extensionality.

### Mathematical insight
This theorem is a version of Lawvere's fixed-point theorem, which is a category-theoretic generalization of Cantor's diagonal argument. It shows that if there exists a surjective function from a set to its function space (which is impossible for non-trivial cases, by Cantor's theorem), then every endomorphism on the codomain has a fixed point.

The theorem has profound implications in set theory, category theory, and theoretical computer science:

1. It can be used to prove Cantor's theorem that there is no surjection from a set to its power set
2. It relates to fixed-point theorems in various branches of mathematics
3. In computer science, it has applications to recursion theory and the theory of computation

The proof technique uses a diagonal construction similar to the one in Cantor's original argument, showing the deep connection between these results.

### Dependencies
- `FUN_EQ_THM`: Function extensionality theorem that states two functions are equal if they produce the same output for all inputs

### Porting notes
When porting this theorem:
- The proof relies on the automatic reasoning capabilities of `ASM_MESON_TAC`. In systems with less powerful automation, you might need to expand these steps manually.
- The diagonal construction is the key mathematical insight. Make sure to preserve the definition of `g` that applies the function to itself.
- Function extensionality is used explicitly, which might require a separate axiom or theorem in some proof assistants.

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
For any set $A$ and any function $f: A \to (A \to \text{bool})$, it is not the case that $f$ is surjective. That is:

$$\forall f: A \to (A \to \text{bool}). \lnot (\forall s. \exists x. f(x) = s)$$

Where:
- $A$ is any type
- $(A \to \text{bool})$ represents the power set of $A$ (i.e., functions from $A$ to boolean values)
- $f$ is a function mapping elements of $A$ to predicates on $A$
- The theorem states that not every predicate on $A$ can be in the range of $f$

### Informal proof
This is a proof of Cantor's theorem using the Lawvere fixed-point theorem approach.

- We start with a function $f: A \to (A \to \text{bool})$.
- Assume for contradiction that $f$ is surjective, meaning that for every predicate $s: A \to \text{bool}$, there exists some $x \in A$ such that $f(x) = s$.
- Apply `CANTOR_LAWVERE` theorem, which states that if a function $h: A \to (A \to B)$ is surjective, then every function $n: B \to B$ has a fixed point.
- Instantiate the negation function $\lnot: \text{bool} \to \text{bool}$ as our function $n$.
- This leads to a contradiction, because the negation function has no fixed point (there is no boolean value $x$ such that $\lnot x = x$).

### Mathematical insight
This is Cantor's theorem, a fundamental result in set theory that establishes that the power set of any set $A$ has strictly greater cardinality than $A$ itself. The proof uses a variant of Cantor's diagonal argument, formalized through Lawvere's fixed-point theorem approach.

The key insight is that if we had a surjection $f$ from $A$ to its power set, we could construct a predicate that cannot be in the image of $f$ (the "diagonal predicate"), leading to a contradiction.

While the traditional Cantor diagonal argument directly constructs this contradictory predicate, this proof elegantly uses Lawvere's fixed-point theorem to reach the same conclusion by showing that the existence of such a surjection would imply that the negation function has a fixed point, which is impossible.

This theorem has profound implications for understanding cardinality, particularly the existence of infinite hierarchies of increasingly large infinite sets.

### Dependencies
- `CANTOR_LAWVERE`: A formulation of Lawvere's fixed-point theorem which states that if $h: A \to (A \to B)$ is surjective, then every function $B \to B$ has a fixed point.

### Porting notes
When porting this theorem:
- Ensure that the target system has a proper representation of function types and power sets.
- The proof relies on the ability to apply the negation function to boolean values and reason about fixed points.
- The proof is quite concise in HOL Light due to automated reasoning tactics; other systems may require more explicit reasoning about the contradiction that arises.

---

## CANTOR_TAYLOR

### CANTOR_TAYLOR
- `CANTOR_TAYLOR`

### Type of the formal statement
- theorem

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
For any type $A$, there does not exist a function $f: (A \to \text{bool}) \to A$ that is injective. In other words, for any function $f$ from sets of elements of type $A$ to elements of type $A$, there must exist distinct sets $x$ and $y$ such that $f(x) = f(y)$.

Formally: $\forall f: (A \to \text{bool}) \to A. \neg (\forall x,y. f(x) = f(y) \implies x = y)$

### Informal proof
The proof uses Cantor's theorem which states that there is no surjection from a set to its power set.

- First, we assume the contrary: there exists a function $f: (A \to \text{bool}) \to A$ such that for all sets $x$ and $y$, if $f(x) = f(y)$ then $x = y$ (i.e., $f$ is injective).
  
- We then construct the set $S = \{b : A \mid \forall s. f(s) = a \implies b \in s\}$, which is the set of all elements $b$ that belong to every set $s$ whose image under $f$ is $a$.
  
- We apply Cantor's theorem (`CANTOR`), which states that no function $f: A \to (A \to \text{bool})$ can be surjective, rewritten in its contrapositive form via `NOT_EXISTS_THM`.
  
- Using set-theoretic principles (expressed through `EXTENSION` and `IN_ELIM_THM`), the proof reaches a contradiction with our initial assumption.
  
- The automated reasoner (`ASM_MESON_TAC`) completes the proof by deriving the contradiction.

### Mathematical insight
This theorem is a version of Cantor's theorem applied to functions going from sets to elements rather than elements to sets. It establishes that there cannot be an injective function from the power set of $A$ (represented as $A \to \text{bool}$ in HOL Light) to $A$ itself. This is dual to the classical Cantor's theorem, which states there is no surjection from $A$ to its power set.

The result is important in set theory and the foundations of mathematics as it demonstrates fundamental limitations on the relationships between sets and their power sets, regardless of which direction we map between them. This particular formulation highlights that the cardinality of the power set is strictly greater than the cardinality of the original set, as witnessed by the lack of an injective mapping from the power set to the set.

### Dependencies
- `CANTOR`: The standard Cantor's theorem, which states that for any function $f: A \to (A \to \text{bool})$, there exists a set $s$ such that for all $x$, $f(x) \neq s$.
- Other HOL Light tactics and theorems: `NOT_EXISTS_THM`, `EXTENSION`, `IN_ELIM_THM`

### Porting notes
When porting to other systems, note that:
- HOL Light represents sets as predicates (functions to bool)
- The proof relies on Cantor's theorem, so that should be ported first
- The construction of the set $\{b : A \mid \forall s. f(s) = a \implies b \in s\}$ is crucial to the proof
- Automated reasoning is used at the end, so you may need to expand this into more basic logical steps in systems with different automation capabilities

---

## SURJECTIVE_COMPOSE

### SURJECTIVE_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SURJECTIVE_COMPOSE = prove
 (`(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)`,
  MESON_TAC[o_THM]);;
```

### Informal statement
If $f$ is a surjective function (i.e., $\forall y. \exists x. f(x) = y$) and $g$ is a surjective function (i.e., $\forall z. \exists y. g(y) = z$), then their composition $g \circ f$ is also surjective (i.e., $\forall z. \exists x. (g \circ f)(x) = z$).

### Informal proof
The proof uses the MESON automated theorem prover with the theorem about function composition (`o_THM`).

The key argument can be described as:
- Given any $z$ in the codomain of $g \circ f$
- Since $g$ is surjective, there exists $y$ such that $g(y) = z$
- Since $f$ is surjective, there exists $x$ such that $f(x) = y$
- Therefore, $(g \circ f)(x) = g(f(x)) = g(y) = z$
- This shows that for any $z$, there exists an $x$ such that $(g \circ f)(x) = z$, proving that $g \circ f$ is surjective

### Mathematical insight
This theorem formalizes the well-known result from set theory that the composition of two surjective functions is also surjective. This is a fundamental property of surjective functions and is important in many areas of mathematics including set theory, category theory, and abstract algebra. 

The result is intuitive: if $f$ can "reach" every element in its codomain, and $g$ can "reach" every element in its codomain, then by chaining them together, $g \circ f$ can "reach" every element in the codomain of $g$.

### Dependencies
- `o_THM`: The definition of function composition, stating that $(g \circ f)(x) = g(f(x))$

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies only on the basic definition of function composition and the concept of surjectivity. Most proof assistants have built-in support for quantifiers and existential statements, making the statement itself directly translatable.

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
For any function $f : A \to B$, if $f$ is injective (i.e., $\forall x, y. f(x) = f(y) \Rightarrow x = y$), then for any set $t \subseteq A$, there exists a set $s \subseteq B$ such that the preimage of $s$ under $f$ equals $t$. That is:

$$\forall f: A \to B. (\forall x, y. f(x) = f(y) \Rightarrow x = y) \Rightarrow \forall t. \exists s. \{x \mid f(x) \in s\} = t$$

### Informal proof
The proof demonstrates that for any injective function $f$ and set $t$, we can find a set $s$ whose preimage equals $t$.

* Given an injective function $f: A \to B$ and a set $t \subseteq A$, we need to find a set $s \subseteq B$ such that $\{x \mid f(x) \in s\} = t$.
* We claim that $s = f(t) = \{f(x) \mid x \in t\}$ (the image of $t$ under $f$) works.
* To show this, we prove that the sets $\{x \mid f(x) \in f(t)\}$ and $t$ are equal by showing they contain the same elements:
  * For any $x$, $x \in \{x \mid f(x) \in f(t)\} \iff f(x) \in f(t) \iff \exists y \in t. f(x) = f(y)$
  * Since $f$ is injective, $f(x) = f(y) \implies x = y$
  * Therefore, $\exists y \in t. f(x) = f(y) \iff x \in t$
  * This establishes that $\{x \mid f(x) \in f(t)\} = t$, as required.

### Mathematical insight
This theorem characterizes a key property of injective functions: they allow us to "reverse engineer" any subset of their domain by finding an appropriate subset of their codomain. Specifically, it shows that when a function is injective, every set in the domain can be expressed as the preimage of some set in the codomain.

This result is also related to the general notion that injective functions preserve the "information" of their inputs, allowing for reconstruction of the original set. It's a fundamental result used in set theory and the study of functions.

The theorem can be seen as dual to the fact that for any function (injective or not), the image of a preimage is always contained in the original set. For injective functions, we gain the additional property that preimages can be precisely controlled.

### Dependencies
- `EXTENSION`: Two sets are equal if and only if they contain the same elements
- `IN_ELIM_THM`: Characterization of membership in set comprehensions
- `IN_IMAGE`: Characterization of membership in the image of a set

### Porting notes
When porting this theorem:
- Ensure your system has a clear notion of injectivity for functions
- The proof relies on set comprehension and image operations, which should be available in most proof assistants
- Pay attention to how set equality is defined in your target system (extensionality)
- The automated reasoning (`ASM_MESON_TAC`) at the end resolves some details that might require explicit steps in other systems

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
For any types $B$ and $S$, and for any functions $i : B \to S$ and $f : B \to (S \to \text{bool})$, it is not possible for $i$ to be injective and $f$ to be surjective simultaneously. 

Formally: $\forall i : B \to S, \forall f : B \to (S \to \text{bool}), \lnot((\forall x,y. i(x) = i(y) \Rightarrow x = y) \land (\forall s. \exists z. f(z) = s))$

### Informal proof
This theorem is a more general form of Cantor's theorem and follows from the standard Cantor's argument. The proof is as follows:

1. We prove by contradiction. Assume that there exist functions $i: B \to S$ and $f: B \to (S \to \text{bool})$ such that $i$ is injective and $f$ is surjective.

2. We define a composition of functions:
   $g = \text{IMAGE}(f) \circ \lambda s. \{x \mid i(x) \in s\}$

   Where:
   - $\lambda s. \{x \mid i(x) \in s\}$ maps a set $s$ of elements of $S$ to the preimage of $s$ under $i$.
   - $\text{IMAGE}(f)$ maps a set of elements of $B$ to the image of that set under $f$.

3. Apply Cantor's theorem (`CANTOR`) to this composition. Cantor's theorem states that for any function from a type to its powerset, there cannot exist a surjection.

4. To show that our composition $g$ is surjective, we use the fact that the composition of surjective functions is surjective (`SURJECTIVE_COMPOSE`).

5. We demonstrate that:
   - The function $\lambda s. \{x \mid i(x) \in s\}$ is surjective because $i$ is injective (using `INJECTIVE_SURJECTIVE_PREIMAGE`).
   - The function $\text{IMAGE}(f)$ is surjective because $f$ is surjective (using `SURJECTIVE_IMAGE`).

6. This leads to a contradiction with Cantor's theorem, thus proving the statement.

### Mathematical insight
This theorem, named after Peter Johnstone, is a generalization of Cantor's theorem that provides a deeper understanding of the relationship between injective and surjective functions in set theory. The classical Cantor's theorem states that there is no surjection from a set to its power set. This generalization shows that even when we have two different types $B$ and $S$, we cannot simultaneously have an injection from $B$ to $S$ and a surjection from $B$ to the powerset of $S$.

The theorem has important implications in category theory and set theory, as it places fundamental restrictions on the relationship between sets and their powersets. It demonstrates the impossibility of certain constructions and provides insights into the limitations of set-theoretic mappings.

### Dependencies
- Theorems:
  - `CANTOR`: States there is no surjection from a type to its powerset
  - `SURJECTIVE_COMPOSE`: The composition of surjective functions is surjective
  - `INJECTIVE_SURJECTIVE_PREIMAGE`: An injective function allows surjective mapping to preimages
  - `SURJECTIVE_IMAGE`: A surjective function induces a surjective image operation

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure the target system has appropriate representations of functions and powersets
2. The proof relies on composition of functions and set-theoretic operations like image and preimage
3. Take care with the representation of the powerset (sets of type $S \to \text{bool}$ in HOL Light)
4. The dependencies like Cantor's theorem should be ported first

---

