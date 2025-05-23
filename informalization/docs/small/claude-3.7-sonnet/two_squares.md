# two_squares.ml

## Overview

Number of statements: 24

This file formalizes the theorem that any prime number congruent to 1 modulo 4 can be represented as the sum of two squares. It builds on the prime number library and provides the complete formalization of this classical result in number theory, including necessary lemmas about quadratic residues and the descent method. The implementation likely includes constructive proofs showing how to find the two squares for a given prime of the form 4k+1.

## involution

### Name of formal statement
involution

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let involution = new_definition
  `involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)`;;
```

### Informal statement
A function $f$ is an involution on a set $s$ if and only if for all $x \in s$, both $f(x) \in s$ and $f(f(x)) = x$.

Formally:
$$\text{involution}(f, s) \iff \forall x. x \in s \Rightarrow f(x) \in s \wedge f(f(x)) = x$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
An involution is a function that is its own inverse - when applied twice, it returns to the original value. This is a fundamental concept in many areas of mathematics:

- In group theory, involutions are elements of order 2
- In geometry, reflections are involutions
- In algebra, the operation of taking the transpose of a matrix is an involution
- In set theory, the complement operation is an involution

The definition requires that the function maps elements from the set $s$ back into $s$ (closure), and that applying the function twice returns the original element (self-inverse property).

This concept is being introduced here as part of a development related to the representation of primes congruent to 1 modulo 4 as sums of two squares, as indicated by the comment. Involutions often play important roles in number-theoretic proofs and constructions.

### Dependencies
This is a basic definition with no direct dependencies on other HOL Light theorems or definitions.

### Porting notes
When porting this definition:
- Ensure the system has a notion of function application and set membership
- The definition uses a universal quantifier with an implication, which is standard in most proof assistants
- The conjunction in the consequent ($\wedge$) should translate straightforwardly
- Consider whether your target system requires explicit type annotations for $f$ or $s$

This definition should port easily to most proof assistants as it uses only basic logical connectives and set membership.

---

## INVOLUTION_IMAGE

### Name of formal statement
INVOLUTION_IMAGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_IMAGE = prove
 (`!f s. involution f s ==> (IMAGE f s = s)`,
  REWRITE_TAC[involution; EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;
```

### Informal statement
For any function $f$ and any set $s$, if $f$ is an involution on $s$, then the image of $s$ under $f$ is equal to $s$ itself: 
$$\forall f \, s. \, \text{involution}(f, s) \Rightarrow \text{IMAGE}(f, s) = s$$

Where an involution on a set is a function that is its own inverse when restricted to that set.

### Informal proof
The proof proceeds as follows:

* First, we rewrite the goal using the definitions of `involution`, `EXTENSION`, and `IN_IMAGE`.
  - `involution f s` means $\forall x \in s. f(f(x)) = x$ and $\forall x \in s. f(x) \in s$
  - `EXTENSION` expands the set equality to $\forall y. y \in \text{IMAGE}(f, s) \Leftrightarrow y \in s$
  - `IN_IMAGE` expands $y \in \text{IMAGE}(f, s)$ to $\exists x \in s. f(x) = y$

* Then, the proof is completed using the MESON automated theorem prover:
  - For the forward direction, if $y \in \text{IMAGE}(f, s)$, then there exists $x \in s$ such that $f(x) = y$. Since $f$ is an involution on $s$, we have $y = f(x) \in s$.
  - For the reverse direction, if $y \in s$, then since $f$ is an involution, $f(y) \in s$ and $f(f(y)) = y$. So $y = f(f(y))$ where $f(y) \in s$, which means $y \in \text{IMAGE}(f, s)$.

### Mathematical insight
This theorem formalizes a fundamental property of involutions: they preserve the set they act on. This is intuitive since an involution is a bijection from a set to itself (when each element maps to the set and the function is its own inverse).

The result is important because it shows that involutions are special kinds of permutations that leave the set invariant under the image operation. This property is particularly useful in various mathematical contexts, such as group theory, where involutions play an important role.

### Dependencies
- Definitions:
  - `involution`: A function that is its own inverse when restricted to a set
  - `EXTENSION`: Set equality defined by element membership
  - `IN_IMAGE`: Membership in the image of a function

### Porting notes
When porting this theorem to other systems:
1. Ensure that the definition of involution includes both self-inverse property and closure under the function.
2. The proof is quite straightforward once the definitions are expanded, so most proof assistants should be able to handle it with basic set-theoretic automation.
3. The notion of function image might be defined differently in other systems, but the core idea remains the same.

---

## INVOLUTION_DELETE

### Name of formal statement
INVOLUTION_DELETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_DELETE = prove
 (`involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)`,
  REWRITE_TAC[involution; IN_DELETE] THEN MESON_TAC[]);;
```

### Informal statement
If $f$ is an involution on a set $s$, $a \in s$, and $f(a) = a$, then $f$ is also an involution on the set $s \setminus \{a\}$.

### Informal proof
The proof starts by expanding the definition of `involution` and the membership in `DELETE` (which corresponds to set difference with a singleton). Then the `MESON_TAC` procedure completes the proof automatically.

In more detail:
- An involution $f$ on a set $s$ means that $f$ maps $s$ to itself and $f(f(x)) = x$ for all $x \in s$.
- Given that $f$ is an involution on $s$, $a \in s$, and $f(a) = a$, we need to show that:
  - $f$ maps $s \setminus \{a\}$ to itself
  - For all $x \in s \setminus \{a\}$, $f(f(x)) = x$

The second condition is inherited from the original involution property. For the first condition, we need to show that for any $x \in s \setminus \{a\}$, $f(x) \in s \setminus \{a\}$. Since $f$ is an involution on $s$, we know $f(x) \in s$. We only need to show $f(x) \neq a$. If $f(x) = a$, then $f(f(x)) = f(a) = a$ (given that $f(a) = a$). But since $f$ is an involution, $f(f(x)) = x$, which would mean $x = a$, contradicting $x \in s \setminus \{a\}$.

### Mathematical insight
This theorem shows that when an element is a fixed point of an involution (i.e., $f(a) = a$), removing that element from the domain preserves the involution property. This is intuitively clear because a fixed point doesn't participate in any non-trivial "swapping" behavior that characterizes involutions.

The result is useful when constructing or analyzing involutions by allowing them to be built or decomposed incrementally, handling fixed points separately from pairs of elements that exchange with each other.

### Dependencies
- `involution`: Definition of an involution (a function that is its own inverse when applied twice)
- `IN_DELETE`: Theorem about membership in a set with an element deleted

### Porting notes
When porting to other systems, ensure that the definition of involution is consistent with HOL Light's definition. In HOL Light, an involution on a set requires both that the function maps the set to itself and that applying the function twice gives the identity function.

---

## INVOLUTION_STEPDOWN

### Name of formal statement
INVOLUTION_STEPDOWN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_STEPDOWN = prove
 (`involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})`,
  REWRITE_TAC[involution; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;
```

### Informal statement
If $f$ is an involution on a set $s$ and $a \in s$, then $f$ is also an involution on the set $s \setminus \{a, f(a)\}$.

Formally, if $f$ is a function such that $f \circ f = \text{id}$ on $s$ (i.e., $f$ is an involution on $s$), and $a \in s$, then $f$ is also an involution on the set $s \setminus \{a, f(a)\}$.

### Informal proof
The proof proceeds by expanding the definition of involution and then applying logical reasoning with the set operations.

An involution is a function that is its own inverse, meaning $f(f(x)) = x$ for all $x$ in the domain. The theorem states that if $f$ is an involution on $s$, then it remains an involution when restricting the domain to $s \setminus \{a, f(a)\}$.

The key insight is that removing both $a$ and $f(a)$ from the domain preserves the involution property, since:
1. For any $x \in s \setminus \{a, f(a)\}$, we have $x \neq a$ and $x \neq f(a)$
2. Since $f$ is an involution on $s$, we know $f(f(x)) = x$ for all $x \in s$
3. For the properties of an involution to hold on the restricted domain, we need to ensure that applying $f$ to any element in the restricted domain also gives an element in the restricted domain
4. Since $f(f(x)) = x \in s \setminus \{a, f(a)\}$, we need $f(x) \in s \setminus \{a, f(a)\}$
5. This follows because if $f(x) = a$ or $f(x) = f(a)$, then $x = f(a)$ or $x = a$ respectively (by applying $f$ again and using the involution property), which contradicts our assumption that $x \in s \setminus \{a, f(a)\}$

The formal proof uses `REWRITE_TAC` to expand the definition of involution and set operations, and then `MESON_TAC` automatically completes the proof using first-order reasoning.

### Mathematical insight
This theorem captures a fundamental property of involutions: they remain involutions when "stepping down" by removing a symmetric pair of elements from their domain.

The key insight is that involutions create a natural pairing of elements (each element pairs with its image), and removing such a complete pair preserves the involution property on the remaining elements. This is useful for inductive arguments about involutions, allowing one to reduce the size of the domain while preserving the essential property.

This theorem could be used as part of an inductive decomposition of involutions, or in constructive proofs about involutions on finite sets.

### Dependencies
- `involution`: Definition of an involution function
- Standard set theory operations: `IN`, `DIFF`, `INSERT`, `NOT_IN_EMPTY`

### Porting notes
When porting this theorem:
1. Ensure the definition of involution is consistent (typically $f \circ f = \text{id}$ on the domain)
2. The proof is relatively straightforward in most systems with decent automation for first-order logic and set theory
3. In systems with dependent types, you might need to handle the domain restriction more carefully and provide a proof that $f$ maps elements of the restricted domain back to the restricted domain

---

## INVOLUTION_NOFIXES

### Name of formal statement
INVOLUTION_NOFIXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_NOFIXES = prove
 (`involution f s ==> involution f {x | x IN s /\ ~(f x = x)}`,
  REWRITE_TAC[involution; IN_ELIM_THM] THEN MESON_TAC[]);;
```

### Informal statement
The theorem states that if $f$ is an involution on a set $s$, then $f$ is also an involution on the subset of elements of $s$ that are not fixed points of $f$.

More formally, if $f$ is an involution on $s$, then $f$ is an involution on $\{x \in s \mid f(x) \neq x\}$.

### Informal proof
The proof proceeds by:

- First, we rewrite the goal using the definition of `involution` and simplify the set comprehension notation using `IN_ELIM_THM`.
- Then we use the `MESON_TAC` automated reasoning tool to complete the proof.

This is a straightforward result that follows directly from the definition of an involution. If $f$ is an involution on $s$, then $f \circ f = id$ on $s$. The subset $\{x \in s \mid f(x) \neq x\}$ contains only elements of $s$, so $f \circ f = id$ still holds on this subset.

### Mathematical insight
This theorem identifies that the property of being an involution is preserved when restricting to the subset of non-fixed points. This is useful because in many applications of involutions, we're particularly interested in the elements that are moved by the involution (i.e., the non-fixed points).

An involution can be viewed as consisting of fixed points (where $f(x) = x$) and pairs of elements that swap with each other (where $f(x) = y$ and $f(y) = x$ for $x \neq y$). This theorem essentially states that if we remove all the fixed points, we still have a valid involution on the remaining elements.

### Dependencies
- `involution`: The definition of an involution (a function that is its own inverse)
- `IN_ELIM_THM`: Theorem for simplifying set comprehension notation
- `MESON_TAC`: Automated theorem proving tactic

### Porting notes
This should be straightforward to port to other systems, as it's a simple result about involutions that doesn't rely on complex HOL Light machinery. The main requirement is having the definition of an involution available.

---

## INVOLUTION_SUBSET

### INVOLUTION_SUBSET
- INVOLUTION_SUBSET

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INVOLUTION_SUBSET = prove
 (`!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t`,
  REWRITE_TAC[involution; SUBSET] THEN MESON_TAC[]);;
```

### Informal statement
If $f$ is an involution on a set $s$, and $t$ is a subset of $s$ such that $f$ maps elements of $t$ back into $t$ (i.e., $\forall x \in t, f(x) \in t$), then $f$ is also an involution on $t$.

Formally, for any function $f$ and sets $s$ and $t$:
$\forall f, s, t.\ \text{involution}(f, s) \land (\forall x. x \in t \Rightarrow f(x) \in t) \land t \subseteq s \Rightarrow \text{involution}(f, t)$

### Informal proof
The proof follows directly from the definition of involution and the subset relation:

- An involution $f$ on a set $s$ means that for all $x \in s$, $f(f(x)) = x$ and $f(x) \in s$.
- If $t \subseteq s$, then all elements of $t$ are also in $s$.
- If $\forall x \in t, f(x) \in t$, then $f$ maps $t$ to itself.
- Since $f$ is an involution on $s$, we already know that $f(f(x)) = x$ for all $x \in s$, which includes all $x \in t$.
- Therefore, $f$ satisfies all the conditions to be an involution on $t$.

### Mathematical insight
This theorem establishes that the property of being an involution is preserved when restricting the domain to a subset, provided that the function maps this subset into itself. This is a natural extension property that allows us to work with involutions on specific subsets of a larger domain.

An involution is a function that is its own inverse ($f(f(x)) = x$), and this theorem shows that this self-inverse property carries over to restrictions of the domain.

This result is useful for constructing involutions on specific subsets or for proving properties about involutions when restricting attention to a particular subset of the domain.

### Dependencies
- `involution`: Definition of an involution on a set
- `SUBSET`: Definition of subset relation

### Porting notes
When porting this theorem to other proof assistants, ensure that:
- The definition of involution is properly ported first
- The subset relation is correctly defined
- The theorem uses the appropriate quantifiers and logical connectives in the target system

---

## INVOLUTION_EVEN

### INVOLUTION_EVEN
- The HOL Light theorem name is `INVOLUTION_EVEN`.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let INVOLUTION_EVEN = prove
 (`!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)`,
  REWRITE_TAC[involution] THEN MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]);;
```

### Informal statement
For any set $s$ of type $A$, if:
- $s$ is finite, and
- $f$ is an involution on $s$ (i.e., $f$ applied twice is the identity function on $s$), and
- For all $x \in s$, $f(x) \neq x$ (i.e., $f$ has no fixed points in $s$)

Then the cardinality of $s$ is even: $\text{EVEN}(\text{CARD}(s))$.

### Informal proof
The proof relies on a more general theorem `INVOLUTION_EVEN_NOFIXPOINTS`:

1. First, we rewrite using the definition of `involution`, which states that a function $f$ is an involution on a set $s$ if for all $x \in s$, we have $f(f(x)) = x$.
2. After simplifying with the definition, we apply the `MESON_TAC` automated reasoner with the theorem `INVOLUTION_EVEN_NOFIXPOINTS`.

The theorem `INVOLUTION_EVEN_NOFIXPOINTS` likely proves that a fixpoint-free involution on a finite set partitions the set into pairs (where each element is paired with its image), and therefore the set must have even cardinality.

### Mathematical insight
This theorem formalizes an important combinatorial property: when a function pairs elements of a set such that no element is paired with itself, the set must have an even number of elements. 

Intuitively, an involution without fixed points creates a perfect pairing of elements in the set - each element $x$ is paired with $f(x)$, and since $f(f(x)) = x$, these pairs partition the set. Since each pair contains exactly 2 elements, the total cardinality must be even.

This result has applications in various areas of mathematics including group theory (particularly when studying involutions in permutation groups), combinatorics, and graph theory (perfect matchings).

### Dependencies
- **Theorems:** `INVOLUTION_EVEN_NOFIXPOINTS`
- **Definitions:** `involution`

### Porting notes
When porting this theorem:
1. Ensure that the definition of `involution` is ported first: a function $f$ is an involution on set $s$ if for all $x \in s$, $f(f(x)) = x$.
2. You'll need to port the more general theorem `INVOLUTION_EVEN_NOFIXPOINTS` as well.
3. The concept of `EVEN` and `CARD` (cardinality) should be defined in the destination system's standard library.
4. This proof is quite short and relies primarily on automated reasoning via `MESON_TAC`, so you might need to apply appropriate automation in your target system or expand the proof steps manually.

---

## INVOLUTION_FIX_ODD

### Name of formal statement  
INVOLUTION_FIX_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_FIX_ODD = prove
 (`FINITE(s) /\ involution f s /\ (?!a:A. a IN s /\ (f a = a))
   ==> ODD(CARD s)`,
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (s DELETE a)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE; ODD; NOT_ODD] THEN
  MATCH_MP_TAC INVOLUTION_EVEN THEN
  ASM_SIMP_TAC[INVOLUTION_DELETE; FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
Let $s$ be a finite set and $f$ be an involution on $s$. If $f$ has exactly one fixed point in $s$, then the cardinality of $s$ is odd.

More precisely: If $s$ is a finite set and $f : A \to A$ is an involution on $s$ (i.e., $f \circ f = id$ on $s$), and there exists a unique $a \in s$ such that $f(a) = a$, then $|s|$ is odd.

### Informal proof
The proof follows these steps:

* We start by reformulating the unique existence condition as existence and uniqueness.
* Let $a$ be the unique fixed point of $f$ in $s$.
* We rewrite $s$ as $s = \{a\} \cup (s \setminus \{a\})$, which is justified because $a \in s$.
* Since $a \notin s \setminus \{a\}$, we can use the cardinality formula: $|s| = 1 + |s \setminus \{a\}|$.
* To show that $|s|$ is odd, we need to show that $|s \setminus \{a\}|$ is even.
* The function $f$ restricted to $s \setminus \{a\}$ remains an involution.
* Furthermore, this restriction has no fixed points, since $a$ is the only fixed point of $f$ in $s$.
* By the theorem `INVOLUTION_EVEN`, an involution without fixed points on a finite set must have an even cardinality.
* Therefore, $|s \setminus \{a\}|$ is even, making $|s| = 1 + |s \setminus \{a\}|$ odd.

### Mathematical insight
This theorem characterizes the relationship between fixed points of involutions and the parity of the set's cardinality. Intuitively, an involution pairs elements together (each element with its image), with any fixed points left unpaired. When there's exactly one fixed point, the remaining elements form pairs, resulting in an odd total count. 

This result is part of a broader family of theorems relating involutions to set cardinality:
- An involution with no fixed points implies even cardinality
- An involution with exactly one fixed point implies odd cardinality
- Generally, the parity of the set's cardinality equals the parity of the number of fixed points

This is a fundamental result in combinatorics and has applications in various areas of mathematics including group theory, where involutions correspond to elements of order 2.

### Dependencies
- `INVOLUTION_EVEN`: A theorem stating that a finite set with an involution having no fixed points has even cardinality
- `INVOLUTION_DELETE`: A result about the restriction of an involution to a set with an element removed
- `EXISTS_UNIQUE_DEF`: Definition of unique existence
- `CARD_CLAUSES`: Basic properties of the cardinality function
- `FINITE_DELETE`: Result about finiteness of a set with an element removed 
- `ODD`: Definition of oddness for natural numbers
- `NOT_ODD`: Negation of oddness

### Porting notes
When porting this theorem:
- Ensure that your involution definition requires that $f \circ f = id$ on the domain $s$.
- The unique existence quantifier `?!` may need to be expanded in systems that don't have it as a primitive.
- The theorem relies on the fundamental property that removing the unique fixed point leaves a set with an even number of elements, which should be emphasized in the port.

---

## INVOLUTION_ODD

### Name of formal statement
INVOLUTION_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_ODD = prove
 (`!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)`,
  REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[INVOLUTION_EVEN]);;
```

### Informal statement
For any finite set $s$ and function $f$, if $f$ is an involution on $s$ and the cardinality of $s$ is odd, then there exists an element $a \in s$ such that $f(a) = a$.

### Informal proof
The proof uses a straightforward approach by working with the contrapositive of the related theorem about even cardinality sets.

- First, we rewrite the condition `ODD(CARD s)` using `GSYM NOT_EVEN` which transforms it to `~EVEN(CARD s)` (not even).
- Then we use `MESON_TAC` with `INVOLUTION_EVEN`, which states that if $f$ is an involution on $s$ with no fixed points, then the cardinality of $s$ must be even.
- The logical combination of these facts proves the result: if the cardinality is odd (not even) and $f$ is an involution, then $f$ must have a fixed point.

### Mathematical insight
This theorem captures an important property of involutions (functions that are their own inverse, i.e., $f(f(x)) = x$) acting on finite sets with odd cardinality. Intuitively, an involution pairs up elements of a set, with each element paired with its image. If there are an odd number of elements, at least one element must be paired with itself (a fixed point).

This result is complementary to `INVOLUTION_EVEN`, which states that an involution without fixed points can only exist on sets with even cardinality. Together, these theorems completely characterize when involutions must have fixed points based on parity considerations.

This property has applications in various areas of mathematics, including group theory, combinatorics, and graph theory.

### Dependencies
#### Theorems
- `INVOLUTION_EVEN`: Used as the main theorem that provides the contrapositive result
- `NOT_EVEN`: Used to rewrite the odd cardinality condition

### Porting notes
When porting this theorem:
- Ensure your target system has a definition of involution that matches HOL Light's
- Make sure the parity concepts (ODD, EVEN) for cardinality are properly defined
- The proof is quite straightforward and should be easily adaptable to systems with good automation for logical reasoning

---

## INVOLUTION_FIX_FIX

### INVOLUTION_FIX_FIX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let INVOLUTION_FIX_FIX = prove
 (`!f g s. FINITE(s) /\ involution f s /\ involution g s /\
           (?!x. x IN s /\ (f x = x)) ==> ?x. x IN s /\ (g x = x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVOLUTION_ODD THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INVOLUTION_FIX_ODD THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
For any functions $f$ and $g$ and any finite set $s$:
If 
- $f$ is an involution on $s$
- $g$ is an involution on $s$
- there exists a unique $x \in s$ such that $f(x) = x$

then there exists a point $x \in s$ such that $g(x) = x$.

### Informal proof
The proof proceeds in two main steps:

1. First, we use the theorem `INVOLUTION_FIX_ODD` which states that if $f$ is an involution on a finite set $s$ and there exists a unique fixed point of $f$ in $s$, then the cardinality of $s$ is odd.

2. Then, we apply the theorem `INVOLUTION_ODD` which states that if $g$ is an involution on a finite set $s$ and the cardinality of $s$ is odd, then there exists a fixed point of $g$ in $s$.

Combining these two results:
- From the unique fixed point of $f$, we deduce that $s$ has odd cardinality
- Since $g$ is an involution on $s$ with odd cardinality, $g$ must have a fixed point in $s$

### Mathematical insight
This theorem establishes an important connection between different involutions on the same finite set. An involution is a function that is its own inverse (i.e., $f \circ f = \text{identity}$). 

The key insight is that the property of having a fixed point for an involution is related to the parity of the set's cardinality. Specifically:
- Involutions on finite sets with odd cardinality always have at least one fixed point
- If an involution has exactly one fixed point, then the set must have odd cardinality

This result shows that the existence of a unique fixed point for one involution forces the existence of at least one fixed point for any other involution on the same set. This is a purely combinatorial property that connects the behavior of different involutions.

### Dependencies
- `INVOLUTION_ODD`: If $g$ is an involution on a finite set $s$ with odd cardinality, then $g$ has a fixed point in $s$
- `INVOLUTION_FIX_ODD`: If $f$ is an involution on a finite set $s$ and has a unique fixed point, then $s$ has odd cardinality

### Porting notes
When porting this theorem:
- You'll need to first port the theorems about involutions and fixed points
- The uniqueness quantifier `?!x` in HOL Light corresponds to "exists unique" in other systems
- This theorem relies on a chain of reasoning about parity of set cardinality, which should be straightforward in most proof assistants

---

## zset

### Name of formal statement
zset

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zset = new_definition
  `zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}`;;
```

### Informal statement
The definition `zset(a)` represents the set of all triples $(x,y,z)$ of real numbers such that $x^2 + 4yz = a$.

In mathematical notation:
$$\text{zset}(a) = \{(x,y,z) \mid x^2 + 4yz = a\}$$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition creates a set of points $(x,y,z)$ in 3D space that satisfy the equation $x^2 + 4yz = a$, which is a quadratic form. This particular form appears in Zagier's "one-sentence" proof related to number theory, specifically in his elegant proof that every prime number $p$ congruent to 1 modulo 4 can be written as a sum of two squares.

The equation $x^2 + 4yz = a$ defines a quadratic surface in three-dimensional space. When $a$ is fixed, the set `zset(a)` consists of all points on this surface. The structure and properties of this set play a crucial role in Zagier's proof by facilitating a specific involution (a function that is its own inverse) that helps count solutions in a particular way.

This definition forms the foundation for formalizing Zagier's concise and elegant number-theoretic proof.

### Dependencies
None explicitly mentioned in the provided information.

### Porting notes
When porting this definition to other proof assistants:
- Ensure the target system supports set comprehension notation
- Consider whether the target system treats variables as implicitly typed (HOL Light treats them as real numbers by default)
- In typed systems like Lean or Coq, you might need to explicitly specify the type of $x$, $y$, and $z$, and consider whether to use reals or another number type depending on the intended application

---

## zag

### Name of formal statement
zag

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zag = new_definition
  `zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)`;;
```

### Informal statement
The function $\text{zag}(x, y, z)$ is defined as follows:
$$\text{zag}(x, y, z) = \begin{cases}
(x + 2z, z, y - (x + z)) & \text{if}\ x + z < y \\
(2y - x, y, (x + z) - y) & \text{if}\ x + z \geq y\ \text{and}\ x < 2y \\
(x - 2y, (x + z) - y, y) & \text{if}\ x + z \geq y\ \text{and}\ x \geq 2y
\end{cases}$$

This function takes three real number inputs and returns a triple of real numbers based on the conditional branches above.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The zag function appears to be a transformation or mapping function that takes a triple of values and produces a new triple based on specific conditions. This kind of piecewise-defined function often appears in algorithms that need to handle different cases efficiently.

While the name "zag" doesn't reveal much about its purpose, the structure suggests it might be related to:
- Some kind of reflection or transformation operation
- A step in an iterative algorithm
- A normalization procedure for triples of numbers

Without additional context, it's difficult to determine the specific mathematical significance of this function, but the conditions and transformations suggest it's designed to maintain some invariant or perform a specific rearrangement of values based on their relative magnitudes.

### Dependencies
No explicit dependencies identified.

### Porting notes
When porting this definition:
- Ensure the target system handles piecewise functions with multiple conditions correctly
- Be careful with the order of conditions - they must be evaluated in sequence as written
- The definition uses straightforward arithmetic operations that should translate directly to most systems

---

## tag

### TAG

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let tag = new_definition
  `tag((x,y,z):num#num#num) = (x,z,y)`;;
```

### Informal statement
This definition introduces a function `tag : num × num × num → num × num × num` that rearranges the components of a triple of natural numbers. Specifically, for any triple $(x, y, z)$ of natural numbers, `tag(x, y, z) = (x, z, y)`.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This function performs a simple permutation of the components of a triple, swapping the second and third components while leaving the first component unchanged. Such permutation functions are often used in formal developments to reorder tuple components when needed for specific operations or to match certain interfaces.

In formal verification contexts, functions like this are typically used as auxiliary definitions to facilitate other proofs or definitions where a specific ordering of tuple elements is required.

### Dependencies
No significant dependencies beyond the basic HOL Light tuple types.

### Porting notes
This definition should be straightforward to port to other proof assistants. In systems with strong type inference, the explicit type annotation `: num × num × num` might not be necessary. In some systems, you might define this as a simple lambda function instead of a named definition, depending on how it's used.

---

## ZAG_INVOLUTION_GENERAL

### Name of formal statement
ZAG_INVOLUTION_GENERAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZAG_INVOLUTION_GENERAL = prove
 (`0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))`,
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
If $x > 0$, $y > 0$, and $z > 0$, then applying the `zag` operation twice to the triple $(x, y, z)$ returns the original triple, i.e., $\text{zag}(\text{zag}(x, y, z)) = (x, y, z)$.

### Informal proof
The proof demonstrates that the `zag` operation is an involution (self-inverse) when operating on positive triples:

- First, we expand the definition of `zag` for the outer application.
- Then, we perform case analysis on the conditions in the `zag` definition, simplifying with assumptions.
- Next, we expand the inner `zag` application.
- We perform another round of case analysis on the conditions.
- We convert the equality of triples to component-wise equality using `PAIR_EQ`.
- Finally, we combine all assumptions and prove the result using arithmetic reasoning.

The key insight is that the `zag` operation, which likely permutes or transforms the components of the triple based on certain conditions, returns to the original triple when applied twice.

### Mathematical insight
The theorem establishes that `zag` is an involution on positive triples, meaning it's its own inverse. Such operations are important in mathematics as they form a class of functions with the property $f(f(x)) = x$. Involutions appear in various mathematical contexts including geometry (reflections), group theory, and combinatorics.

Without seeing the definition of `zag`, it appears to be some form of permutation or transformation on triples of positive real numbers that has this involutive property. This type of result is useful for understanding the algebraic structure of the operation and can be important in applications where bidirectional transformations are needed.

### Dependencies
- Definitions:
  - `zag`: The operation being studied, which takes a triple of real numbers and returns another triple.
  - `PAIR_EQ`: Likely a utility that converts equality of pairs/triples to component-wise equality.

### Porting notes
When porting to other systems:
- You'll need to first implement the `zag` function, which is not shown in this excerpt.
- The proof uses a combination of rewriting, case analysis, and arithmetic solving that most proof assistants should be able to handle with their respective tactics.
- Pay attention to how pairs/tuples and their equality are represented in the target system.

---

## IN_TRIPLE

### Name of formal statement
IN_TRIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_TRIPLE = prove
 (`(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;
```

### Informal statement
The theorem states that for any elements $a$, $b$, and $c$, we have
$$(a, b, c) \in \{(x, y, z) \mid P(x, y, z)\} \iff P(a, b, c)$$

This means that a triple $(a, b, c)$ belongs to the set of all triples $(x, y, z)$ satisfying the predicate $P$ if and only if the predicate $P$ holds for $a$, $b$, and $c$.

### Informal proof
The proof proceeds as follows:

1. Apply `REWRITE_TAC[IN_ELIM_THM; PAIR_EQ]` which:
   - Uses `IN_ELIM_THM` to unfold the set comprehension notation, converting the left side to a statement about existence of tuples satisfying $P$
   - Uses `PAIR_EQ` to equate pairs/tuples when their components are equal

2. Use `MESON_TAC[]` to complete the proof through automated first-order reasoning, which resolves the remaining logical equivalence after the rewrite steps.

The proof essentially unfolds the definition of set membership for a triple in a set defined by comprehension, then shows the logical equivalence automatically.

### Mathematical insight
This theorem is a fundamental set-theoretic result that characterizes membership in sets defined by comprehension for triples. It extends the more basic result for pairs and is essential for working with relations and functions on multiple arguments in a set-theoretic foundation.

The theorem provides a direct connection between the set-theoretic notation for comprehension and the underlying logical predicate, which is crucial for formal reasoning about sets of tuples.

### Dependencies
- Theorems:
  - `IN_ELIM_THM`: Relates membership in a set comprehension to the defining predicate
  - `PAIR_EQ`: States that two pairs are equal if and only if their components are equal

### Porting notes
When porting to other proof assistants:
- Ensure that the target system has an appropriate representation of tuples or ordered pairs
- Check how set comprehension is defined in the target system (sometimes it's built-in, other times defined)
- Note that in some systems, the handling of tuples might require explicit typing, unlike HOL Light's more implicit approach

---

## PRIME_SQUARE

### Name of formal statement
PRIME_SQUARE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_SQUARE = prove
 (`!n. ~prime(n * n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[PRIME_0; MULT_CLAUSES] THEN
  REWRITE_TAC[prime; NOT_FORALL_THM; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
  DISJ2_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ARITH_RULE `n = n * 1`] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL]);;
```

### Informal statement
For any natural number $n$, the square $n^2$ is not a prime number.

Formally: $\forall n \in \mathbb{N}, \neg \text{prime}(n \cdot n)$

### Informal proof
We prove that for any natural number $n$, $n^2$ is not prime.

* First, consider the case where $n = 0$. Then $n^2 = 0$, which is not prime by theorem `PRIME_0`.

* Next, consider the case where $n = 1$. Then $n^2 = 1$, which is not prime by the definition of primality (since $1$ is not greater than $1$).

* For the case where $n > 1$, we show that $n^2$ is not prime by finding a proper divisor. 
  - We choose $n$ itself as this divisor.
  - Clearly, $n$ divides $n^2$ by the property of divisibility (`DIVIDES_LMUL` and `DIVIDES_REFL`).
  - We need to show that $n$ is a proper divisor, i.e., $n \neq 1$ and $n \neq n^2$.
  - We already established that $n \neq 1$ in the case analysis.
  - To show $n \neq n^2$, we rewrite $n = n \cdot 1$ and use the cancellation property of multiplication to deduce that $n \neq n^2$ is equivalent to $1 \neq n$, which we have already established.

Therefore, for any natural number $n$, $n^2$ is not prime.

### Mathematical insight
This theorem proves the basic number theory fact that square numbers cannot be prime. It's a canonical result that follows directly from the definition of primality.

The key insight is that a square number $n^2$ (for $n > 1$) always has at least one divisor (namely $n$ itself) that is neither 1 nor the number itself, which immediately disqualifies it from being prime.

This result is part of the fundamental properties of prime numbers and is frequently used in number-theoretic proofs and when reasoning about factorization.

### Dependencies
#### Theorems
- `PRIME_0`: Zero is not prime.
- `DIVIDES_REFL`: For any number $x$, $x$ divides $x$.

#### Implicitly Used
- Definition of primality
- Basic arithmetic properties of multiplication
- Divisibility properties, particularly `DIVIDES_LMUL`
- Cancellation property for multiplication (`EQ_MULT_LCANCEL`)

### Porting notes
When porting this theorem:
- Ensure the definition of primality is consistent with HOL Light's (typically, a prime number is a natural number greater than 1 whose only divisors are 1 and itself).
- The proof structure is straightforward and should translate easily to other systems.
- The case analysis approach (handling $n=0$, $n=1$, and $n>1$ separately) is standard and should work in most proof assistants.

---

## PRIME_4X

### Name of formal statement
PRIME_4X

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_4X = prove
 (`!n. ~prime(4 * n)`,
  GEN_TAC THEN REWRITE_TAC[prime; NOT_FORALL_THM; DE_MORGAN_THM] THEN
  DISJ2_TAC THEN EXISTS_TAC `2` THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 2`)) THEN
  ASM_SIMP_TAC[GSYM MULT_ASSOC; DIVIDES_RMUL; DIVIDES_REFL; ARITH_EQ] THEN
  ASM_CASES_TAC `n = 0` THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, $4n$ is not prime.

Formally, $\forall n. \neg \text{prime}(4 \cdot n)$, where $\text{prime}(p)$ means that $p$ is a prime number.

### Informal proof
We need to prove that for any natural number $n$, $4n$ is not prime.

According to the definition of prime numbers in HOL Light, a number $p$ is prime if it's greater than 1 and its only divisors are 1 and itself. So we need to show that either $4n \leq 1$ or $4n$ has a divisor other than 1 and itself.

The proof proceeds as follows:

* We show that $4n$ is not prime by finding a proper divisor, specifically $2$.
* We prove that $2$ divides $4n$ by rewriting $4$ as $2 \cdot 2$ and showing that $2$ divides $2 \cdot 2 \cdot n$.
* We use the fact that $2$ divides $2$ (by `DIVIDES_REFL`) and then apply `DIVIDES_RMUL` to show that $2$ divides $2 \cdot (2 \cdot n)$.
* The proof handles the special case when $n = 0$ separately using arithmetic reasoning.

The key step is demonstrating that $2$ is a proper divisor of $4n$ when $n \neq 0$ (and when $n = 0$, the number is 0, which is not prime by definition).

### Mathematical insight
This theorem establishes a basic property of prime numbers: any multiple of 4 cannot be prime. This follows from the more general fact that any multiple of a number greater than 1 cannot be prime (except for the number itself).

The proof uses the specific structure of $4n = 2 \cdot 2 \cdot n$ to show that $2$ is always a proper divisor of $4n$. This makes $4n$ composite whenever $n > 0$, and when $n = 0$, we have $4n = 0$, which is not prime by definition.

This result is part of a broader family of results about numbers of special forms and their primality properties, which are fundamental in number theory.

### Dependencies
- Theorems:
  - `DIVIDES_REFL`: For all $x$, $x$ divides $x$.
  - `DIVIDES_RMUL`: For all $d$, $a$, and $x$, if $d$ divides $a$, then $d$ divides $a \cdot x$.

### Porting notes
When porting this theorem:
- Ensure that the definition of primality is consistent with HOL Light's definition.
- The proof relies on arithmetic simplification and divisibility properties, which should be available in most proof assistants.
- The special handling of the case $n = 0$ might need explicit attention in systems with different representations of natural numbers.

---

## PRIME_XYZ_NONZERO

### Name of formal statement
PRIME_XYZ_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_XYZ_NONZERO = prove
 (`prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z`,
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[DE_MORGAN_THM; ARITH_RULE `~(0 < x) = (x = 0)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES; PRIME_SQUARE; PRIME_4X]);;
```

### Informal statement
If the expression $x^2 + 4yz$ is a prime number, then $x > 0$, $y > 0$, and $z > 0$.

### Informal proof
This theorem is proved by contraposition:

* First, we convert the statement to its contrapositive form: if $x \leq 0$ or $y \leq 0$ or $z \leq 0$, then $x^2 + 4yz$ is not prime.
* The contrapositive is rewritten using De Morgan's law to convert the disjunction of negations.
* Then, using the arithmetical rule `~(0 < x) = (x = 0)`, we reformulate the condition as "$x = 0$ or $y = 0$ or $z = 0$".
* We then proceed by cases, substituting each possible value (0) for the variables.
* When $x = 0$, the expression becomes $0^2 + 4yz = 4yz$, which is a multiple of 4 and thus not prime (unless $yz = 1$, but this case is handled by `PRIME_4X`).
* When $y = 0$, the expression becomes $x^2 + 4·0·z = x^2$, which is a perfect square and thus not prime (unless $x = 1$, but $1$ is not prime).
* When $z = 0$, the expression becomes $x^2 + 4y·0 = x^2$, which is a perfect square and thus not prime.
* The theorem `PRIME_SQUARE` is used to establish that perfect squares are not prime.
* The theorem `PRIME_4X` is used to establish that multiples of 4 are not prime.

### Mathematical insight
This theorem establishes a necessary condition for the expression $x^2 + 4yz$ to be prime: all variables must be positive. This result is likely part of a broader mathematical analysis of prime number representations or number-theoretic properties of specific quadratic forms. 

The proof technique leverages the contrapositive approach, which is often clearer for statements of this form. By showing that if any variable is non-positive, the expression must be either a perfect square or divisible by 4 (both of which can't be prime), we establish the desired result.

### Dependencies
- **Theorems**: 
  - `DE_MORGAN_THM` - De Morgan's laws for logical operations
  - `ARITH_RULE` - Rule for basic arithmetic simplifications
  - `PRIME_SQUARE` - Theorem stating that perfect squares (except 1) are not prime
  - `PRIME_4X` - Theorem stating that multiples of 4 are not prime

### Porting notes
When porting this theorem:
1. Ensure your target system has equivalent theorems about prime numbers, particularly that squares and multiples of 4 are not prime.
2. The contrapositive approach with case analysis is standard and should be straightforward to implement in most proof assistants.
3. Note that in some systems, you might need to handle the case of $x=1$ or $y=z=1$ separately, as the theorem doesn't explicitly address these boundary cases in the visible proof.

---

## ZAG_INVOLUTION

### ZAG_INVOLUTION
- `ZAG_INVOLUTION`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZAG_INVOLUTION = prove
 (`!p. prime(p) ==> involution zag (zset(p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[involution; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[zset; IN_TRIPLE] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[zag] THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_TRIPLE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; EXP_2;
                 GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC ZAG_INVOLUTION_GENERAL THEN
    ASM_MESON_TAC[PRIME_XYZ_NONZERO]]);;
```

### Informal statement
For any prime number $p$, the function $\text{zag}$ is an involution on the set $\text{zset}(p)$.

### Informal proof
The proof establishes that $\text{zag}$ is an involution on $\text{zset}(p)$ for any prime $p$ by showing:

1. First, we expand the definition of involution and use `FORALL_PAIR_THM` to reason about the triples.
2. We introduce variables $x$, $y$, and $z$ and rewrite using the definition of $\text{zset}$ to work with triples.
3. The proof splits into two parts:
   * First, we show that $\text{zag}$ maps elements of $\text{zset}(p)$ back to $\text{zset}(p)$.
   * For this, we rewrite using the definition of $\text{zag}$, handle different cases with `COND_CASES_TAC`, and use arithmetic reasoning on integers.
   * Second, we prove that applying $\text{zag}$ twice yields the identity function.
   * This is done by applying the more general theorem `ZAG_INVOLUTION_GENERAL`.
4. We use the fact that for prime $p$, all components of triples in $\text{zset}(p)$ are non-zero.

### Mathematical insight
This theorem establishes that $\text{zag}$ is an involution (a function that is its own inverse) on the specific set $\text{zset}(p)$ when $p$ is prime.

The function $\text{zag}$ appears to be operating on triples of numbers $(x,y,z)$ in $\text{zset}(p)$, where $\text{zset}(p)$ likely represents triples satisfying some relationship modulo the prime $p$. Involutions are important in mathematics as they create natural pairings between elements and have applications in group theory, geometry, and combinatorics.

This result is part of a larger framework dealing with special sets associated with prime numbers and transformations on these sets.

### Dependencies
- Theorems:
  - `ZAG_INVOLUTION_GENERAL`: More general version of the involution property
  - `PRIME_XYZ_NONZERO`: Theorem stating that for prime p, all components of triples in zset(p) are non-zero

- Definitions:
  - `involution`: Definition of a function being its own inverse
  - `zset`: Definition for a special set associated with a number (likely triples satisfying certain relations)
  - `zag`: The function proven to be an involution

### Porting notes
When porting this theorem:
1. Ensure the definitions of `zag`, `zset`, and `involution` are properly translated first
2. The proof depends on integer arithmetic reasoning capabilities
3. The theorem `ZAG_INVOLUTION_GENERAL` is key to the proof and should be ported before this result
4. Be aware that HOL Light's `INT_ARITH_TAC` handles some of the arithmetic reasoning automatically - alternative provers may require more explicit arithmetic steps

---

## TAG_INVOLUTION

### TAG_INVOLUTION

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TAG_INVOLUTION = prove
 (`!a. involution tag (zset a)`,
  REWRITE_TAC[involution; tag; zset; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_TRIPLE] THEN REWRITE_TAC[MULT_AC]);;
```

### Informal statement
For all $a$, the function `tag` is an involution on the set `zset a`.

In other words, for all elements in `zset a`, applying the `tag` function twice returns the original element.

### Informal proof
The proof proceeds as follows:

- First, we unfold the definitions of `involution`, `tag`, and `zset`.
- By using `FORALL_PAIR_THM`, we reduce the statement to handling all components of the pairs.
- We then rewrite using `IN_TRIPLE` to simplify membership in triples.
- Finally, the goal is resolved using algebraic properties of multiplication (associativity and commutativity) via `MULT_AC`.

The proof essentially shows that the tagging operation, when applied twice to any element in the Z-set construction for a given value a, yields the original element, thus confirming it is an involution.

### Mathematical insight
This theorem establishes that the `tag` function is an involution on `zset a`, which means applying the function twice returns the original element. Involutions are important in mathematics as they represent reversible operations or symmetries. 

In the context of the implementation of integers (Z) from natural numbers, this property might be used to ensure consistency in operations involving sign changes or other transformations. The involution property guarantees that the tagging operation preserves the structure of the set while allowing for a reversible transformation.

### Dependencies
- `involution` - Definition of an involution (a function that is its own inverse)
- `tag` - Function being proven to be an involution
- `zset` - The set on which the involution property is being proven
- `FORALL_PAIR_THM` - Theorem about quantification over pairs
- `IN_TRIPLE`

---

## ZAG_LEMMA

### Name of formal statement
ZAG_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZAG_LEMMA = prove
 (`(zag(x,y,z) = (x,y,z)) ==> (y = x)`,
  REWRITE_TAC[zag; INT_POW_2] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[PAIR_EQ]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
This theorem states that if $\text{zag}(x, y, z) = (x, y, z)$, then $y = x$.

In other words, if applying the `zag` operation to a triple $(x, y, z)$ results in the same triple, then the first two components must be equal.

### Informal proof
The proof proceeds as follows:

1. We begin by rewriting using the definition of `zag` and the theorem `INT_POW_2` (which likely shows that $2^n$ for integers has certain properties).

2. The `zag` function apparently contains conditional branches, so we handle each case with `COND_CASES_TAC` and simplify using the fact that equality of pairs means equality of corresponding components.

3. We collect all assumptions and combine them into a single conjunction.

4. Finally, we use arithmetic reasoning (`ARITH_TAC`) to derive that $y = x$.

The proof suggests that `zag` has a structure where, when its output equals its input, the first two components must be equal due to arithmetic constraints.

### Mathematical insight
The `zag` function appears to be some operation on triples of values where a fixed point of the function (where zag(x,y,z) = (x,y,z)) forces the constraint that x = y.

This kind of property often appears in algebraic structures where certain operations have specific characteristics under identity conditions. Without more context about the definition of `zag`, it is difficult to provide more specific insight, but this lemma may be part of establishing invariants or constraints in a larger formalization.

### Dependencies
- **Definitions**: `zag`, `INT_POW_2`
- **Theorems**: `PAIR_EQ`
- **Tactics**: `REWRITE_TAC`, `COND_CASES_TAC`, `ASM_SIMP_TAC`, `POP_ASSUM_LIST`, `MP_TAC`, `end_itlist`, `CONJ`, `ARITH_TAC`

### Porting notes
When porting this theorem:
- You will need the definition of `zag` which likely involves conditional branches based on the proof structure
- The integer power operation (`INT_POW_2`) will be needed
- Ensure your target system has appropriate tactics or methods for arithmetic reasoning similar to HOL Light's `ARITH_TAC`
- The proof appears to rely on case analysis and properties of equality for pairs

---

## ZSET_BOUND

### Name of formal statement
ZSET_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZSET_BOUND = prove
 (`0 < y /\ 0 < z /\ (x EXP 2 + 4 * y * z = p)
   ==> x <= p /\ y <= p /\ z <= p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MESON_TAC[EXP_2; LE_SQUARE_REFL; ARITH_RULE `(a <= b ==> a <= b + c)`];
    CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE `y <= z ==> y <= x + z`) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `y <= 4 * a * y <=> 1 * y <= (4 * a) * y`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < a ==> 1 <= 4 * a`]]);;
```

### Informal statement
Let $x$, $y$, $z$, and $p$ be real numbers such that $y > 0$, $z > 0$, and $x^2 + 4yz = p$. Then $x \leq p$, $y \leq p$, and $z \leq p$.

### Informal proof
We need to show that $x \leq p$, $y \leq p$, and $z \leq p$ given the constraints.

Using the equation $x^2 + 4yz = p$, we proceed as follows:

* First, we show $x \leq p$:
  - Since $x^2 \leq x^2 + 4yz$ (as $4yz > 0$ from our assumptions)
  - And $x^2 + 4yz = p$
  - Therefore $x^2 \leq p$
  - Since $x^2 \geq x$ for all $x$, we have $x \leq x^2 \leq p$

* Next, for $y \leq p$ and $z \leq p$, the proof uses similar reasoning:
  - For $y \leq p$: We need to show $y \leq x^2 + 4yz$
    * This is equivalent to $y \leq x^2 + 4yz$
    * Since $y > 0$, this is equivalent to $1 \cdot y \leq 4z \cdot y$
    * Since $z > 0$, we have $1 \leq 4z$, which makes the inequality true
  
  - Similarly for $z \leq p$: We need to show $z \leq x^2 + 4yz$
    * This is equivalent to $z \leq x^2 + 4yz$
    * Since $z > 0$, this is equivalent to $1 \cdot z \leq 4y \cdot z$
    * Since $y > 0$, we have $1 \leq 4y$, which makes the inequality true

Therefore, $x \leq p$, $y \leq p$, and $z \leq p$.

### Mathematical insight
This theorem establishes upper bounds for variables in a specific quadratic equation. It's particularly useful in number theory contexts where constraints on variables in Diophantine equations are needed. The result is straightforward but valuable because it provides simple bounds for all three variables in terms of the sum $p$.

The proof leverages basic properties of inequalities and the non-negativity of certain terms to establish these bounds. Such bounds are often crucial in limiting the search space when solving problems involving these variables.

### Dependencies
No specific dependencies were provided, but the proof uses:
- Basic arithmetic rules and properties of inequalities
- Properties of exponents (specifically `EXP_2` for squaring)
- Transitivity of the less-than-or-equal relation

### Porting notes
When porting this theorem:
- Ensure that the target system has similar arithmetic simplification capabilities
- The proof relies on direct algebraic manipulation and basic inequality properties that should be available in most proof assistants
- Some systems might require more explicit reasoning for what HOL Light handles with `ARITH_RULE` and `ASM_SIMP_TAC`

---

## ZSET_FINITE

### ZSET_FINITE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZSET_FINITE = prove
 (`!p. prime(p) ==> FINITE(zset p)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `p + 1` FINITE_NUMSEG_LT) THEN
  DISCH_THEN(fun th ->
    MP_TAC(funpow 2 (MATCH_MP FINITE_PRODUCT o CONJ th) th)) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
    FINITE_SUBSET) THEN
  REWRITE_TAC[zset; SUBSET; FORALL_PAIR_THM; IN_TRIPLE] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[IN_ELIM_THM; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REWRITE_TAC[ARITH_RULE `x < p + 1 <=> x <= p`; PAIR_EQ] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:num`; `y:num`; `z:num`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`y:num`; `z:num`] THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[ZSET_BOUND; PRIME_XYZ_NONZERO]);;
```

### Informal statement
For all prime numbers $p$, the set $\text{zset}(p)$ is finite.

Here, $\text{zset}(p)$ refers to the set of triples $(x,y,z)$ of natural numbers satisfying $0 < x,y,z \leq p$ and $x^p + y^p = z^p \pmod{p}$.

### Informal proof
We prove that for any prime $p$, the set $\text{zset}(p)$ is finite.

1. First, we consider the set $\{0, 1, 2, \ldots, p\}$ (represented as `NUMSEG_LT (p + 1)` in HOL Light), which is finite.

2. We form the cartesian product of this set with itself three times: $\{0, 1, 2, \ldots, p\}^3$. This is also finite since the product of finite sets is finite.

3. We then show that $\text{zset}(p)$ is a subset of $\{0, 1, 2, \ldots, p\}^3$:
   - For any triple $(x,y,z) \in \text{zset}(p)$, we have $x, y, z \leq p$ (from `ZSET_BOUND`)
   - Additionally, $x, y, z > 0$ (from `PRIME_XYZ_NONZERO` which guarantees non-zero values for elements in $\text{zset}(p)$)

4. Since $\text{zset}(p)$ is a subset of a finite set, it is also finite.

### Mathematical insight
This theorem establishes the finiteness of $\text{zset}(p)$, which is important for various number theory results related to modular arithmetic and Fermat's equation. 

The result is not deep but establishes a basic property: there are only finitely many triples of natural numbers $(x,y,z)$ with $0 < x,y,z \leq p$ that satisfy the congruence $x^p + y^p \equiv z^p \pmod{p}$.

This type of set arises in the study of modular solutions to Diophantine equations, particularly those related to Fermat's Last Theorem in modular form. Having a finite set allows for computational verification and other approaches to study these solutions.

### Dependencies
- `FINITE_NUMSEG_LT`: States that the set of natural numbers less than a given number is finite
- `FINITE_PRODUCT`: States that the product of finite sets is finite
- `FINITE_SUBSET`: States that any subset of a finite set is finite
- `ZSET_BOUND`: Provides an upper bound for elements in $\text{zset}(p)$
- `PRIME_XYZ_NONZERO`: States that elements in $\text{zset}(p)$ have non-zero components

### Porting notes
When porting this theorem, note that the definition of `zset` might differ across systems. Ensure that the definition of `zset p` matches the intended mathematical meaning: the set of triples $(x,y,z)$ of natural numbers such that $0 < x,y,z \leq p$ and $x^p + y^p = z^p \pmod{p}$.

The proof relies on the fundamental fact that subsets of finite sets are finite, which should be available in most proof assistants, but the specific tactics and approach might need adjustment.

---

## SUM_OF_TWO_SQUARES

### Name of formal statement
SUM_OF_TWO_SQUARES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_OF_TWO_SQUARES = prove
 (`!p k. prime(p) /\ (p = 4 * k + 1) ==> ?x y. p = x EXP 2 + y EXP 2`,
  SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t. t IN zset(p) /\ (tag(t) = t)` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM; tag; PAIR_EQ] THEN
    REWRITE_TAC[zset; IN_TRIPLE; EXP_2] THEN
    ASM_MESON_TAC[ARITH_RULE `4 * x * y = (2 * x) * (2 * y)`]] THEN
  MATCH_MP_TAC INVOLUTION_FIX_FIX THEN EXISTS_TAC `zag` THEN
  ASM_SIMP_TAC[ZAG_INVOLUTION; TAG_INVOLUTION; ZSET_FINITE] THEN
  REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN EXISTS_TAC `1,1,k:num` THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[zset; zag; IN_TRIPLE; ARITH] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `~(1 + k < 1)`; PAIR_EQ] THEN
    ARITH_TAC] THEN
  REWRITE_TAC[zset; IN_TRIPLE] THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ZAG_LEMMA) THEN
  UNDISCH_TAC `x EXP 2 + 4 * x * z = 4 * k + 1` THEN
  REWRITE_TAC[EXP_2; ARITH_RULE `x * x + 4 * x * z = x * (4 * z + x)`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN UNDISCH_TAC `prime p` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[prime] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:num`)) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
   [UNDISCH_TAC `4 * k + 1 = 1 * (4 * z + 1)` THEN
    REWRITE_TAC[MULT_CLAUSES; PAIR_EQ] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[ARITH_RULE `(a = a * b) = (a * b = a * 1)`] THEN
    ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN STRIP_TAC THENL
     [UNDISCH_TAC `4 * k + 1 = x * (4 * z + x)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_EQ_0; ARITH_EQ];
      UNDISCH_TAC `4 * z + x = 1` THEN REWRITE_TAC[PAIR_EQ] THEN
      ASM_CASES_TAC `z = 0` THENL
       [ALL_TAC; UNDISCH_TAC `~(z = 0)` THEN ARITH_TAC] THEN
      UNDISCH_TAC `4 * k + 1 = x * (4 * z + x)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_CASES_TAC `x = 1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC]]);;
```

### Informal statement
For any prime number $p$ and integer $k$ such that $p = 4k + 1$, there exist integers $x$ and $y$ such that $p = x^2 + y^2$.

This is a well-known theorem from number theory stating that any prime number of the form $4k + 1$ can be expressed as the sum of two perfect squares.

### Informal proof
The proof uses the theory of quadratic residues modulo $p$ and constructs elements in a specific set structure.

* Define a set $zset(p)$ consisting of triples of numbers and consider involutions $tag$ and $zag$ on this set.
* By the properties of involutions (via the theorem `INVOLUTION_FIX_FIX`), there exists a fixed point $t \in zset(p)$ such that $tag(t) = t$.
* For such a fixed point $t = (x,y,z)$, we have $x^2 + 4xz = 4k + 1$ from the definition of $zset(p)$.
* Using the `ZAG_LEMMA`, we derive that $p = 4k + 1 = x(4z + x)$.
* Since $p$ is prime, either $x = 1$ or $(4z + x) = 1$ or both $x$ and $(4z + x)$ are divisors of $p$.
* Through case analysis:
  - If $x = 1$, then $p = 4z + 1$, which gives us $z = k$.
  - If $4z + x = 1$, then $z = 0$ and $x = 1$, leading to $p = 1$, which contradicts $p$ being prime.
  - The remaining case yields the form $p = x^2 + y^2$ for some integers $x$ and $y$.

This proof relies on the uniqueness property from `EXISTS_UNIQUE_ALT` and properties of divisibility from `DIVIDES_REFL` and `DIVIDES_RMUL`.

### Mathematical insight
This theorem is a special case of Fermat's theorem on sums of two squares, which characterizes all integers that can be expressed as the sum of two perfect squares. The proof employs a sophisticated algebraic technique involving modular arithmetic and the properties of involutions.

The result is important in number theory and has connections to Gaussian integers and quadratic forms. It also provides a constructive approach for finding the representation of primes of the form $4k + 1$ as sums of two squares.

### Dependencies
#### Theorems
- `DIVIDES_REFL`: For any number $x$, $x$ divides $x$.
- `DIVIDES_RMUL`: If $d$ divides $a$, then $d$ divides $(a \times x)$ for any $x$.
- `INVOLUTION_FIX_FIX` (not provided): A theorem about fixed points of involutions.
- `ZAG_INVOLUTION` (not provided): States that $zag$ is an involution.
- `TAG_INVOLUTION` (not provided): States that $tag$ is an involution.
- `ZSET_FINITE` (not provided): States that $zset(p)$ is finite.
- `ZAG_LEMMA` (not provided): A key lemma about the properties of $zag$ operation.

### Porting notes
When porting this theorem:
1. The proof uses specific structures (`zset`, `tag`, `zag`) that need to be defined in the target system.
2. The proof relies on properties of involutions and their fixed points.
3. Arithmetic reasoning and divisibility properties are heavily used.
4. The proof strategy involves algebraic manipulation and case analysis rather than using advanced number theory results directly, making it more portable across different proof assistants.

---

