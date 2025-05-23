# four_squares.ml

## Overview

Number of statements: 36

This file formalizes theorems about representing integers as sums of squares, specifically focusing on representations as sums of two squares and four squares. It proves Fermat's theorem on the sum of two squares (characterizing which integers can be expressed as sums of two squares) and Lagrange's four-square theorem (proving that every natural number can be expressed as the sum of four squares). The file builds on prime number theory and analysis, providing complete formal proofs of these classical number-theoretic results.

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
A function $f$ is an involution on a set $s$ if for all $x \in s$, we have $f(x) \in s$ and $f(f(x)) = x$.

Formally:
$$\text{involution}(f, s) \iff \forall x. x \in s \Rightarrow f(x) \in s \land f(f(x)) = x$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
An involution is a function that acts as its own inverse when applied twice. This is a fundamental concept in mathematics with applications in many areas:

1. In set theory and abstract algebra, involutions are self-inverse functions.
2. In geometry, reflections are examples of involutions.
3. In group theory, involutions correspond to elements of order 2.
4. In computer science, involutions are important for operations that need to be undone in the same way they are done (like toggling states).

The definition captures two essential properties:
- Domain preservation: The function maps elements from the set back into the set
- Self-inverse property: Applying the function twice returns to the original element

This definition appears in the context of theorems about representations of numbers as sums of squares, where certain involutions can help establish properties of these representations.

### Dependencies
None (this is a fundamental definition)

### Porting notes
This is a straightforward definition that should port easily to most proof assistants. When porting:
- Ensure that the function type is properly handled in the target system
- Note that HOL Light's `IN` corresponds to set membership in other systems (e.g., `∈` in Lean or Coq)
- Some systems might prefer a more explicit typing of the function $f$ and set $s$

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
For any function $f$ and set $s$, if $f$ is an involution on $s$ (i.e., $f(f(x)) = x$ for all $x \in s$), then the image of $s$ under $f$ equals $s$ itself:

$$\forall f, s. \text{involution}(f, s) \Rightarrow \text{IMAGE}(f, s) = s$$

### Informal proof
The proof proceeds by first rewriting the goal using the definitions of involution, set extension, and set image. Then, the goal is solved using the MESON automated theorem prover.

More explicitly:
- An involution $f$ on a set $s$ means that $f(f(x)) = x$ for all $x \in s$
- Two sets are equal (by extension) if they contain exactly the same elements
- $x \in \text{IMAGE}(f, s)$ if and only if there exists a $y \in s$ such that $f(y) = x$

With these definitions expanded, MESON can prove that:
- For any $x \in s$, we have $f(x) \in \text{IMAGE}(f, s)$, so $s \subseteq \text{IMAGE}(f, s)$
- For any $x \in \text{IMAGE}(f, s)$, there exists $y \in s$ such that $f(y) = x$. Since $f$ is an involution, $f(f(y)) = y$, so $f(x) = y \in s$, which means $x = f(f(x)) \in \text{IMAGE}(f, s)$, giving $\text{IMAGE}(f, s) \subseteq s$

Therefore, $\text{IMAGE}(f, s) = s$.

### Mathematical insight
This theorem captures a fundamental property of involutions: they preserve the domain on which they operate. An involution is a function that is its own inverse (applying it twice gives the identity function), and such functions necessarily map their domain onto itself.

This result is important in various mathematical contexts where involutions appear, such as group theory (involutory elements have order 2), linear algebra (involutory matrices), and set theory. The result provides a simple but useful characterization: a function is an involution on a set if and only if it maps the set to itself and is self-inverse.

This theorem can be seen as formalizing the intuition that involutions "shuffle" elements within a set but don't add or remove elements.

### Dependencies
- `involution`: Definition of a function being an involution on a set
- `EXTENSION`: Theorem stating that two sets are equal if they have the same elements
- `IN_IMAGE`: Theorem characterizing membership in the image of a set under a function

### Porting notes
When porting this theorem:
- Ensure that your system has a definition of involution that matches HOL Light's: $\forall x \in s, f(f(x)) = x$
- The proof is quite straightforward if your system has good automation for basic set theory
- The theorem may already exist in some form in other libraries, possibly as a property of bijections on a set, since involutions are specific cases of bijections

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
If $f$ is an involution on a set $s$, and $a \in s$ is a fixed point of $f$ (i.e., $f(a) = a$), then $f$ is also an involution on the set $s \setminus \{a\}$ (i.e., $s$ with the element $a$ removed).

Formally: If $f$ is an involution on $s$, $a \in s$, and $f(a) = a$, then $f$ is an involution on $s \setminus \{a\}$.

### Informal proof
The proof unpacks the definition of involution and then uses `MESON_TAC` to complete the inference.

To elaborate:
- We need to show that $f$ remains an involution when restricted to $s \setminus \{a\}$.
- By definition, an involution $f$ on a set $S$ means:
  1. For all $x \in S$, $f(x) \in S$ (closure under $f$)
  2. For all $x \in S$, $f(f(x)) = x$ (applying $f$ twice yields the identity)
- When we remove a fixed point $a$ from $s$:
  - Since $f(a) = a$, removing $a$ doesn't affect the preservation of these properties
  - For all $x \in s \setminus \{a\}$, $x \neq a$ and $f(x) \in s$ (by $f$ being an involution on $s$)
  - If $f(x) = a$, then $f(f(x)) = f(a) = a \neq x$ (since $x \neq a$), which contradicts $f$ being an involution on $s$
  - Therefore, $f(x) \neq a$ for all $x \in s \setminus \{a\}$, meaning $f(x) \in s \setminus \{a\}$
  - The property $f(f(x)) = x$ is preserved for all $x \in s \setminus \{a\}$

### Mathematical insight
This theorem demonstrates a basic property of involutions: removing a fixed point preserves the involution property on the remaining set. The key insight is that a fixed point of an involution can be safely removed without disrupting the involution structure, as the mapping between other elements remains intact.

This result is useful for constructing or modifying involutions by adding or removing fixed points, which has applications in group theory, combinatorics, and computer science. It establishes that the property of being an involution is preserved under certain set operations.

### Dependencies
No specific dependencies were provided, but the proof uses:
- `involution` definition (a function is an involution on a set if it maps the set to itself and applying it twice yields the identity function)
- `IN_DELETE` (characterizes membership in a set with an element deleted)
- `MESON_TAC` (automated reasoning tactic)

### Porting notes
When porting this theorem to another system:
- Ensure the `involution` definition is ported first
- The set difference operation (DELETE in HOL Light) may have different syntax in other systems
- The automated reasoning used here (`MESON_TAC`) is relatively simple, so the proof should be straightforward to reconstruct using similar automation in other systems

---

## INVOLUTION_STEPDOWN

### INVOLUTION_STEPDOWN
- `INVOLUTION_STEPDOWN`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INVOLUTION_STEPDOWN = prove
 (`involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})`,
  REWRITE_TAC[involution; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;
```

### Informal statement
Let $f$ be a function and $s$ be a set. If $f$ is an involution on $s$ and $a \in s$, then $f$ is also an involution on the set $s \setminus \{a, f(a)\}$.

Here, $f$ being an involution on a set $s$ means that for all $x \in s$, we have $f(x) \in s$ and $f(f(x)) = x$.

### Informal proof
The proof is straightforward using the definition of involution and set operations:

Since $f$ is an involution on $s$, we know that:
1. For all $x \in s$, $f(x) \in s$
2. For all $x \in s$, $f(f(x)) = x$

To prove $f$ is an involution on $s \setminus \{a, f(a)\}$, we need to show:
- For any $x \in s \setminus \{a, f(a)\}$, $f(x) \in s \setminus \{a, f(a)\}$
- For any $x \in s \setminus \{a, f(a)\}$, $f(f(x)) = x$

The second condition follows directly from the fact that $f$ is an involution on $s$.

For the first condition, consider $x \in s \setminus \{a, f(a)\}$. This means $x \in s$ but $x \neq a$ and $x \neq f(a)$. Since $f$ is an involution on $s$, we know $f(x) \in s$. We need to show $f(x) \neq a$ and $f(x) \neq f(a)$.

If $f(x) = a$, then $f(f(x)) = f(a)$. But since $f$ is an involution, $f(f(x)) = x$, which would mean $x = f(a)$, contradicting $x \neq f(a)$.

Similarly, if $f(x) = f(a)$, then applying $f$ to both sides and using the involution property: $f(f(x)) = f(f(a))$ implies $x = a$, contradicting $x \neq a$.

Therefore, $f(x) \in s \setminus \{a, f(a)\}$ for any $x \in s \setminus \{a, f(a)\}$, completing the proof.

### Mathematical insight
This theorem shows that we can "step down" from a set where a function is an involution by removing a point and its image. This is useful for inductive arguments or constructions involving involutions.

The key insight is that the properties of an involution ensure that removing a point and its image preserves the involution property on the remaining set. This is because involutions pair up elements in the set (each element with its image), so removing such a pair preserves the pairing structure.

This result could be used in breaking down problems involving involutions into smaller cases or in constructing involutions incrementally.

### Dependencies
- `involution`: The definition of an involution on a set
- `IN_DIFF`: Theorem about set difference membership
- `IN_INSERT`: Theorem about set insertion membership
- `NOT_IN_EMPTY`: Theorem about empty set membership

### Porting notes
When porting this theorem:
- Ensure your definition of involution matches the one used here (a function that maps elements in the set to elements in the set and is its own inverse)
- The proof uses MESON_TAC which is an automated reasoning tactic - this might need to be replaced with explicit reasoning steps in systems with different automation capabilities

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
If $f$ is an involution on a set $s$, then $f$ is also an involution on the subset of $s$ consisting of elements that are not fixed points of $f$.

More precisely, if $f$ is a function such that $f \circ f = \textrm{id}$ on the set $s$, then $f \circ f = \textrm{id}$ on the set $\{x \in s : f(x) \neq x\}$.

### Informal proof
The proof follows directly from the definition of involution. If $f$ is an involution on $s$, then for all $x \in s$, we have $f(f(x)) = x$. 

Since $\{x \in s : f(x) \neq x\} \subseteq s$, the property $f(f(x)) = x$ holds for all elements in this subset as well. Therefore, $f$ is also an involution on $\{x \in s : f(x) \neq x\}$.

### Mathematical insight
This theorem highlights that the involution property is preserved when restricting to the subset of non-fixed points. In the context of involutions, fixed points (where $f(x) = x$) have special significance - they're the elements unaffected by the function. This theorem confirms that removing these fixed points still leaves us with a well-defined involution on the remaining elements.

This result can be useful when studying the structure of involutions, particularly when analyzing their action on different subsets of the domain.

### Dependencies
- `involution`: Definition of a function being an involution on a set
- `IN_ELIM_THM`: Theorem about set membership for sets defined by set-builder notation
- `MESON_TAC`: Automated reasoning tactic

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies on basic set theory and function properties. The main consideration would be ensuring that the definition of an involution is compatible across systems.

---

## INVOLUTION_SUBSET

### Name of formal statement
INVOLUTION_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_SUBSET = prove
 (`!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t`,
  REWRITE_TAC[involution; SUBSET] THEN MESON_TAC[]);;
```

### Informal statement
For any function $f$ and sets $s$ and $t$, if:
1. $f$ is an involution on $s$ (i.e., $f \circ f = \text{id}$ on $s$),
2. $f$ maps elements of $t$ into $t$ (i.e., $\forall x \in t, f(x) \in t$), and
3. $t$ is a subset of $s$ (i.e., $t \subseteq s$),

then $f$ is also an involution on $t$.

### Informal proof
The proof follows directly from the definition of involution and subset relation:

First, we rewrite using the definitions of `involution` and `SUBSET`. An involution on a set means that $f(f(x)) = x$ for all $x$ in the set, and $t \subseteq s$ means that every element of $t$ is also in $s$.

Then, using first-order reasoning (via `MESON_TAC`), we can establish that:
- Since $f$ is an involution on $s$, we have $f(f(x)) = x$ for all $x \in s$
- For any $x \in t$, we know $x \in s$ (since $t \subseteq s$)
- Therefore, $f(f(x)) = x$ for all $x \in t$
- Also, since $f$ maps elements of $t$ back into $t$, we have $f(x) \in t$ for all $x \in t$

These conditions together establish that $f$ is an involution on $t$.

### Mathematical insight
This theorem demonstrates an important property of involutions: they preserve their involution property when restricted to invariant subsets of their domain. An invariant subset here means a subset that is closed under the function application.

This result is useful when working with restricted domains of functions. It allows us to establish that a function remains an involution when we narrow its domain, provided that the narrowed domain is closed under the function's action and is a subset of the original domain.

### Dependencies
- `involution`: Definition of a function being an involution on a set
- `SUBSET`: Definition of subset relation

### Porting notes
When porting this theorem, ensure that your proof assistant has established definitions for:
1. Involutions (functions that are their own inverse when applied twice)
2. Set membership and subset relations

The proof is straightforward and should translate easily to most proof assistants using basic rewriting and first-order reasoning tactics.

---

## INVOLUTION_EVEN

### INVOLUTION_EVEN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_EVEN = prove
 (`!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)`,
  REWRITE_TAC[involution] THEN MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]);;
```

### Informal statement
For any set $s$ and function $f$, if $s$ is finite, $f$ is an involution on $s$ (meaning $f \circ f = \text{id}$ on $s$), and $f$ has no fixed points on $s$ (i.e., $\forall x \in s, f(x) \neq x$), then the cardinality of $s$ is even.

### Informal proof
The proof proceeds by rewriting the definition of `involution` and then using the theorem `INVOLUTION_EVEN_NOFIXPOINTS` which already establishes this result.

In more detail:
- First, the definition of involution is expanded (an involution is a function where applying it twice returns to the original value)
- Then, the theorem `INVOLUTION_EVEN_NOFIXPOINTS` is applied, which directly proves that a finite set with a fixed-point-free involution must have even cardinality.

### Mathematical insight
This theorem captures an important combinatorial property: when a set has a function that pairs its elements (through the involution) with no element paired with itself, the set must contain an even number of elements.

The result is intuitive because an involution without fixed points essentially partitions the set into pairs $(x, f(x))$, where $x \neq f(x)$ and $f(f(x)) = x$. Since each element belongs to exactly one such pair, the total number of elements must be even.

This theorem has applications in various areas of mathematics, including group theory (where involutions are elements of order 2), combinatorics, and the study of permutations.

### Dependencies
- Theorems:
  - `INVOLUTION_EVEN_NOFIXPOINTS`: The main result being used, which establishes that a finite set with a fixed-point-free involution has even cardinality.
- Definitions:
  - `involution`: Defines what it means for a function to be an involution (i.e., $f \circ f = \text{id}$)

### Porting notes
When porting this theorem:
1. Ensure the target system has a definition of involution that captures the property $f \circ f = \text{id}$
2. The dependency `INVOLUTION_EVEN_NOFIXPOINTS` would need to be ported first
3. The concept of a function without fixed points is straightforward ($\forall x \in s, f(x) \neq x$) but might require explicit formalization in some systems

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
If $s$ is a finite set and $f$ is an involution on $s$ with exactly one fixed point (i.e., there exists a unique $a \in s$ such that $f(a) = a$), then the cardinality of $s$ is odd.

### Informal proof
The proof proceeds as follows:

* First we expand the "exists unique" notation and strip the assumptions.
* Let $a \in s$ be the unique fixed point of $f$ (i.e., $f(a) = a$).
* We decompose the set $s$ as $s = \{a\} \cup (s \setminus \{a\})$.
* By the properties of cardinality for finite sets, we have $\text{CARD}(s) = 1 + \text{CARD}(s \setminus \{a\})$.
* Since $a$ is the only fixed point of $f$, the involution $f$ restricted to $s \setminus \{a\}$ has no fixed points.
* By the theorem `INVOLUTION_EVEN`, an involution with no fixed points on a finite set implies that the cardinality of that set is even.
* Therefore, $\text{CARD}(s \setminus \{a\})$ is even.
* Since $\text{CARD}(s) = 1 + \text{CARD}(s \setminus \{a\})$ and $\text{CARD}(s \setminus \{a\})$ is even, it follows that $\text{CARD}(s)$ is odd.

### Mathematical insight
This theorem captures an important structural property of involutions: an involution with exactly one fixed point must act on a domain with odd cardinality. This is a direct consequence of the fact that the non-fixed points must be paired up by the involution.

The result is part of a broader pattern in combinatorial mathematics, where the parity of various structures can be determined by analyzing their symmetries. It is particularly useful in group theory and discrete mathematics when studying permutations and their cycle structures.

Intuitively, you can think of an involution as pairing up elements (each element with its image), except for fixed points which are paired with themselves. If there is exactly one fixed point, all other elements form pairs, making the total count odd.

### Dependencies
#### Theorems:
- `INVOLUTION_EVEN` - Theorem stating that an involution with no fixed points on a finite set implies the set has even cardinality
- `INVOLUTION_DELETE` - Theorem about restricting an involution to a subset by deleting an element
- `CARD_CLAUSES` - Basic theorems about cardinality of finite sets
- `FINITE_DELETE` - Theorem stating that deleting an element from a finite set results in a finite set

#### Definitions:
- `involution` - A function that is its own inverse: $f \circ f = \text{id}$
- `ODD` - Property of a number being odd
- `EXISTS_UNIQUE_DEF` - Definition of unique existence

### Porting notes
When porting this theorem:
1. Ensure your system has a proper definition of involution that matches HOL Light's definition: a function that is its own inverse.
2. The handling of unique existence (`?!`) might differ between systems, so pay attention to how the unique fixed point is described.
3. The theorem relies on `INVOLUTION_EVEN`, so that should be ported first.
4. The proof uses set operations and cardinality properties, which are standard but might have different notation in other systems.

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
For any natural number $n$ and set $s$, if $s$ is finite, $f$ is an involution on $s$, and the cardinality of $s$ is odd, then there exists an element $a \in s$ such that $f(a) = a$.

In other words, an involution on a finite set with odd cardinality must have at least one fixed point.

### Informal proof
The proof is a straightforward application of the previous theorem `INVOLUTION_EVEN`, which states that if $f$ is an involution on a finite set $s$, then the number of elements $a \in s$ such that $f(a) = a$ has the same parity as the cardinality of $s$.

The proof proceeds as follows:
- We rewrite the goal using `GSYM NOT_EVEN`, which transforms `ODD(CARD s)` into `~EVEN(CARD s)`.
- Then we use `MESON_TAC` with `INVOLUTION_EVEN` to complete the proof.

The underlying reasoning is:
- Since `INVOLUTION_EVEN` tells us that the parity of fixed points matches the parity of the set size
- And we know the set size is odd
- Therefore, the number of fixed points must also be odd
- An odd number is always positive (at least 1)
- Hence, there must exist at least one fixed point

### Mathematical insight
This theorem captures an important property of involutions (functions that are their own inverse): they must have fixed points when defined on sets of odd cardinality. This result has applications in various areas of mathematics including group theory, combinatorics, and graph theory.

The result is closely related to the fact that when we decompose the action of an involution into orbits, these orbits are either singletons (fixed points) or pairs. If the total number of elements is odd, there must be at least one singleton orbit.

This theorem and its companion `INVOLUTION_EVEN` form a complete characterization of the parity relationship between a finite set's cardinality and the number of fixed points of any involution on that set.

### Dependencies
- `INVOLUTION_EVEN`: The theorem stating that if $f$ is an involution on a finite set $s$, then the number of elements $a \in s$ such that $f(a) = a$ has the same parity as the cardinality of $s$.
- `GSYM NOT_EVEN`: A rewriting rule that transforms `ODD(CARD s)` into `~EVEN(CARD s)`.

### Porting notes
When porting this theorem:
- Ensure that the definition of involution is correctly established: a function $f$ such that $f \circ f = \text{identity}$
- The proof relies on the parity relationship established in `INVOLUTION_EVEN`, so that theorem should be ported first
- The theorem statement is straightforward and should translate easily across systems

---

## INVOLUTION_FIX_FIX

### INVOLUTION_FIX_FIX

### Type of the formal statement
Theorem

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
For any functions $f$ and $g$ and any set $s$, if:
- $s$ is finite
- $f$ is an involution on $s$ (i.e., $f \circ f = \text{id}$ on $s$)
- $g$ is an involution on $s$ 
- There exists exactly one element $x \in s$ such that $f(x) = x$ (i.e., $f$ has a unique fixed point in $s$)

Then there exists an element $x \in s$ such that $g(x) = x$ (i.e., $g$ also has a fixed point in $s$).

### Informal proof
The proof follows from two other theorems about involutions:

1. First, we apply the theorem `INVOLUTION_ODD`, which states that if $s$ is a finite set and $f$ is an involution on $s$ with an odd number of fixed points, then any other involution $g$ on $s$ must also have at least one fixed point.

2. To use this theorem, we need to show that $f$ has an odd number of fixed points. This is established using the theorem `INVOLUTION_FIX_ODD`, which states that if an involution has exactly one fixed point, then the total number of fixed points is odd.

3. Since we know $f$ has exactly one fixed point (by the hypothesis), we can apply `INVOLUTION_FIX_ODD` to conclude that $f$ has an odd number of fixed points.

4. Then, by `INVOLUTION_ODD`, we can conclude that $g$ must have at least one fixed point.

### Mathematical insight
This theorem establishes an important connection between different involutions on the same finite set. It shows that the property of having fixed points transfers between involutions in specific ways. In particular, if one involution has a unique fixed point, then any other involution on the same set must also have at least one fixed point.

The key insight is that involutions divide sets into orbits of size 1 (fixed points) and size 2 (pairs of elements that map to each other). This structural property creates constraints on the possible number of fixed points - specifically, involutions on finite sets must have a congruent number of fixed points modulo 2. When one involution has exactly one fixed point, the total is odd, which forces other involutions to have at least one fixed point as well.

### Dependencies
- `INVOLUTION_ODD`: Theorem stating that if a finite set has an involution with an odd number of fixed points, then any other involution on the set must also have at least one fixed point.
- `INVOLUTION_FIX_ODD`: Theorem stating that if an involution has exactly one fixed point, then it has an odd number of fixed points in total.

### Porting notes
When porting this theorem, it's important to ensure that the definitions of "involution" and "finite" match those in HOL Light. An involution is typically defined as a function that is its own inverse (i.e., composing it with itself yields the identity function). The uniqueness quantifier "?!" should be properly translated to the target system's equivalent notation for "there exists exactly one."

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
The function $\text{zset}(a)$ is defined as the set of all ordered triples $(x,y,z)$ such that $x^2 + 4yz = a$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition creates a set of all triples $(x,y,z)$ that satisfy the equation $x^2 + 4yz = a$ for a given parameter $a$. This is a key component in Zagier's "one-sentence" proof related to the representation of numbers, particularly in the context of number theory.

The definition is important because it allows for the classification of integers based on whether they can be expressed in the form $x^2 + 4yz$, which connects to various areas of number theory including:
- Representation of integers by quadratic forms
- Properties of sums of squares
- Diophantine equations

The name "zset" likely refers to Don Zagier, a mathematician known for elegant and concise proofs in number theory.

### Dependencies
This definition has no explicit dependencies beyond basic set theory notation and arithmetic operations in HOL Light.

### Porting notes
When porting to another proof assistant:
- Ensure the system has a way to represent sets of tuples
- Verify that exponentiation (`EXP` in HOL Light) is properly defined
- Check if the target system requires explicit type declarations for variables x, y, z, and a

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
The function $\text{zag}$ is defined as a mapping $\text{zag} : \mathbb{R}^3 \to \mathbb{R}^3$ such that for any triple $(x, y, z)$, we have:

$$\text{zag}(x, y, z) = 
\begin{cases}
(x + 2z, z, y - (x + z)), & \text{if } x + z < y \\
(2y - x, y, (x + z) - y), & \text{if } x + z \geq y \text{ and } x < 2y \\
(x - 2y, (x + z) - y, y), & \text{if } x + z \geq y \text{ and } x \geq 2y
\end{cases}$$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The `zag` function appears to define a transformation in three-dimensional space, specifically a transformation that preserves certain properties (likely the sum of coordinates). The function branches into three different cases depending on the relationship between the input coordinates.

The name "zag" suggests this might be part of a "zig-zag" pattern or transformation, possibly used in computational geometry, number theory, or as part of an algorithm related to partitioning or sorting triplets of numbers.

Without additional context, it's difficult to determine the specific mathematical motivation, but such piecewise functions are often used to define canonical forms or normal forms for mathematical objects, or to implement algorithms that progressively transform inputs toward some desired structure.

### Dependencies
None explicitly identified.

### Porting notes
When porting this definition:
- Ensure the target system treats conditional expressions similarly to HOL Light
- Verify that operations on reals (or the expected numeric type) behave the same way
- Pay attention to the precedence of operations in the conditional branches
- The definition uses a straightforward piecewise function pattern, which should be directly expressible in most theorem provers

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
The function $\text{tag} : \mathbb{N} \times \mathbb{N} \times \mathbb{N} \to \mathbb{N} \times \mathbb{N} \times \mathbb{N}$ is defined by:

$$\text{tag}(x, y, z) = (x, z, y)$$

where $x, y, z$ are natural numbers.

### Informal proof
This is a simple definition, so no proof is required.

### Mathematical insight
This definition creates a function that reorders the components of a triple of natural numbers by swapping the second and third components. It takes a triple $(x, y, z)$ and returns the triple $(x, z, y)$.

Such permutation functions are often used in formal systems for implementing data structure transformations, encoding/decoding algorithms, or for proving properties about symmetry and permutation invariance.

### Dependencies
None specified.

### Porting notes
This definition should be straightforward to port to any proof assistant that supports tuples or ordered pairs. The definition simply creates a function that reorders elements in a triple, which is a basic operation in most systems.

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
For positive real numbers $x$, $y$, and $z$, the zag function applied twice returns the original triple:
$$0 < x \land 0 < y \land 0 < z \Rightarrow \text{zag}(\text{zag}(x,y,z)) = (x,y,z)$$

### Informal proof
The proof shows that the zag function is an involution (self-inverse) when applied to positive triples:

1. First, we expand the definition of `zag` in the expression `zag(zag(x,y,z))`.
2. We perform case analysis using `COND_CASES_TAC` to consider all possible branches in the conditional definitions of `zag`.
3. For each case, we simplify using the assumptions from the case analysis.
4. We expand the definition of `zag` again for the inner application.
5. We perform another round of case analysis and simplification with the assumptions.
6. We use `PAIR_EQ` to convert the equality of tuples to component-wise equalities.
7. Finally, we collect all assumptions using `POP_ASSUM_LIST` and solve the resulting arithmetic proof obligations with `ARITH_TAC`.

The key insight is that applying the zag function twice to a triple of positive numbers returns the original triple, regardless of the relative magnitudes of the components.

### Mathematical insight
The `zag` function is an involution on triples of positive real numbers, meaning it is its own inverse. This theorem establishes that applying the function twice returns to the starting point. 

Involutions are important in mathematics as they often represent symmetries or reflections. In this case, the `zag` function likely performs some kind of permutation or transformation on the components of the triple that, when applied twice, cancels out.

The general nature of this theorem (applying to all positive triples) makes it useful for reasoning about the behavior of the `zag` function in broader contexts.

### Dependencies
- Definitions:
  - `zag`: Definition of the zag function (not provided in the input)
- Theorems:
  - `PAIR_EQ`: Equality of pairs means equality of corresponding components

### Porting notes
When implementing this in other systems:
1. Ensure the `zag` function is properly defined first
2. The proof might need different tactics in other systems, but the core approach of case analysis and arithmetic solving should be similar
3. The proof relies on automation for arithmetic reasoning (`ARITH_TAC`), so in systems with weaker automation, explicit arithmetic steps might be needed

---

## IN_TRIPLE

### IN_TRIPLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IN_TRIPLE = prove
 (`(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;
```

### Informal statement
The theorem states that:
$(a, b, c) \in \{(x, y, z) \mid P(x, y, z)\} \Leftrightarrow P(a, b, c)$

This expresses that a triple $(a, b, c)$ belongs to the set of all triples $(x, y, z)$ that satisfy the predicate $P(x, y, z)$ if and only if $P(a, b, c)$ holds.

### Informal proof
The proof proceeds as follows:
- Apply `REWRITE_TAC` with the theorems `IN_ELIM_THM` and `PAIR_EQ` to simplify the goal
  - `IN_ELIM_THM` expands the set membership notation
  - `PAIR_EQ` expands equality of pairs
- Then use `MESON_TAC[]` to complete the proof by automated reasoning

This essentially reduces the statement to the basic definition of set membership in terms of the defining predicate, and then uses automated reasoning to handle the triple structure.

### Mathematical insight
This theorem establishes a fundamental connection between set comprehension notation and predicate satisfaction for triples. It extends similar results for singletons and pairs to the case of triples. Such results are essential for working with sets defined by comprehension, allowing us to convert between membership assertions and direct predicate assertions.

### Dependencies
- Theorems:
  - `IN_ELIM_THM`: A result that relates set membership to the defining predicate
  - `PAIR_EQ`: Theorem about equality of pairs

### Porting notes
When porting to other systems:
- This is straightforward to implement in any system with support for set comprehension
- Some systems might have implicit handling of tuples in set comprehensions, making this theorem either built-in or unnecessary
- In systems with dependent types, the representation of finite tuples may differ, requiring appropriate adjustments

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
For all natural numbers $n$, the square $n^2$ is not a prime number.

Formally: $\forall n \in \mathbb{N}. \neg \text{prime}(n \cdot n)$

### Informal proof
We prove that for any natural number $n$, its square $n^2$ is not a prime number.

* Case 1: If $n = 0$, then $n^2 = 0$, and by `PRIME_0`, we know that 0 is not prime.

* Case 2: If $n = 1$, then $n^2 = 1$, and 1 is not prime by the definition of primality.

* Case 3: If $n > 1$, we show that $n^2$ is not prime by exhibiting a proper divisor. 
  - We take $n$ itself as a divisor of $n^2$.
  - Clearly, $n$ divides $n^2$ (using `DIVIDES_LMUL` and `DIVIDES_REFL`).
  - Since $n > 1$, we have $n < n^2$ (as $n^2 = n \cdot n = n \cdot 1 \cdot n$), so $n$ is a proper divisor of $n^2$.
  - Thus $n^2$ has a proper divisor and cannot be prime.

### Mathematical insight
This theorem establishes the fundamental fact that perfect squares (other than 1) are always composite numbers. This is because any square number $n^2$ with $n > 1$ has at least three distinct divisors: 1, $n$, and $n^2$. The proof leverages the definition of primality, which requires a prime to have exactly two distinct divisors.

This result is part of the elementary theory of prime numbers and is often used when reasoning about the structure of the natural numbers or in number-theoretic algorithms.

### Dependencies
- **Theorems**:
  - `DIVIDES_REFL`: For any number $x$, $x$ divides itself.
  - `PRIME_0`: 0 is not a prime number.
- **Implicit**:
  - `prime`: Definition of primality
  - `DIVIDES_LMUL`: If $a$ divides $b$, then $a$ divides $bc$ for any $c$.
  - `EQ_MULT_LCANCEL`: Cancellation law for multiplication: if $n \neq 0$ and $n \cdot a = n \cdot b$, then $a = b$.

### Porting notes
When porting this theorem, ensure that the definitions of primality align between systems. Some proof assistants might define primality starting from 2 rather than considering the cases of 0 and 1 separately. Also, the divisibility relation may be defined differently across systems.

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
For all natural numbers $n$, $4n$ is not a prime number.

In formal terms, $\forall n. \lnot \text{prime}(4 \cdot n)$, where $\text{prime}(p)$ means that $p$ is a prime number.

### Informal proof
To prove that $4n$ is not prime for any natural number $n$, we need to show that $4n$ is either 1 or has a proper divisor.

* We use the definition of primality, which states that a number $p$ is prime if $p > 1$ and the only divisors of $p$ are 1 and $p$ itself.
* The negation of this gives us that a number is not prime if it equals 1 or if there exists a divisor $d$ such that $1 < d < p$ and $d$ divides $p$.
* We prove that $4n$ is not prime by showing that 2 is a proper divisor of $4n$ for any $n$.
* First, we rewrite $4$ as $2 \cdot 2$.
* Then, $4n = (2 \cdot 2) \cdot n = 2 \cdot (2 \cdot n)$, by associativity of multiplication.
* Since $2$ divides itself (by `DIVIDES_REFL`), and multiplication preserves divisibility (by `DIVIDES_RMUL`), we know that $2$ divides $2 \cdot (2 \cdot n) = 4n$.
* We handle the case where $n = 0$ separately using arithmetic reasoning.
* For $n > 0$, since $2 < 4n$ (as $n > 0$ implies $4n \geq 4$), we have found a proper divisor of $4n$.
* Therefore, $4n$ is not prime for any natural number $n$.

### Mathematical insight
This theorem establishes that multiples of 4 cannot be prime numbers. This is a basic result in number theory related to divisibility properties. The result is straightforward but illustrates an important pattern: numbers with certain structural properties (like being divisible by 4) automatically fail to be prime.

The proof hinges on the fact that any number of the form $4n$ can be written as $2 \cdot (2n)$, which immediately shows that it has 2 as a proper divisor (except when $n=0$, in which case $4n=0$ which is also not prime by definition).

This theorem is part of a larger family of results about the distribution and properties of prime numbers.

### Dependencies
#### Theorems
- `DIVIDES_REFL`: For any number $x$, $x$ divides $x$.
- `DIVIDES_RMUL`: For any numbers $d$, $a$, and $x$, if $d$ divides $a$, then $d$ divides $a \cdot x$.

### Porting notes
When porting this theorem, ensure that:
1. The definition of primality in the target system matches HOL Light's definition
2. Basic arithmetic properties and associativity of multiplication are available
3. The divisibility relation has the required properties (reflexivity and preservation under right multiplication)
4. The system can handle the case distinction for $n=0$ properly

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
If $x^2 + 4yz$ is prime, then $x > 0$, $y > 0$, and $z > 0$.

### Informal proof
We prove this by contraposition. We want to show that if any of $x$, $y$, or $z$ is not positive (i.e., equals zero), then $x^2 + 4yz$ is not prime.

First, we transform the negation of the conclusion using De Morgan's laws and the fact that $\neg(0 < x) \iff (x = 0)$. 

Then for each case where $x = 0$ or $y = 0$ or $z = 0$, we substitute the value and simplify:

- If $x = 0$, then $x^2 + 4yz = 0^2 + 4yz = 4yz$, which is either 0 (if $y=0$ or $z=0$) or a multiple of 4 (if both $y,z \neq 0$)
- If $y = 0$, then $x^2 + 4yz = x^2 + 4 \cdot 0 \cdot z = x^2$, which is a perfect square
- If $z = 0$, then $x^2 + 4yz = x^2 + 4y \cdot 0 = x^2$, which is a perfect square

In all cases, $x^2 + 4yz$ is not prime, using the theorems:
- `PRIME_SQUARE`: a perfect square greater than 1 is not prime
- `PRIME_4X`: a multiple of 4 is not prime

### Mathematical insight
This theorem establishes necessary conditions for $x^2 + 4yz$ to be prime. It shows that if this expression is prime, then all variables must be positive. This is useful in number theory, particularly when studying Diophantine equations and the behavior of prime numbers.

The result is quite intuitive: if any variable is zero, the expression simplifies to either a perfect square or a multiple of 4, neither of which can be prime (except for the special case of 2, which is handled separately by the proof).

### Dependencies
- `DE_MORGAN_THM`: De Morgan's laws for logical negation
- `ARITH_RULE`: Arithmetic simplification rule
- `EXP_2`: Definition/theorem about squaring
- `MULT_CLAUSES`: Basic multiplication properties
- `ADD_CLAUSES`: Basic addition properties
- `PRIME_SQUARE`: Theorem stating that perfect squares greater than 1 are not prime
- `PRIME_4X`: Theorem stating that multiples of 4 are not prime

### Porting notes
When porting this theorem:
- Ensure that the target system has theorems equivalent to `PRIME_SQUARE` and `PRIME_4X`
- The contrapositive approach is standard and should be available in most proof assistants
- The arithmetic simplifications are straightforward and should be supported by standard automation

---

## ZAG_INVOLUTION

### Name of formal statement
ZAG_INVOLUTION

### Type of the formal statement
theorem

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
For every prime number $p$, the function $\text{zag}$ is an involution on the set $\text{zset}(p)$.

In other words, for any prime $p$, the function $\text{zag}$ is a bijection from $\text{zset}(p)$ to itself such that applying $\text{zag}$ twice returns to the original element: $\text{zag}(\text{zag}(x)) = x$ for all $x \in \text{zset}(p)$.

### Informal proof
The proof demonstrates that $\text{zag}$ is an involution on $\text{zset}(p)$ for any prime $p$ by showing:

1. First, we unpack the definition of involution and set up the proof framework:
   - An involution requires that for all $(x,y,z) \in \text{zset}(p)$, two properties hold:
     * $\text{zag}(x,y,z) \in \text{zset}(p)$ (closure property)
     * $\text{zag}(\text{zag}(x,y,z)) = (x,y,z)$ (involution property)

2. For closure, we:
   - Apply the definition of $\text{zag}$
   - Analyze different cases based on the conditions in the $\text{zag}$ function
   - Use arithmetic properties involving integers, exponentiation, multiplication, and subtraction
   - Show that the result of $\text{zag}$ is indeed in $\text{zset}(p)$

3. For the involution property:
   - Apply the more general theorem `ZAG_INVOLUTION_GENERAL`
   - Use the fact that for prime $p$, the components of elements in $\text{zset}(p)$ are non-zero (via `PRIME_XYZ_NONZERO`)

These steps establish that $\text{zag}$ is an involution on $\text{zset}(p)$ when $p$ is prime.

### Mathematical insight
This theorem establishes an important involution property for the $\text{zag}$ function on $\text{zset}(p)$ for prime numbers $p$. 

The $\text{zag}$ function appears to be related to number-theoretic transformations on triples of numbers that satisfy certain properties. Involutions are important in mathematics because they represent reversible operations that return to the original state after being applied twice.

For number theory and algebraic geometry, involutions like this can help establish symmetries and structure within certain sets of number triples. The fact that this property holds specifically for prime numbers suggests connections to deeper number-theoretic properties.

The $\text{zset}(p)$ likely represents triples of numbers with specific relationships modulo the prime $p$, and $\text{zag}$ provides a way to map between such triples while preserving their fundamental structure.

### Dependencies
- `involution`: Definition of what it means for a function to be an involution
- `FORALL_PAIR_THM`: Theorem about universal quantification over pairs
- `zset`: Definition of the set $\text{zset}(p)$ for a prime $p$
- `IN_TRIPLE`: Theorem about membership in a triple
- `zag`: Definition of the $\text{zag}$ function
- `INT_OF_NUM_EQ`, `INT_OF_NUM_ADD`, `INT_OF_NUM_MUL`, `INT_OF_NUM_SUB`: Theorems about integer arithmetic
- `EXP_2`: Theorem about squaring numbers
- `LT_IMP_LE`: Theorem that less-than implies less-than-or-equal-to
- `ZAG_INVOLUTION_GENERAL`: A more general theorem about $\text{zag}$ being an involution
- `PRIME_XYZ_NONZERO`: Theorem stating that elements in $\text{zset}(p)$ for prime $p$ have non-zero components

### Porting notes
When porting this theorem:
1. Ensure the definitions of `zag` and `zset` are ported first, as they are essential for this result
2. The `ZAG_INVOLUTION_GENERAL` theorem appears to be a key dependency and might need to be ported beforehand
3. Pay attention to how integer arithmetic is handled in the target system, particularly conversions between natural numbers and integers
4. The proof uses case analysis on conditions within the `zag` function, which might require different tactics in other systems

---

## TAG_INVOLUTION

### TAG_INVOLUTION
- The theorem name is `TAG_INVOLUTION`.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let TAG_INVOLUTION = prove
 (`!a. involution tag (zset a)`,
  REWRITE_TAC[involution; tag; zset; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_TRIPLE] THEN REWRITE_TAC[MULT_AC]);;
```

### Informal statement
For any value $a$, the function `tag` is an involution on the set `zset a`.

More precisely, for any $a$, the function `tag` is a function that maps each element of `zset a` to another element of `zset a`, and applying `tag` twice to any element of `zset a` returns the original element.

### Informal proof
The proof proceeds as follows:

- The goal is to show that for any $a$, `tag` is an involution on the set `zset a`.
- First, we unfold the definitions of `involution`, `tag`, and `zset` and apply `FORALL_PAIR_THM` to handle the universal quantification over pairs.
- After rewriting with these definitions, we're left with a goal about element membership in triples, which is further simplified using `IN_TRIPLE`.
- Finally, the goal is solved by applying associativity and commutativity properties of multiplication (via `MULT_AC`).

### Mathematical insight
This theorem establishes that the `tag` function, when restricted to `zset a` for any value $a$, is an involution - a function that is its own inverse. In the context of constructing integer arithmetic from pairs of natural numbers, this property is crucial as it allows us to define operations like negation and subtraction in a well-defined way.

The `tag` function likely maps between different representations of the same integer value, and this theorem shows that applying this mapping twice gets back to the original representation.

### Dependencies
- **Definitions**: `involution`, `tag`, `zset`
- **Theorems**: `FORALL_PAIR_THM`, `IN_TRIPLE`, `MULT_AC`

### Porting notes
When porting this theorem, ensure that the corresponding definitions for `tag`, `zset`, and `involution` have matching semantics. The proof relies on algebraic properties of multiplication, so the target system should have equivalent theorems about multiplicative associativity and commutativity.

---

## ZAG_LEMMA

### ZAG_LEMMA
- `ZAG_LEMMA`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZAG_LEMMA = prove
 (`(zag(x,y,z) = (x,y,z)) ==> (y = x)`,
  REWRITE_TAC[zag; INT_POW_2] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[PAIR_EQ]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
If $\text{zag}(x, y, z) = (x, y, z)$, then $y = x$.

This is a property of the `zag` function, which seems to manipulate triples of values based on the relationship between $x$ and $y$.

### Informal proof
The proof follows these steps:

- First, we rewrite using the definition of `zag` and the theorem `INT_POW_2`.
- The definition of `zag` likely contains conditional expressions, as we then process each case with `COND_CASES_TAC` and simplify using the equality of pairs.
- For each case that arises, we extract the assumptions and combine them.
- Finally, we use arithmetic reasoning (`ARITH_TAC`) to deduce that $y = x$ must hold.

This suggests that the `zag` function is defined to behave differently depending on the relationship between $x$ and $y$, and the only way the function can return its input unchanged is if $x$ and $y$ are equal.

### Mathematical insight
This lemma establishes a fixed-point property of the `zag` function: if applying `zag` to a triple leaves it unchanged, then the first two components must be equal.

The function `zag` appears to be some sort of transformation on triples that can only be identity when certain constraints are met. This lemma identifies one such constraint - the equality of the first two components.

### Dependencies
- Theorems:
  - `INT_POW_2` (related to integer powers, specifically squares)
  - `PAIR_EQ` (equality of pairs)
  
- Definitions:
  - `zag` (a function operating on triples)

### Porting notes
When porting this theorem:
- You'll need the proper definition of the `zag` function first
- The proof relies on arithmetic reasoning capabilities, so ensure your target system has similar functionality
- The conditional structure of `zag` will be important to handle correctly

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
Let $x$, $y$, $z$, and $p$ be real numbers such that $0 < y$, $0 < z$, and $x^2 + 4yz = p$. Then $x \leq p$, $y \leq p$, and $z \leq p$.

### Informal proof
We prove that each variable is bounded by $p$, given the assumptions.

1. First, we rewrite our goal using the equation $x^2 + 4yz = p$.

2. For the first inequality ($x \leq p$):
   - We know that $x^2 \geq 0$ for any real number $x$.
   - By our assumption, $p = x^2 + 4yz$.
   - Since $0 < y$ and $0 < z$, we have $4yz > 0$.
   - Thus, $x \leq |x| \leq \sqrt{x^2} = x^2$ (if $|x| \geq 1$) and $x^2 \leq x^2 + 4yz = p$.
   - Therefore, $x \leq p$.

3. For the second inequality ($y \leq p$):
   - We need to show $y \leq x^2 + 4yz$.
   - This is equivalent to showing $y \leq x^2 + 4yz$.
   - Since $y > 0$, this is equivalent to $1 \cdot y \leq (4z) \cdot y$.
   - This holds if and only if $1 \leq 4z$ (by canceling $y$, which is positive).
   - Since $0 < z$, we have $1 \leq 4z$ if $z \geq 1/4$.
   - If $z < 1/4$, the inequality $y \leq p$ still holds because $y \leq 4yz$ is not necessary; 
     we just need $y \leq x^2 + 4yz$, which is true because $x^2 \geq 0$.
   - Therefore, $y \leq p$.

4. For the third inequality ($z \leq p$):
   - Using the same approach as for $y$, but utilizing the commutativity of multiplication:
   - We need to show $z \leq x^2 + 4yz$.
   - By commutativity, $4yz = 4zy$.
   - Again, since $z > 0$, we need $1 \cdot z \leq (4y) \cdot z$, which is equivalent to $1 \leq 4y$.
   - Given that $0 < y$, this holds if $y \geq 1/4$.
   - Similar to the previous case, if $y < 1/4$, we still have $z \leq p$ because $x^2 \geq 0$.
   - Therefore, $z \leq p$.

### Mathematical insight
This theorem establishes upper bounds for variables $x$, $y$, and $z$ in terms of a sum $p$ that involves all three variables. It shows that when these variables are related by the equation $x^2 + 4yz = p$ and both $y$ and $z$ are positive, none of the variables can exceed $p$. 

The result is straightforward but useful in contexts where bounds on variables are needed, particularly in optimization problems or when working with geometric or number-theoretic constraints where variables must satisfy certain relations.

### Dependencies
No explicit dependencies were provided, but the proof uses:
- Basic arithmetic rules (`ARITH_RULE`)
- Properties of exponentiation (`EXP_2`)
- Properties of inequalities (`LE_SQUARE_REFL`, `LE_MULT_RCANCEL`)

### Porting notes
When porting this theorem:
- The proof relies on basic properties of real numbers, exponentiation, and inequalities that should be available in most proof assistants.
- The strategy is straightforward and should translate well to other systems.
- Special attention might be needed for the handling of non-strict inequalities and the manipulation of expressions with mixed operations.

---

## ZSET_FINITE

### ZSET_FINITE
- `ZSET_FINITE`

### Type of the formal statement
- theorem

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
For all integers $p$, if $p$ is prime, then the set $\text{zset}(p)$ is finite.

Here, $\text{zset}(p)$ refers to the set of triples $(x,y,z)$ of integers such that $0 < x,y,z \leq p$ and $x^p + y^p = z^p \mod p^2$.

### Informal proof
The proof shows that $\text{zset}(p)$ is a finite set by establishing that it is a subset of a finite set:

- We start by using `FINITE_NUMSEG_LT` with the value $p+1$ to establish that the set $\{0,1,2,...,p\}$ is finite.
- We then use `FINITE_PRODUCT` twice to show that the Cartesian product $\{0,1,2,...,p\} \times \{0,1,2,...,p\} \times \{0,1,2,...,p\}$ is finite.
- Using `FINITE_SUBSET`, we prove that $\text{zset}(p)$ is finite by showing it's a subset of this Cartesian product.
- To establish this subset relation:
  * We expand the definitions and show that any triple $(x,y,z) \in \text{zset}(p)$ satisfies $x,y,z \leq p$.
  * This follows from `ZSET_BOUND`, which provides the bound on elements in $\text{zset}(p)$.
  * We also use `PRIME_XYZ_NONZERO` to ensure the non-zero property of $x$, $y$, and $z$.

### Mathematical insight
This theorem establishes an important finite property of the set $\text{zset}(p)$, which contains triples of numbers satisfying a modular version of Fermat's equation. The finiteness of this set is a crucial property when analyzing potential counterexamples to Fermat's Last Theorem using modular arithmetic approaches.

The theorem contributes to the broader study of Fermat's Last Theorem and modular approaches to number theory by showing that for any prime $p$, there are only finitely many triples satisfying the condition $x^p + y^p \equiv z^p \pmod{p^2}$ with the constraints that $0 < x,y,z \leq p$.

### Dependencies
- `FINITE_NUMSEG_LT`: States that for any number $n$, the set $\{m : m < n\}$ is finite.
- `FINITE_PRODUCT`: States that the Cartesian product of two finite sets is finite.
- `FINITE_SUBSET`: States that any subset of a finite set is finite.
- `ZSET_BOUND`: Provides bounds on the elements in $\text{zset}(p)$.
- `PRIME_XYZ_NONZERO`: States that elements in $\text{zset}(p)$ have non-zero components.

### Porting notes
When porting this theorem:
- Ensure that the definition of `zset` is properly translated to your target system.
- The proof relies heavily on set operations and finiteness properties, so ensure your target system has analogous theorems for products of finite sets.
- The modular arithmetic aspects of `zset` definition will need careful attention, especially if the target system handles congruences differently.

---

## SUM_OF_TWO_SQUARES

### SUM_OF_TWO_SQUARES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that every prime number $p$ of the form $p = 4k + 1$, where $k$ is a natural number, can be expressed as the sum of two squares. Formally:

$$\forall p, k. \text{prime}(p) \land (p = 4k + 1) \Rightarrow \exists x, y. p = x^2 + y^2$$

Where $\text{prime}(p)$ indicates that $p$ is a prime number, and $x^2 + y^2$ represents the sum of two perfect squares.

### Informal proof
The proof employs the theory of quadratic residues and applies an involution technique on a carefully constructed set.

- We begin by constructing a set called `zset(p)` and applying an involution argument. We want to show there exists an element $t$ in `zset(p)` such that $\text{tag}(t) = t$.

- To achieve this, we apply `INVOLUTION_FIX_FIX` with the involution `zag`. We need to show that `zag` is indeed an involution on `zset(p)` and that the set is finite.

- Next, we identify a specific element $(1,1,k)$ that belongs to `zset(p)` and show it's unique with certain properties.

- When we apply the involution `zag` to elements of `zset(p)`, we obtain a relation $x^2 + 4xz = 4k + 1$.

- Using properties of prime numbers, particularly that $p = 4k + 1$:
  - We rewrite the equation as $x(4z + x) = 4k + 1$
  - Since $p$ is prime and divides the product $x(4z + x)$, it must divide at least one of the factors
  - We consider the cases:
    - If $p$ divides $x$, we reach a contradiction
    - If $p$ divides $(4z + x)$, we show this implies $4z + x = 1$ and $x = 1$, with $z = 0$

- This gives us the desired result, as the existence of this fixed point under the involution implies the existence of the representation of $p$ as a sum of two squares.

The proof relies on properties of modular arithmetic and the structure of numbers of the form $4k + 1$.

### Mathematical insight
This theorem is a special case of Fermat's theorem on sums of two squares, which characterizes exactly which positive integers can be expressed as the sum of two squares. The proof uses a clever construction involving an involution (a function that is its own inverse) on a specially designed set. The key insight is to use properties of quadratic residues modulo a prime $p$ of form $4k+1$ to establish the existence of appropriate $x$ and $y$.

This result is significant in number theory as it provides a concrete characterization for a subset of primes. More generally, it connects to the study of quadratic forms and the representation of integers, which has applications in cryptography and coding theory.

### Dependencies
#### Theorems:
- `DIVIDES_REFL`: States that every number divides itself: $\forall x. x \text{ divides } x$
- `DIVIDES_RMUL`: If $d$ divides $a$, then $d$ divides $a \cdot x$: $\forall d, a, x. d \text{ divides } a \Rightarrow d \text{ divides } (a \cdot x)$
- `INVOLUTION_FIX_FIX`: A theorem about fixed points of involutions (not listed in dependencies, but used)
- `ZAG_INVOLUTION`: States that `zag` is an involution (not listed in dependencies)
- `TAG_INVOLUTION`: States that `tag` is an involution (not listed in dependencies)
- `ZSET_FINITE`: States that `zset` is finite (not listed in dependencies)
- `ZAG_LEMMA`: A lemma about the behavior of `zag` (not listed in dependencies)

### Porting notes
When porting this theorem to another system, careful attention should be paid to:

1. The definition of the `zset`, `tag`, and `zag` functions, which are crucial for the proof but not provided in the dependencies.
2. The handling of the involution argument, which may require different techniques in other proof assistants.
3. The representation of modular arithmetic concepts, which might have different standard libraries in other systems.
4. The automation used in the HOL Light proof (particularly `ASM_MESON_TAC` and `ARITH_TAC`) may need to be replaced with appropriate tactics in the target system.

---

## PIGEONHOLE_LEMMA

### Name of formal statement
PIGEONHOLE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PIGEONHOLE_LEMMA = prove
 (`!f:A->B g s t.
        FINITE(s) /\ FINITE(t) /\
        (!x. x IN s ==> f(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) /\
        (!x. x IN s ==> g(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y)) /\
        CARD(t) < 2 * CARD(s)
        ==> ?x y. x IN s /\ y IN s /\ (f x = g y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:A->B) s`; `IMAGE (g:A->B) s`] CARD_UNION) THEN
  SUBGOAL_THEN `(CARD(IMAGE (f:A->B) s) = CARD s) /\
                (CARD(IMAGE (g:A->B) s) = CARD s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CARD_IMAGE_INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MATCH_MP_TAC(TAUT `(~a ==> c) /\ ~b ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `!t. t < 2 * s /\ p <= t ==> ~(p = s + s)`) THEN
  EXISTS_TAC `CARD(t:B->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
For any functions $f : A \to B$ and $g : A \to B$, and sets $s \subseteq A$ and $t \subseteq B$, if:
- $s$ and $t$ are finite sets
- $\forall x \in s, f(x) \in t$
- $\forall x, y \in s, f(x) = f(y) \implies x = y$ (i.e., $f$ is injective on $s$)
- $\forall x \in s, g(x) \in t$
- $\forall x, y \in s, g(x) = g(y) \implies x = y$ (i.e., $g$ is injective on $s$)
- $|t| < 2 \cdot |s|$

Then there exist $x, y \in s$ such that $f(x) = g(y)$.

### Informal proof
The proof proceeds by contradiction using a cardinality argument:

1. First, we establish that $|f[s]| = |s|$ and $|g[s]| = |s|$ using the injectivity of $f$ and $g$ on $s$.

2. We consider the cardinality of the union $|f[s] \cup g[s]|$ using the formula:
   $|f[s] \cup g[s]| = |f[s]| + |g[s]| - |f[s] \cap g[s]|$

3. We need to show $f[s] \cap g[s] \neq \emptyset$ (i.e., there exists some element in the intersection). This is equivalent to finding $x, y \in s$ such that $f(x) = g(y)$.

4. Suppose for contradiction that $f[s] \cap g[s] = \emptyset$.
   - Then $|f[s] \cup g[s]| = |f[s]| + |g[s]| = |s| + |s| = 2 \cdot |s|$
   - Since $f[s] \cup g[s] \subseteq t$, we know $|f[s] \cup g[s]| \leq |t|$
   - Therefore, $2 \cdot |s| \leq |t|$
   - This contradicts our assumption that $|t| < 2 \cdot |s|$

5. Thus, $f[s] \cap g[s] \neq \emptyset$, which means there exist $x, y \in s$ such that $f(x) = g(y)$.

### Mathematical insight
This theorem is a generalized version of the pigeonhole principle. The standard pigeonhole principle states that if $n$ items are placed into $m$ containers, and $n > m$, then at least one container must contain more than one item.

In this version, we have two different injective functions $f$ and $g$ mapping elements from set $s$ into set $t$. If the target set $t$ has fewer than $2|s|$ elements, then the images of $f$ and $g$ must overlap. This happens because $f$ and $g$ each map $|s|$ distinct elements into $t$, and if their images didn't overlap, we would need at least $2|s|$ elements in $t$.

This result has applications in combinatorics and algorithm analysis, particularly in problems involving duplicate detection or collision finding.

### Dependencies
This theorem uses results about cardinality of finite sets and their operations:
- `CARD_IMAGE_INJ` - Relates the cardinality of an injective image to original set
- `CARD_UNION` - Formula for cardinality of union of sets
- `CARD_SUBSET` - Result about cardinality of a subset
- `FINITE_IMAGE` - Image of a finite set is finite

### Porting notes
When porting this theorem:
- Ensure your target system has a well-developed finite set theory with cardinality operations
- The proof relies on arithmetical reasoning about set cardinalities, so check that the target system can handle such reasoning
- The contradiction approach might need adaptation depending on how the target system prefers to structure such proofs

---

## PIGEONHOLE_LEMMA_P12

### Name of formal statement
PIGEONHOLE_LEMMA_P12

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PIGEONHOLE_LEMMA_P12 = prove
 (`!f g p.
        ODD(p) /\
        (!x. 2 * x < p ==> f(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y)) /\
        (!x. 2 * x < p ==> g(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (g x = g y) ==> (x = y))
        ==> ?x y. 2 * x < p /\ 2 * y < p /\ (f x = g y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
  MP_TAC(ISPECL [`f:num->num`; `g:num->num`;
                 `{x:num | 2 * x < 2 * k + 1}`; `{x:num | x < 2 * k + 1}`]
         PIGEONHOLE_LEMMA) THEN
  REWRITE_TAC[ADD1; ARITH_RULE `2 * x < 2 * k + 1 <=> x < k + 1`] THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `2 * k + 1 < 2 * (k + 1)`]);;
```

### Informal statement
For any functions $f$ and $g$ and an odd number $p$, if the following conditions hold:
- $p$ is odd
- For all $x$ such that $2x < p$, we have $f(x) < p$
- For all $x,y$ such that $2x < p$ and $2y < p$, if $f(x) = f(y)$ then $x = y$ (i.e., $f$ is injective on $\{x : 2x < p\}$)
- For all $x$ such that $2x < p$, we have $g(x) < p$
- For all $x,y$ such that $2x < p$ and $2y < p$, if $g(x) = g(y)$ then $x = y$ (i.e., $g$ is injective on $\{x : 2x < p\}$)

Then there exist $x$ and $y$ such that $2x < p$, $2y < p$, and $f(x) = g(y)$.

### Informal proof
The proof uses the pigeonhole principle:

- First, we rewrite the condition that $p$ is odd using the `ODD_EXISTS` theorem, which means there exists a $k$ such that $p = 2k + 1$.

- We instantiate the `PIGEONHOLE_LEMMA` with:
  * Functions $f$ and $g$
  * Domain $\{x : 2x < 2k + 1\}$, which equals $\{x : x < k + 1\}$
  * Codomain $\{x : x < 2k + 1\}$

- We simplify the arithmetic conditions: 
  * $2x < 2k + 1$ is equivalent to $x < k + 1$
  * We have $|{x : x < k + 1}| = k + 1$ elements in the domain
  * The codomain has $2k + 1$ elements
  
- Since both $f$ and $g$ are injective on this domain, and the domain has $k+1$ elements, the images $f(\{x : x < k + 1\})$ and $g(\{x : x < k + 1\})$ each have exactly $k+1$ elements.

- The total number of elements in both image sets is $2(k+1) = 2k + 2$, which is greater than $2k + 1$, the size of the codomain.

- By the pigeonhole principle, there must be some element in the intersection of the two image sets, meaning there exist $x, y$ such that $f(x) = g(y)$ with $2x < p$ and $2y < p$.

### Mathematical insight
This theorem is applying the pigeonhole principle in a modular arithmetic context. It shows that for an odd number $p$, if we have two injective functions mapping from the set $\{0,1,...,\lfloor\frac{p-1}{2}\rfloor\}$ to $\{0,1,...,p-1\}$, then their images must have a non-empty intersection.

This result is particularly useful in number theory, especially in the context of modular arithmetic and when working with quadratic residues. The fact that we're working with the restricted domain where $2x < p$ is significant because for odd $p$, this represents precisely half of the elements in the modular field $\mathbb{Z}_p$.

### Dependencies
- `ODD_EXISTS`: Theorem showing that odd numbers can be written as $2k + 1$ for some $k$
- `PIGEONHOLE_LEMMA`: The standard pigeonhole principle theorem
- `FINITE_NUMSEG_LT`: Theorem stating that sets of the form $\{x : x < n\}$ are finite
- `CARD_NUMSEG_LT`: Theorem giving the cardinality of sets of the form $\{x : x < n\}$
- `ARITH_RULE`: Arithmetic simplification rules

### Porting notes
When porting this theorem:
- Ensure the target system has a good representation of the pigeonhole principle
- Be careful with the arithmetic manipulations, especially the conversion between $2x < 2k + 1$ and $x < k + 1$
- The proof relies on set cardinality arguments, so ensure the target system has adequate support for finite sets and cardinality reasoning

---

## SQUAREMOD_INJ_LEMMA

### Name of formal statement
SQUAREMOD_INJ_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUAREMOD_INJ_LEMMA = prove
 (`!p x d. prime(p) /\ 2 * (x + d) < p /\
           ((x + d) * (x + d) + m * p = x * x + n * p)
           ==> (d = 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides d \/ p divides (2 * x + d)` MP_TAC THENL
   [MATCH_MP_TAC PRIME_DIVPROD THEN ASM_REWRITE_TAC[divides] THEN
    EXISTS_TAC `n - m:num` THEN REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE `!a:num. (a + b + d = a + c) ==> (b = c - d)`) THEN
    EXISTS_TAC `x * x:num` THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN(MP_TAC o MATCH_MP DIVIDES_LE)) THEN
    SIMP_TAC[ADD_EQ_0] THEN UNDISCH_TAC `2 * (x + d) < p` THEN ARITH_TAC]);;
```

### Informal statement
For any prime number $p$, integers $x$ and $d$, and integers $m$ and $n$, if:
1. $p$ is prime
2. $2(x + d) < p$
3. $(x + d)^2 + m \cdot p = x^2 + n \cdot p$

Then $d = 0$.

### Informal proof
We prove this by showing that either $p$ divides $d$ or $p$ divides $(2x + d)$, and then showing that in either case, we must have $d = 0$.

* First, we show that $p$ divides $d \cdot (2x + d)$:
  - From the given equation $(x + d)^2 + m \cdot p = x^2 + n \cdot p$
  - Expanding $(x + d)^2 = x^2 + 2xd + d^2$
  - Rearranging, we get $x^2 + 2xd + d^2 + m \cdot p = x^2 + n \cdot p$
  - Further simplifying: $2xd + d^2 = (n - m) \cdot p$
  - So $d \cdot (2x + d) = (n - m) \cdot p$
  - Thus, $p$ divides $d \cdot (2x + d)$

* Since $p$ is prime and divides the product $d \cdot (2x + d)$, by the theorem `PRIME_DIVPROD`, we have:
  - Either $p$ divides $d$ or $p$ divides $(2x + d)$

* Case 1: If $p$ divides $d$, then $d \geq p$ or $d = 0$
  - But if $d \geq p$, then $2(x + d) \geq 2d \geq 2p > p$, contradicting our hypothesis that $2(x + d) < p$
  - Therefore, $d = 0$

* Case 2: If $p$ divides $(2x + d)$, then $2x + d \geq p$ or $2x + d = 0$
  - If $2x + d \geq p$, then $2(x + d) = 2x + 2d > 2x + d \geq p$, contradicting our hypothesis that $2(x + d) < p$
  - If $2x + d = 0$, then $d = -2x$, which implies $x + d = x - 2x = -x$, and thus $2(x + d) = 2(-x) = -2x = d$
  - But we know $2(x + d) < p$, so $d < p$
  - Since $p$ divides $d$ and $0 \leq d < p$, we must have $d = 0$

Therefore, in all cases, $d = 0$.

### Mathematical insight
This lemma proves an injectivity property for the quadratic function $f(x) = x^2 \bmod p$ when restricted to certain ranges. Specifically, it shows that if $(x+d)^2 \equiv x^2 \pmod{p}$ and $2(x+d) < p$, then $d = 0$. 

The result is important for cryptographic applications, particularly for quadratic residues in modular arithmetic. It shows that the square function is injective on certain intervals modulo a prime, which is a key property used in number-theoretic algorithms and cryptographic protocols.

This lemma is likely used as part of a larger proof related to the structure of quadratic residues modulo primes, which has applications in quadratic reciprocity, primality testing, and cryptography.

### Dependencies
- Theorems:
  - `PRIME_DIVPROD`: If a prime $p$ divides a product $a \cdot b$, then $p$ divides $a$ or $p$ divides $b$

### Porting notes
When porting to another system:
- The proof relies heavily on arithmetic manipulation and the fundamental property of prime numbers dividing products.
- The system needs to handle modular arithmetic and have good automation for arithmetic reasoning.
- The `ARITH_RULE` and `ARITH_TAC` tactics in HOL Light handle the arithmetic reasoning automatically - other systems may require more explicit steps for these calculations.

---

## SQUAREMOD_INJ

### Name of formal statement
SQUAREMOD_INJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUAREMOD_INJ = prove
 (`!p. prime(p)
   ==> (!x. 2 * x < p ==> (x EXP 2 + a) MOD p < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\
              ((x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p)
              ==> (x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `x < a ==> ~(a = 0)`)) THEN
  ASM_SIMP_TAC[DIVISION] THEN
  SUBGOAL_THEN
   `(x EXP 2 + a = (x EXP 2 + a) DIV p * p + (x EXP 2 + a) MOD p) /\
    (y EXP 2 + a = (y EXP 2 + a) DIV p * p + (y EXP 2 + a) MOD p)`
  MP_TAC THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(x2 + a = xp + b:num) /\ (y2 + a = yp + b)
    ==> (x2 + yp = y2 + xp)`)) THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`x:num`; `y:num`] LE_CASES) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS])
  THENL [ONCE_REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
  REWRITE_TAC[EXP_2; ARITH_RULE `(x + d = x) = (d = 0)`] THEN
  ASM_MESON_TAC[SQUAREMOD_INJ_LEMMA]);;
```

### Informal statement
For any prime number $p$, the following two conditions hold:
1. For all $x$ such that $2x < p$, we have $(x^2 + a) \bmod p < p$
2. For all $x, y$ such that $2x < p$ and $2y < p$, if $(x^2 + a) \bmod p = (y^2 + a) \bmod p$, then $x = y$

This theorem establishes that the mapping $x \mapsto (x^2 + a) \bmod p$ is injective on the set $\{x \in \mathbb{N} \mid 2x < p\}$.

### Informal proof
This proof establishes the injectivity of the square mapping modulo a prime $p$:

* We begin by taking a prime $p$ and proving both parts of the conjunction.
* The first part $(x^2 + a) \bmod p < p$ follows immediately from the definition of the modulo operation.
* For the second part (injectivity), we assume $2x < p$, $2y < p$, and $(x^2 + a) \bmod p = (y^2 + a) \bmod p$.
* From the prime assumption, we derive that $p \neq 0$.
* We apply the division theorem to get:
  * $x^2 + a = (x^2 + a) \text{ DIV } p \cdot p + (x^2 + a) \bmod p$
  * $y^2 + a = (y^2 + a) \text{ DIV } p \cdot p + (y^2 + a) \bmod p$
* Since the modulo terms are equal by assumption, we can derive:
  * $x^2 + (y^2 + a) \text{ DIV } p \cdot p = y^2 + (x^2 + a) \text{ DIV } p \cdot p$
* We consider two cases:
  * Case 1: $x \leq y$. We write $y = x + d$ for some $d$.
  * Case 2: $y < x$. We handle this symmetrically.
* In the first case, after substitution, the equation simplifies to $d = 0$, which means $x = y$.
* The theorem is completed by using a lemma called `SQUAREMOD_INJ_LEMMA` (not provided), which likely handles the core number-theoretic reasoning about squares modulo a prime.

### Mathematical insight
This theorem establishes a fundamental property in modular arithmetic: the squaring function modulo a prime has an injective property on a restricted domain. Specifically, when considering values less than half the prime, the function $f(x) = (x^2 + a) \bmod p$ is injective.

This kind of result is important in number theory and cryptography. For instance, it relates to properties of quadratic residues and can be relevant in cryptographic schemes that rely on the difficulty of finding square roots modulo a prime. The restriction $2x < p$ is necessary, as without it, we would have $f(x) = f(p-x)$ for many values.

The theorem could be used as a building block for more complex results about modular arithmetic and quadratic congruences.

### Dependencies
- `DIVISION`: The theorem about division algorithm
- `SQUAREMOD_INJ_LEMMA`: A lemma used in the proof, likely establishing key properties of squares modulo a prime
- `ARITH_RULE`: An arithmetic reasoning function
- `LE_CASES`: A theorem about the cases of less than or equal relation
- `LE_EXISTS`: A theorem that expresses "less than or equal" in terms of existence

### Porting notes
When porting this theorem:
1. Ensure that modulo and division operations are consistently defined in the target system
2. The dependent lemma `SQUAREMOD_INJ_LEMMA` will need to be ported first
3. Be aware of potential differences in how arithmetic is handled in the target system
4. In some systems, it might be more natural to define this result in terms of congruence relations rather than explicit modulo operations

---

## REFLECT_INJ

### REFLECT_INJ
- REFLECT_INJ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REFLECT_INJ = prove
 (`(!x. 2 * x < p ==> f(x) < p) /\
   (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y))
   ==> (!x. 2 * x < p ==> p - 1 - f(x) < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\ (p - 1 - f(x) = p - 1 - f(y))
              ==> (x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * x < p ==> p - 1 - y < p`] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE
   `x < p /\ y < p /\ (p - 1 - x = p - 1 - y) ==> (x = y)`) THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
Given a function $f$ and a number $p$, if:
1. For all $x$ such that $2x < p$, we have $f(x) < p$
2. For all $x, y$ such that $2x < p$ and $2y < p$, if $f(x) = f(y)$ then $x = y$

Then the reflected function $g(x) = p - 1 - f(x)$ satisfies:
1. For all $x$ such that $2x < p$, we have $g(x) < p$
2. For all $x, y$ such that $2x < p$ and $2y < p$, if $g(x) = g(y)$ then $x = y$

### Informal proof
We need to prove two claims about the reflected function $g(x) = p - 1 - f(x)$:

1. First claim: For all $x$ such that $2x < p$, we have $g(x) < p$.
   - This follows directly from arithmetic. If $2x < p$, then $p - 1 - f(x) < p$ for any value of $f(x)$.
   - This is established by the application of the arithmetic rule `2 * x < p ==> p - 1 - y < p`.

2. Second claim: For all $x, y$ such that $2x < p$ and $2y < p$, if $g(x) = g(y)$ then $x = y$.
   - Assume $2x < p$, $2y < p$, and $g(x) = g(y)$.
   - Then $p - 1 - f(x) = p - 1 - f(y)$.
   - From the arithmetic rule `x < p /\ y < p /\ (p - 1 - x = p - 1 - y) ==> (x = y)`, we can conclude that $f(x) = f(y)$.
   - From our initial assumption about $f$ being injective (second premise), we get $x = y$.

### Mathematical insight
This theorem shows that reflection of an injective function that maps elements satisfying $2x < p$ to values less than $p$ preserves both the range constraint and injectivity. This is useful in modular arithmetic contexts, particularly in number theory and cryptography where reflections of functions (like $g(x) = p - 1 - f(x)$) are common operations.

The reflection operation is essentially taking the "complement" with respect to $p-1$. This theorem confirms that this operation preserves important properties of functions in modular contexts, which is crucial for constructing functions with specific behaviors in finite fields or rings.

### Dependencies
No explicit dependencies were provided, but the theorem uses:
- `ARITH_RULE` for arithmetic reasoning
- Basic logical operations in HOL Light

### Porting notes
When porting this theorem:
- Ensure the target system has appropriate arithmetic reasoning capabilities
- The theorem is essentially about arithmetic properties of functions, so it should translate straightforwardly to other proof assistants
- Take care with the interpretation of inequalities (<) on different number types in the target system

---

## LAGRANGE_LEMMA_ODD

### LAGRANGE_LEMMA_ODD
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LAGRANGE_LEMMA_ODD = prove
 (`!a p. prime(p) /\ ODD(p)
         ==> ?n x y. 2 * x < p /\ 2 * y < p /\
                     (n * p = x EXP 2 + y EXP 2 + a + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (x EXP 2 + a) MOD p`;
                 `\x. p - 1 - (x EXP 2 + 0) MOD p`; `p:num`]
                PIGEONHOLE_LEMMA_P12) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `(a /\ b) /\ (c /\ d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REFLECT_INJ] THEN
    ASM_MESON_TAC[SQUAREMOD_INJ]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `(x = p - 1 - y) ==> y < p ==> (x + y + 1 = p)`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(MOD)`) THEN
  SUBGOAL_THEN
   `((x EXP 2 + a) MOD p + (y EXP 2 + 0) MOD p + 1) MOD p =
    (x EXP 2 + y EXP 2 + a + 1) MOD p`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
    EXISTS_TAC `(x EXP 2 + a) DIV p + (y EXP 2) DIV p` THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
      `(x2 + a = xd * p + xm) /\ (y2 = yd * p + ym)
       ==> (x2 + y2 + a + 1 = (xm + ym + 1) + (xd + yd) * p)`) THEN
    ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
  SUBGOAL_THEN `p MOD p = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`(x EXP 2 + y EXP 2 + a + 1) DIV p`; `x:num`; `y:num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x EXP 2 + y EXP 2 + a + 1` o
    MATCH_MP DIVISION) THEN
 ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN MESON_TAC[]);;
```

### Informal statement
For any integer $a$ and any odd prime $p$, there exist natural numbers $n$, $x$, and $y$ such that:
- $2x < p$
- $2y < p$
- $np = x^2 + y^2 + a + 1$

This is a lemma related to Lagrange's four-square theorem.

### Informal proof
The proof proceeds as follows:

- First, we establish that $p \neq 0$ (which follows from $p$ being a prime).
- We apply the pigeonhole principle (`PIGEONHOLE_LEMMA_P12`) to the functions:
  - $f(x) = (x^2 + a) \bmod p$
  - $g(x) = p - 1 - (x^2) \bmod p$
  
- We need to show these functions are injective within their domains. This follows from the fact that for a prime $p$, the square modulo function is injective on the range $[0, \frac{p-1}{2}]$.

- The pigeonhole principle gives us values $x$ and $y$ such that $f(x) = g(y)$, which means:
  $(x^2 + a) \bmod p = p - 1 - (y^2) \bmod p$

- This can be rearranged to show that:
  $(x^2 + a) + (y^2) + 1 \equiv 0 \pmod{p}$
  
- Therefore, $p$ divides $x^2 + y^2 + a + 1$, which means there exists some $n$ such that:
  $np = x^2 + y^2 + a + 1$

- The bounds $2x < p$ and $2y < p$ are preserved throughout the proof based on the domains of the functions used in the pigeonhole principle.

### Mathematical insight
This lemma is a key step in proving Lagrange's four-square theorem, which states that every natural number can be expressed as the sum of four integer squares. 

The result establishes that for any odd prime $p$ and integer $a$, we can find $x$ and $y$ within specific bounds such that $x^2 + y^2 + a + 1$ is divisible by $p$. This divisibility property is crucial in the construction used to prove the four-square theorem.

The proof uses a clever application of the pigeonhole principle with carefully chosen functions. By working in modular arithmetic and exploiting properties of squares modulo prime numbers, it establishes the existence of a representation with specific constraints.

### Dependencies
- `PIGEONHOLE_LEMMA_P12`: A lemma applying the pigeonhole principle to functions with specific constraints
- `SQUAREMOD_INJ`: A theorem about injectivity of the square function in modular arithmetic
- `REFLECT_INJ`: A result about injectivity of reflection functions
- `DIVISION`: The division theorem for integers
- `MOD_EQ`: A theorem about equality of expressions in modular arithmetic
- `MOD_UNIQ`: Uniqueness of modular representation

### Porting notes
When porting this theorem:
- Ensure your target system has a well-developed theory of modular arithmetic
- The proof relies heavily on properties of primes and square functions modulo primes
- The explicit manipulation of division and modulus operations might need careful translation in systems with different arithmetic representations
- Ensure your target system can handle the specific form of the pigeonhole principle used here

---

## LAGRANGE_LEMMA

### Name of formal statement
LAGRANGE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LAGRANGE_LEMMA = prove
 (`!a p. prime(p)
         ==> ?n x y. 2 * x <= p /\ 2 * y <= p /\
                     (n * p = x EXP 2 + y EXP 2 + a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `EVEN(p)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [prime]) THEN
    DISCH_THEN(MP_TAC o SPEC `2` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[EVEN_EXISTS; divides]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `EVEN(a)` THENL
     [UNDISCH_TAC `EVEN a` THEN REWRITE_TAC[EVEN_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `0`; `0`] THEN
      REWRITE_TAC[ARITH; ADD_CLAUSES] THEN ARITH_TAC;
      UNDISCH_TAC `~(EVEN(a))` THEN REWRITE_TAC[NOT_EVEN; ODD_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`k + 1`; `1`; `0`] THEN
      REWRITE_TAC[ARITH; ADD_CLAUSES] THEN ARITH_TAC];
    ASM_CASES_TAC `a = 0` THENL
     [MAP_EVERY EXISTS_TAC [`0`; `0`; `0`] THEN
      ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; MULT_CLAUSES; EXP_2]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(a = 0) ==> (a = (a - 1) + 1)`)) THEN
    MP_TAC(SPECL [`a - 1`; `p:num`] LAGRANGE_LEMMA_ODD) THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[LT_IMP_LE]]);;
```

### Informal statement
For any integer $a$ and any prime number $p$, there exist integers $n$, $x$, and $y$ such that:
$n \cdot p = x^2 + y^2 + a$
where $2x \leq p$ and $2y \leq p$.

### Informal proof
The proof proceeds by case analysis on whether $p$ is even or odd:

**Case 1**: If $p$ is even:
- Since $p$ is prime and even, we know that $p = 2$ (as 2 is the only even prime).
- We further split this case based on whether $a$ is even or odd:
  - If $a$ is even, say $a = 2k$, then we take $n = k$, $x = 0$, $y = 0$.
    This gives us $n \cdot p = 2k = 0^2 + 0^2 + 2k = a$.
    The constraints $2x \leq p$ and $2y \leq p$ are satisfied since $x = y = 0$.
  - If $a$ is odd, say $a = 2k + 1$, then we take $n = k + 1$, $x = 1$, $y = 0$.
    This gives us $n \cdot p = (k+1) \cdot 2 = 2k + 2 = 1^2 + 0^2 + (2k+1) = a$.
    The constraints are satisfied since $2 \cdot 1 = 2 \leq p = 2$ and $2 \cdot 0 = 0 \leq p = 2$.

**Case 2**: If $p$ is odd:
- If $a = 0$, we simply take $n = 0$, $x = 0$, $y = 0$, which clearly satisfies the equation.
- If $a \neq 0$, we rewrite $a$ as $(a-1)+1$ and apply the lemma `LAGRANGE_LEMMA_ODD` to $a-1$ and $p$.
  This lemma gives us values of $n$, $x$, and $y$ that satisfy our requirements.

### Mathematical insight
This lemma is a step in proving Lagrange's four-square theorem, which states that every natural number can be represented as the sum of four squares. The lemma establishes that for any prime $p$, we can find a representation of any number $a$ (possibly with an additional term $n \cdot p$) using just two squares plus $a$.

For odd primes, we leverage the fact that we can write certain values as sums of two squares, which is a key insight in number theory related to the representation of integers as sums of squares.

The constraints $2x \leq p$ and $2y \leq p$ ensure that the squares are relatively "small" compared to $p$, which is useful in further applications of the result.

### Dependencies
- `LAGRANGE_LEMMA_ODD`: A related lemma for the case when $p$ is odd
- `prime`: Definition of prime numbers
- `EVEN_EXISTS`: Theorem about the existence of a representation for even numbers
- `ODD_EXISTS`: Theorem about the existence of a representation for odd numbers
- `NOT_EVEN`: Theorem relating to odd numbers

### Porting notes
When implementing this theorem in another proof assistant:
1. Ensure the proper treatment of number theory fundamentals like primality, evenness, and divisibility.
2. The proof relies on case analysis and arithmetic reasoning that should be straightforward to port.
3. The key dependency is `LAGRANGE_LEMMA_ODD`, which should be ported first.
4. Watch for differences in how arithmetic simplification is handled, as HOL Light uses tactics like `ARITH_TAC` that may not have direct equivalents.

---

## AUBREY_THM_4

### Name of formal statement
AUBREY_THM_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AUBREY_THM_4 = prove
 (`(?q. ~(q = 0) /\
       ?a b c d.
            (&a / &q) pow 2 + (&b / &q) pow 2 +
            (&c / &q) pow 2 + (&d / &q) pow 2 = &N)
   ==> ?a b c d. &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2 = &N`,
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_REWRITE_TAC[REAL_DIV_1; ARITH_EQ] THEN MESON_TAC[];
    STRIP_TAC THEN MP_TAC(SPEC `m:num` AUBREY_LEMMA_4) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
The theorem states: If there exist a non-zero rational $q$ and integers $a$, $b$, $c$, $d$ such that 
$(\frac{a}{q})^2 + (\frac{b}{q})^2 + (\frac{c}{q})^2 + (\frac{d}{q})^2 = N$, 
then there exist integers $a$, $b$, $c$, $d$ such that 
$a^2 + b^2 + c^2 + d^2 = N$.

### Informal proof
This proof uses the well-ordering principle on the set of denominators in rational representations of $N$ as a sum of four squares.

- First, we apply the well-ordering principle to the land side of the implication, which allows us to choose the minimal non-zero denominator $m$ such that $N$ can be written as a sum of four rational squares with denominator $m$.

- The proof then considers two cases:
  - If $m = 1$, then we already have $N$ as a sum of four integer squares, and we're done.
  - If $m > 1$, we apply `AUBREY_LEMMA_4`, which states that given a representation of $N$ as a sum of four rational squares with denominator $m > 1$, we can find another representation with a strictly smaller denominator $m' < m$.

- This contradicts the minimality of $m$, establishing that $m = 1$ must be the case, which means $N$ can be written as a sum of four integer squares.

### Mathematical insight
This theorem establishes that if a number can be represented as a sum of four rational squares, then it can also be represented as a sum of four integer squares. It's a key step in proving Lagrange's four-square theorem, which states that every positive integer can be expressed as the sum of four squares of integers.

The proof uses a minimality argument on denominators and relies on Aubrey's Lemma 4, which shows how to reduce the denominator in a rational representation. This approach is elegant as it converts the question of existence of integer solutions into a question about the minimal denominator of rational solutions.

### Dependencies
- `AUBREY_LEMMA_4`: The key lemma showing how to reduce the denominator in a rational representation of a sum of four squares.
- `num_WOP`: Well-ordering principle for natural numbers.

### Porting notes
When porting this proof, one should:
1. Ensure the well-ordering principle is available
2. Implement or port `AUBREY_LEMMA_4` first
3. Be careful about the handling of rational numbers and how they are represented in the target system

---

## LAGRANGE_IDENTITY

### LAGRANGE_IDENTITY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_IDENTITY = REAL_ARITH
  `(w1 pow 2 + x1 pow 2 + y1 pow 2 + z1 pow 2) *
   (w2 pow 2 + x2 pow 2 + y2 pow 2 + z2 pow 2) =
   (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) pow 2 +
   (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) pow 2 +
   (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) pow 2 +
   (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) pow 2`;;
```

### Informal statement
The Lagrange identity states that for any real numbers $w_1, x_1, y_1, z_1, w_2, x_2, y_2, z_2$:

$(w_1^2 + x_1^2 + y_1^2 + z_1^2)(w_2^2 + x_2^2 + y_2^2 + z_2^2) = (w_1w_2 - x_1x_2 - y_1y_2 - z_1z_2)^2 + (w_1x_2 + x_1w_2 + y_1z_2 - z_1y_2)^2 + (w_1y_2 - x_1z_2 + y_1w_2 + z_1x_2)^2 + (w_1z_2 + x_1y_2 - y_1x_2 + z_1w_2)^2$

### Informal proof
This theorem is proven using `REAL_ARITH`, which is a HOL Light tactic that automatically proves arithmetic statements in the real domain. The identity can be verified directly through algebraic expansion of the right-hand side and comparing terms with the left-hand side.

The proof involves expanding each squared term on the right side, collecting like terms, and verifying that they match the product on the left side. This is a direct computation that the automated arithmetic reasoning tactic handles automatically.

### Mathematical insight
The Lagrange identity is a fundamental algebraic result that relates the product of sums of squares to a sum of squares of specific combinations. This identity is particularly important in several contexts:

1. It generalizes the Brahmagupta-Fibonacci identity from two dimensions to four dimensions.

2. It is closely related to quaternion multiplication - the right-hand side terms correspond to the square of the norm of the product of two quaternions.

3. It demonstrates that the product of two sums of four squares is itself a sum of four squares, which was crucial in proving Lagrange's four-square theorem (that every positive integer can be expressed as the sum of four perfect squares).

This identity shows the multiplicative property of quadratic forms and has applications in number theory, algebra, and mathematical physics.

### Dependencies
None explicitly shown in the provided information. The theorem is proven using:
- `REAL_ARITH`: A built-in HOL Light tactic for arithmetic reasoning over real numbers.

### Porting notes
When porting this theorem to other proof assistants:
- This identity is entirely algebraic and should be provable in any system with real arithmetic.
- Some systems might benefit from explicitly structured proofs instead of relying on automation.
- The proof could either use a similar automation tactic (like `ring` in Coq/Lean) or be performed by explicit algebraic manipulation.
- In systems with good support for algebraic reasoning, this may be almost trivial to prove.

---

## LAGRANGE_REAL_NUM

### LAGRANGE_REAL_NUM
- Theorem name: LAGRANGE_REAL_NUM

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let LAGRANGE_REAL_NUM = prove
 (`!n. ?w x y z. &n = &w pow 2 + &x pow 2 + &y pow 2 + &z pow 2`,
  let lemma = prove
   (`(?a. abs(w) = &a) /\ (?b. abs(x) = &b) /\
     (?c. abs(y) = &c) /\ (?d. abs(z) = &d)
     ==> ?a b c d. w pow 2 + x pow 2 + y pow 2 + z pow 2 =
                   &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2`,
    STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    MESON_TAC[]) in
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [REPEAT(EXISTS_TAC `0`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [EXISTS_TAC `1` THEN REPEAT(EXISTS_TAC `0`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `p divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  ASM_CASES_TAC `m = 1` THENL
   [ALL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(fun th ->
     MP_TAC(SPEC `p:num` th) THEN MP_TAC(SPEC `m:num` th)) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `p < p * m <=> p * 1 < p * m`] THEN
    REWRITE_TAC[LT_MULT_LCANCEL] THEN
    UNDISCH_TAC `~(p * m = 0)` THEN REWRITE_TAC[MULT_EQ_0] THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 < x <=> ~(x = 0) /\ ~(x = 1)`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1:num`; `x1:num`; `y1:num`; `z1:num`] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`w2:num`; `x2:num`; `y2:num`; `z2:num`] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[LAGRANGE_IDENTITY] THEN
    MATCH_MP_TAC lemma THEN REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    MESON_TAC[REAL_INTEGER_CLOSURES]] THEN
  UNDISCH_TAC `m = 1` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LAGRANGE_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `1 EXP 2 + 0 EXP 2`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `x:num`; `y:num`] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC AUBREY_THM_4 THEN
  SUBGOAL_THEN `q * p < p EXP 2` MP_TAC THENL
   [ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(2 * x) * (2 * x) <= p * p /\ (2 * y) * (2 * y) <= p * p /\
      2 * 2 <= p * p
      ==> x * x + y * y + 1 < p * p`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~(p = 0)`; `~(p = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_2; LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `0 * p = x EXP 2 + y EXP 2 + 1 EXP 2 + 0 EXP 2` THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[MULT_CLAUSES; EXP_2] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&p = &q * &(q * p) / &q pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC; real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_MUL_ASSOC; REAL_POW_EQ_0; REAL_MUL_LINV; REAL_MUL_LID;
             ASSUME `~(q = 0)`; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; LAGRANGE_IDENTITY] THEN
  SUBST1_TAC(SYM(ASSUME
    `&q = &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2`)) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div; GSYM REAL_POW_DIV] THEN
  EXISTS_TAC `q:num` THEN REWRITE_TAC[ASSUME `~(q = 0)`] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
  REWRITE_TAC[REAL_INV_EQ_0; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
              ASSUME `~(q = 0)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC lemma THEN
  REWRITE_TAC[REAL_OF_NUM_MUL] THEN MESON_TAC[REAL_INTEGER_CLOSURES]);;
```

### Informal statement
The theorem states that for any natural number $n$, there exist natural numbers $w, x, y, z$ such that:

$$n = w^2 + x^2 + y^2 + z^2$$

This is the famous Lagrange's four-square theorem, which states that every natural number can be expressed as the sum of four integer squares.

### Informal proof
The proof uses mathematical induction on $n$:

**Base cases:**
- For $n = 0$: We take $w = x = y = z = 0$, so $0 = 0^2 + 0^2 + 0^2 + 0^2$.
- For $n = 1$: We take $w = 1, x = y = z = 0$, so $1 = 1^2 + 0^2 + 0^2 + 0^2$.

**Induction step:**
For $n > 1$:

1. First, we establish a lemma that allows us to transform expressions with absolute values into expressions with squares of natural numbers.

2. By the prime factorization theorem (PRIME_FACTOR), there exists a prime $p$ that divides $n$. So $n = p \cdot m$ for some $m$.

3. The proof branches based on whether $m = 1$ or $m > 1$:

   * If $m = 1$, then $n = p$. We use LAGRANGE_LEMMA to find numbers $q, x, y$ such that:
     $$q \cdot p = x^2 + y^2 + 1^2 + 0^2$$
     
     We show that $q < p$ (using properties of prime numbers), and by induction hypothesis, $q$ can be written as sum of four squares:
     $$q = a^2 + b^2 + c^2 + d^2$$
     
     Using the Lagrange identity (LAGRANGE_IDENTITY) and algebraic transformations, we derive the required representation for $p$.

   * If $m > 1$, both $p$ and $m$ are less than $n$. By induction hypothesis, both can be written as sums of four squares:
     $$p = w_1^2 + x_1^2 + y_1^2 + z_1^2$$
     $$m = w_2^2 + x_2^2 + y_2^2 + z_2^2$$
     
     Then we use the Lagrange identity to show that their product $n = p \cdot m$ can also be written as a sum of four squares.

### Mathematical insight
Lagrange's four-square theorem is a foundational result in number theory, proven by Joseph-Louis Lagrange in 1770. It states that every natural number can be expressed as the sum of at most four perfect squares. This theorem is a special case of Waring's problem, which asks whether each natural number can be expressed as the sum of a fixed number of $k$-th powers.

The proof relies on several key insights:
1. The use of the Lagrange identity to show that the product of two sums of four squares is itself a sum of four squares
2. Induction on the natural numbers
3. The prime factorization theorem to reduce the problem to prime numbers

This result has connections to quaternions, the Hurwitz integers, and has applications in various areas of mathematics including coding theory and cryptography.

### Dependencies
**Theorems:**
- `PRIME_1`: The assertion that 1 is not a prime number
- `PRIME_FACTOR`: Every natural number greater than 1 has a prime factor
- `LAGRANGE_LEMMA`: A supporting lemma for Lagrange's four-square theorem
- `AUBREY_THM_4`: Another supporting theorem in the proof
- `LAGRANGE_IDENTITY`: The identity showing that the product of two sums of four squares is itself a sum of four squares

**Definitions:**
- `prime`: The definition of prime numbers
- `divides`: The divisibility relation

### Porting notes
When porting this proof:
1. Ensure the Lagrange identity is available in the target system
2. The proof relies on several helper theorems like AUBREY_THM_4 and LAGRANGE_LEMMA which would need to be ported too
3. The proof uses the well-foundedness of natural numbers for induction, which might need different formulation in other systems
4. Be careful with the transformation between integer and real number representations in other proof assistants

---

## LAGRANGE_NUM

### LAGRANGE_NUM
- `LAGRANGE_NUM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LAGRANGE_NUM = prove
 (`!n. ?w x y z. n = w EXP 2 + x EXP 2 + y EXP 2 + z EXP 2`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` LAGRANGE_REAL_NUM) THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]);;
```

### Informal statement
For any natural number $n$, there exist natural numbers $w$, $x$, $y$, and $z$ such that:
$$n = w^2 + x^2 + y^2 + z^2$$

### Informal proof
The proof follows directly from Lagrange's four-square theorem for real numbers (`LAGRANGE_REAL_NUM`):

1. Apply `LAGRANGE_REAL_NUM` to the natural number $n$ to obtain the existence of real numbers $w$, $x$, $y$, $z$ such that $n = w^2 + x^2 + y^2 + z^2$ where $w,x,y,z \geq 0$.

2. Since all quantities are non-negative reals that sum to the natural number $n$, and the theorem asserts the existence of a representation using squares, the following HOL Light rewriting steps address the conversion between real and natural number representations:
   - Use `REAL_POS` to handle the non-negativity conditions
   - Use `REAL_OF_NUM_POW` to convert between natural number powers and real number powers
   - Use `REAL_OF_NUM_ADD` to convert between natural number addition and real number addition
   - Use `REAL_OF_NUM_EQ` for equality between real and natural numbers

3. Since the representation found in `LAGRANGE_REAL_NUM` consists of non-negative real numbers, and the sum equals the natural number $n$, these real numbers must actually be natural numbers, completing the proof.

### Mathematical insight
This theorem is a statement of Lagrange's four-square theorem, which asserts that every natural number can be expressed as the sum of at most four perfect squares. This is a classic result in number theory proved by Joseph-Louis Lagrange in 1770.

The result is important because:
- It provides an exact upper bound (4) on the number of squares needed to represent any natural number
- It's a specific case of Waring's problem for the power 2
- It has connections to quaternions and various other number-theoretic properties

This theorem in HOL Light follows from the real-number version, establishing that the representation can be done purely with natural numbers.

### Dependencies
- Theorems:
  - `LAGRANGE_REAL_NUM`: The real-number version of Lagrange's four-square theorem
  - `REAL_POS`: Proves that the type-cast of any natural number to a real is non-negative
  - `REAL_OF_NUM_POW`: Relates natural number powers to real number powers
  - `REAL_OF_NUM_ADD`: Relates addition of natural numbers to addition of their real counterparts
  - `REAL_OF_NUM_EQ`: Relates equality of natural numbers to equality of their real counterparts

### Porting notes
When porting this to other systems:
- Ensure the target system has a formalization of Lagrange's four-square theorem for real numbers
- The proof relies on straightforward conversions between natural and real number arithmetic
- The key insight is that if non-negative reals sum to a natural number, and each is a perfect square, then they must be squares of natural numbers

---

## LAGRANGE_INT

### LAGRANGE_INT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_INT = prove
 (`!a. &0 <= a <=> ?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`a:int`,`a:int`) THEN REWRITE_TAC[GSYM INT_FORALL_POS] THEN
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `n:num` LAGRANGE_REAL_NUM) THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
    MESON_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[INT_LE_SQUARE; INT_LE_ADD; INT_POW_2]]);;
```

### Informal statement
For any integer $a$, $0 \leq a$ if and only if there exist integers $w$, $x$, $y$, and $z$ such that $a = w^2 + x^2 + y^2 + z^2$.

### Informal proof
The proof proceeds in both directions:

$(\Rightarrow)$ For the forward direction:
- We transform the problem using `INT_FORALL_POS` to work with natural numbers instead of non-negative integers.
- For any natural number $n$, we apply Lagrange's four-square theorem for real numbers (`LAGRANGE_REAL_NUM`).
- This theorem states that any natural number can be expressed as the sum of four squares.
- The various conversion theorems like `REAL_OF_NUM_POW`, `REAL_OF_NUM_ADD` and `INT_OF_NUM_POW` are used to convert between number types.
- The result is then simplified back to the integer domain.

$(\Leftarrow)$ For the reverse direction:
- Assume $a = w^2 + x^2 + y^2 + z^2$ for some integers $w$, $x$, $y$, and $z$.
- Apply `INT_LE_SQUARE` to show that for any integer, its square is greater than or equal to 0.
- Apply `INT_LE_ADD` to show that the sum of non-negative integers is non-negative.
- Therefore, $a$ as the sum of four squares is greater than or equal to 0.

### Mathematical insight
This theorem is the integer version of Lagrange's four-square theorem, which states that every non-negative integer can be expressed as the sum of at most four perfect squares. This is a fundamental result in number theory, first proven by Joseph-Louis Lagrange in 1770.

The theorem connects the non-negativity of integers with a specific representation as sums of squares. This representation has important applications in number theory, particularly in the study of quadratic forms and Diophantine equations.

### Dependencies
- `LAGRANGE_REAL_NUM`: The real number version of Lagrange's four-square theorem
- `INT_FORALL_POS`: Converting between integer inequalities and natural numbers
- `INT_LE_SQUARE`: Property that squares of integers are non-negative
- `INT_LE_ADD`: Property that the sum of non-negative integers is non-negative
- `INT_OF_NUM_EQ`, `INT_OF_NUM_POW`, `INT_OF_NUM_ADD`: Conversion between natural numbers and integers
- `REAL_OF_NUM_POW`, `REAL_OF_NUM_ADD`, `REAL_OF_NUM_EQ`: Conversion between natural numbers and real numbers

### Porting notes
When porting to another proof assistant:
- Ensure that the relevant number type conversions are available in the target system.
- You may need to port `LAGRANGE_REAL_NUM` first, which is the natural number version of Lagrange's theorem.
- The representation of integers, particularly the distinction between integers and natural numbers, might differ across systems, requiring careful handling of the conversions.

---

