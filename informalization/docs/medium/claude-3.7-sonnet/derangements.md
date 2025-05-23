# derangements.ml

## Overview

Number of statements: 43

This file formalizes the classic formula for calculating the number of derangements (permutations with no fixed points) of an n-element set, proving that this number equals the nearest integer to n!/e. It develops the necessary theory around derangement counting, leveraging transcendental functions, real calculations, and floor/ceiling operations from the imported libraries. The proof likely involves techniques from combinatorial mathematics and real analysis to establish this elegant relationship between derangements and the mathematical constant e.

## domain

### Name of formal statement
domain

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let domain = new_definition
 `domain r = {x | ?y. r(x,y)}`;;
```

### Informal statement
The domain of a relation $r$ is defined as the set of all elements $x$ such that there exists a $y$ where $(x, y) \in r$.

Mathematically: $\text{domain}(r) = \{x \mid \exists y. (x, y) \in r\}$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The domain of a relation is a fundamental concept in set theory and relation theory. It represents the set of all first components appearing in the ordered pairs of the relation. For a function, the domain represents the set of inputs for which the function is defined.

This definition is particularly useful when working with relations and functions in formalized mathematics. It allows for reasoning about the first components of relation pairs without having to directly refer to the pairs themselves.

### Dependencies
- No direct dependencies as this is a base definition.

### Porting notes
- This is a straightforward definition that should be easy to port to most proof assistants.
- In some systems, relations might be represented differently than in HOL Light (where they are typically encoded as sets of ordered pairs or as predicates on pairs), so the syntax might need adjustment.
- Some systems might already have built-in definitions for domain and range of relations.

---

## range

### range
- `range`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let range = new_definition
 `range r = {y | ?x. r(x,y)}`;;
```

### Informal statement
Given a binary relation $r$, the range of $r$ is defined as:
$$\text{range}(r) = \{y \mid \exists x. r(x,y)\}$$

This represents the set of all elements $y$ such that there exists some element $x$ where the ordered pair $(x,y)$ is in the relation $r$.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The range of a relation captures all the second components of the ordered pairs in the relation. It's a fundamental concept in set theory and relation theory, giving us the set of all "outputs" or "destination elements" of a relation.

In the context of functions (which are special cases of relations), the range consists of all values that the function actually outputs, as opposed to the codomain which might contain elements that are never reached.

This definition enables formal reasoning about properties of relations, such as surjectivity for functions (where the range equals the codomain).

### Dependencies
#### Definitions
- None explicitly listed in the provided dependency information

### Porting notes
When porting this definition to other proof assistants:
- Ensure the underlying representation of relations in the target system is compatible (typically relations are represented as sets of ordered pairs)
- The definition is straightforward and should translate easily to most systems with basic set theory support

---

## id

### Name of formal statement
compose

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let id = new_definition
 `id(s) (x,y) <=> x IN s /\ x = y`;;
```

### Informal statement
The relational composition of two relations $r$ and $s$, denoted as $r \% s$, is defined as:

$(r \% s)(x,y) \Leftrightarrow \exists z. r(x,z) \land s(z,y)$

This defines the composition of binary relations where $(x,y)$ is in the composition of $r$ and $s$ if and only if there exists some intermediate value $z$ such that $(x,z)$ is in relation $r$ and $(z,y)$ is in relation $s$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
Relational composition is a fundamental operation in relation theory that generalizes function composition to binary relations. It captures the idea of "chaining" two relations together through an intermediate point.

For binary relations $r \subseteq X \times Y$ and $s \subseteq Y \times Z$, their composition $r \% s \subseteq X \times Z$ contains exactly those pairs $(x,z)$ for which there exists some $y \in Y$ such that $(x,y) \in r$ and $(y,z) \in s$.

This operation is especially important in algebraic treatments of relations, relational databases, and category theory (where it corresponds to composition of morphisms). The notation `%` is chosen to represent this composition.

Note that while function composition is typically written from right to left ($(f \circ g)(x) = f(g(x))$), relation composition is often written in the opposite order. In HOL Light, the definition uses the order $r \% s$, which means that $r$ is applied first, followed by $s$.

### Dependencies
No explicit dependencies mentioned in the provided information.

### Porting notes
- The infix notation `%` with right associativity and precedence level 26 is used for relation composition.
- When porting to other proof assistants, you may need to adjust the notation based on the target system's conventions.
- Some systems might already have built-in relation composition operators, so you might want to check for existing definitions before creating your own.

---

## converse

### Name of formal statement
converse

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let converse = new_definition
 `converse(r) (x,y) = r(y,x)`;;
```

### Informal statement
The converse relation of a relation $r$ is defined as the relation $\text{converse}(r)$ such that for any ordered pair $(x,y)$, 
$$\text{converse}(r)(x,y) = r(y,x)$$

In other words, the converse relation flips the order of the elements in each pair of the original relation.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The converse relation is a fundamental concept in relation theory. It reverses the direction of a relation by swapping the order of each pair. For example, if $r$ represents "is a parent of", then $\text{converse}(r)$ represents "is a child of".

This definition provides a formal way to construct the converse of any given relation. It's particularly useful in formalizing mathematical statements where the directionality of relations needs to be reversed. For example, in graph theory, directed graphs can be reversed by taking the converse of their edge relation.

The converse operation is sometimes denoted as $r^{-1}$ or $r^T$ in mathematical literature.

### Dependencies
No dependencies are listed for this definition.

### Porting notes
When porting this definition to other proof assistants:
- This is a straightforward definition that should translate easily to most systems
- In systems with built-in relation types, there might already be a similar concept or notation
- Some systems might represent relations differently (e.g., as sets of ordered pairs rather than as boolean-valued functions on pairs), which would require adapting the definition accordingly

---

## swap

### Name of formal statement
swap

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let swap = new_definition
 `swap(a,b) (x,y) <=> x = a /\ y = b \/ x = b /\ y = a`;;
```

### Informal statement
For any elements $a$, $b$, $x$, and $y$, the function $\text{swap}(a,b)$ applied to the pair $(x,y)$ is defined as:

$$\text{swap}(a,b)(x,y) \iff (x = a \land y = b) \lor (x = b \land y = a)$$

This defines a function that checks whether the pair $(x,y)$ is equal to either $(a,b)$ or $(b,a)$.

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
The `swap` function defines a transposition operation, which is a fundamental concept in permutation theory. It checks whether a given pair $(x,y)$ is one of two specific pairs: either $(a,b)$ or $(b,a)$.

This definition can be used to formalize the notion of swapping or interchanging two elements in various mathematical contexts, such as:
- Defining permutations as compositions of transpositions
- Formalizing symmetry properties where exchanging two elements leads to equivalent structures
- Reasoning about transformations that involve pairwise exchanges

The definition is formulated as a predicate rather than an operation that actually transforms $(a,b)$ into $(b,a)$, which aligns with HOL Light's logical foundation.

### Dependencies
None explicitly mentioned in the provided dependency list.

### Porting notes
When porting this definition:
- Consider whether the target system prefers to represent a transposition as a predicate (as done here) or as a function that returns a new pair
- Check if the target system has existing libraries for permutations that might use different conventions
- Note that in some systems, it might be more natural to define swap as an actual function that transforms pairs rather than as a relation

---

## REL_TAC

### Name of formal statement
REL_TAC

### Type of the formal statement
Custom tactic definition

### Formal Content
```ocaml
let REL_TAC =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM; PAIR_BETA_THM;
              permutes; pairsup; domain; range; compose; id; converse; swap;
              deranges; IN_INSERT; IN_DELETE; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; EMPTY; INSERT; DELETE; UNION; IN_ELIM_THM; PAIR_EQ;
              id; converse; swap] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_MESON_TAC[];;
```

### Informal statement
`REL_TAC` is a custom tactic for proving theorems about relations. It:

1. Removes all assumptions from the goal
2. Rewrites the goal using standard theorems about functions, pairs, relations, permutations, and set operations
3. Performs basic logical inference steps (like stripping quantifiers and proving equivalences)
4. Simplifies the goal by substituting variables
5. Finally attempts to solve the goal using `ASM_MESON_TAC`

### Informal proof
This is a tactic definition, not a theorem, so it doesn't have a proof in the traditional sense. The tactic itself is defined as a sequence of tactical operations:

- Clears all assumptions using `POP_ASSUM_LIST(K ALL_TAC)`
- Applies a series of rewrite steps using standard theorems about:
  - Function equality (`FUN_EQ_THM`)
  - Quantifiers over pairs (`FORALL_PAIR_THM`, `EXISTS_PAIR_THM`)
  - Beta-reduction for pairs (`PAIR_BETA_THM`)
  - Relation and set operations (`permutes`, `pairsup`, `domain`, `range`, etc.)
- Performs logical inference through repeated application of `STRIP_TAC` and `EQ_TAC`
- Substitutes variables using `SUBST_ALL_TAC`
- Finally attempts to solve the goal using `ASM_MESON_TAC`

### Mathematical insight
This tactic is designed to automate proofs about relations, particularly those involving permutations, bijections between sets, and derangements. The comment indicates it's a "trivial tactic for properties of relations," suggesting it handles routine reasoning in this domain.

The tactic encapsulates a standard proof strategy for relation problems:
1. Expand definitions to their core set-theoretic and logical forms
2. Apply standard logical manipulations
3. Use substitution to simplify expressions
4. Let the automated reasoner (`MESON`) handle the remaining logical steps

This approach reflects the typical mathematical strategy of unfolding definitions and applying standard manipulations before tackling the core logical structure of a relational proof.

### Dependencies
#### Theorems
- `FUN_EQ_THM` - Function extensionality
- `FORALL_PAIR_THM` - Universal quantification over pairs
- `EXISTS_PAIR_THM` - Existential quantification over pairs  
- `PAIR_BETA_THM` - Beta reduction for pairs
- `PAIR_EQ` - Equality of pairs

#### Definitions
- `permutes` - A relation that permutes a set
- `pairsup` - A relation that pairs up two sets bijectively
- `domain` - Domain of a relation
- `range` - Range of a relation
- `compose` - Composition of relations
- `id` - Identity relation
- `converse` - Converse of a relation
- `swap` - Swap relation
- `deranges` - A permutation with no fixed points

### Porting notes
When porting this tactic:
1. Identify equivalent theorems in the target system for function equality, pair manipulation, and set operations
2. Consider differences in how relations are represented (as sets of pairs in HOL Light)
3. Adapt the assumption handling and substitution tactics to equivalent operations in the target system
4. Replace `ASM_MESON_TAC` with an appropriate automated theorem prover in the target system
5. Note that in some systems, such specialized tactics might be unnecessary if the built-in automation is powerful enough to handle relation proofs directly

---

## REL_RULE

### Name of formal statement
REL_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REL_RULE tm = prove(tm,REL_TAC);;
```

### Informal statement
`REL_RULE` is a theorem-proving function that takes a term `tm` and proves it using the tactic `REL_TAC`. This function is designed to handle theorems involving relations.

When the function is called with a term `tm`, it attempts to prove `tm` using the `REL_TAC` tactic and returns the resulting theorem.

### Informal proof
The implementation of this function is straightforward:

1. The function takes a term `tm` as input.
2. It calls the `prove` function with two arguments:
   - The term `tm` to be proven
   - The tactic `REL_TAC` which is used to attempt the proof

3. The `prove` function applies the tactic to the goal represented by `tm` and returns the resulting theorem if the proof is successful.

The actual proving work is delegated to `REL_TAC`, which is presumably a tactic specialized for handling relation-based theorems.

### Mathematical insight
`REL_RULE` serves as a convenient wrapper for proving relation-based theorems. It encapsulates the common pattern of using `REL_TAC` for proofs, making theorem proving more concise and easier to read.

This pattern of creating specialized theorem-proving functions is common in interactive theorem provers like HOL Light. Such functions help to abstract away the details of proof tactics and provide a more declarative interface for proving certain classes of theorems.

The function follows HOL Light's naming convention where functions ending with `_RULE` typically take a term and return a theorem.

### Dependencies
- Functions:
  - `prove`: Core HOL Light function that takes a term and a tactic and returns a theorem
  - `REL_TAC`: A tactic specialized for proving relation-based theorems

### Porting notes
When porting this to other proof assistants:
- This is a simple wrapper function that calls the existing proof tactic `REL_TAC`
- To port this, you would need to first ensure that an equivalent to `REL_TAC` exists or is ported
- In some proof assistants, such wrapper functions might be implemented differently, possibly as:
  - Specialized tactics or proof methods
  - Proof automation hints
  - Attributes on theorems

---

## CONVERSE_COMPOSE

### Name of formal statement
CONVERSE_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERSE_COMPOSE = prove
 (`!r s. converse(r % s) = converse(s) % converse(r)`,
  REL_TAC);;
```

### Informal statement
For any two relations $r$ and $s$, the converse of their composition is equal to the composition of their converses in reverse order:
$$\forall r, s. (r \circ s)^{-1} = s^{-1} \circ r^{-1}$$

Here:
- $r \circ s$ denotes the composition of relations $r$ and $s$
- $r^{-1}$ denotes the converse (or inverse) of relation $r$

### Informal proof
This theorem is proven using the `REL_TAC` tactic, which is a specialized tactic for proving statements about relations in HOL Light. This tactic automatically unfolds the definitions of relation operations and proves the equivalence by showing that for any elements $x$ and $y$:

$(x, y) \in (r \circ s)^{-1}$ if and only if $(y, x) \in (r \circ s)$
if and only if there exists a $z$ such that $(y, z) \in r$ and $(z, x) \in s$
if and only if there exists a $z$ such that $(z, y) \in r^{-1}$ and $(x, z) \in s^{-1}$
if and only if $(x, y) \in (s^{-1} \circ r^{-1})$

The `REL_TAC` tactic handles all these logical steps automatically.

### Mathematical insight
This theorem expresses a fundamental property of relation algebra that the converse operation distributes over composition, but with a reversal of order. This property is analogous to the well-known property in linear algebra where the transpose of a matrix product is the product of the transposes in reverse order: $(AB)^T = B^T A^T$.

The result is important in formal reasoning about relations and appears in many contexts, including:
- Category theory (where it relates to opposite categories)
- Database theory (for query optimization)
- Program verification (when reasoning about program relations)

This property allows for systematic manipulation of relations and helps simplify complex relation expressions.

### Dependencies
No explicit dependencies are listed, but the theorem relies on:
- The definitions of relation composition (`%`) and relation converse (`converse`)
- The `REL_TAC` automated tactic

### Porting notes
When porting this theorem:
- Ensure that relation composition and converse are defined consistently in the target system
- The proof is straightforward and should be provable with basic relation algebra in most systems
- In some systems, relations might be represented as functions to `bool` or as sets of pairs, which may affect how the proof is structured

Systems with built-in relation algebra libraries (like Isabelle/HOL) may already have this theorem available.

---

## CONVERSE_CONVERSE

### Name of formal statement
CONVERSE_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERSE_CONVERSE = prove
 (`!r. converse(converse r) = r`,
  REL_TAC);;
```

### Informal statement
For any binary relation $r$, the converse of the converse of $r$ is equal to $r$ itself, formally:
$$\forall r.\ (\text{converse}(\text{converse}(r)) = r)$$

Where $\text{converse}(r)$ represents the relation obtained by reversing the order of elements in each pair of the relation $r$.

### Informal proof
This theorem is proved using `REL_TAC`, which is a tactic designed specifically for proving basic properties of relations. 

The proof is straightforward:
- For a relation $r$, the converse operation swaps the elements in each ordered pair.
- Applying the converse operation twice will swap the elements back to their original order.
- Therefore, $(\text{converse}(\text{converse}(r)) = r)$ for any relation $r$.

### Mathematical insight
This theorem establishes a fundamental property of the converse operation on binary relations - it is its own inverse. This is analogous to how negation in logic or inverses in group theory behave when applied twice.

The result is important because:
1. It shows that the converse operation is an involution
2. It's used in reasoning about relation properties in set theory and other mathematical contexts
3. It provides a simple way to simplify expressions involving multiple converse operations

In formal reasoning systems, this theorem allows for simplification of complex relation expressions.

### Dependencies
The proof uses `REL_TAC`, a specialized tactic for relation theorems in HOL Light.

### Porting notes
This theorem should be straightforward to port to other systems. The main considerations:
- Ensure the target system has the converse relation operation defined
- The proof might be equally simple in other systems, possibly using basic extensionality principles
- Some systems might already have this as a built-in property or lemma

---

## PAIRSUP_EXPLICIT

### Name of formal statement
PAIRSUP_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_EXPLICIT = prove
 (`!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;
```

### Informal statement
For any relation $p$ and sets $s$ and $t$, $p$ is a pairing relation between $(s,t)$ if and only if all of the following conditions hold:
- For all $x$ and $y$, if $p(x,y)$ holds, then $x \in s$ and $y \in t$
- For all $x \in s$, there exists a unique $y \in t$ such that $p(x,y)$
- For all $y \in t$, there exists a unique $x \in s$ such that $p(x,y)$

### Informal proof
The proof is performed using the `REL_TAC` tactic, which is designed for proving statements about relations. This tactic automatically handles the equivalence between the explicit formulation in the theorem statement and the formal definition of a pairing relation (`pairsup`).

The tactic automatically verifies that:
- The relation $p$ maps only between elements of sets $s$ and $t$
- For each element in $s$, there is exactly one matching element in $t$ related by $p$
- For each element in $t$, there is exactly one matching element in $s$ related by $p$

These conditions precisely characterize what it means for $p$ to be a pairing relation between sets $s$ and $t$.

### Mathematical insight
This theorem provides an explicit characterization of what it means for a relation to establish a one-to-one correspondence (bijection) between two sets. The `pairsup` relation is essentially defining a bijective relation between sets.

The importance of this result is that it translates the abstract concept of a pairing relation into three concrete conditions that are easier to work with in proofs:
1. The relation is contained within the Cartesian product $s \times t$
2. Every element of $s$ is related to exactly one element of $t$
3. Every element of $t$ is related to exactly one element of $s$

This characterization is fundamental in set theory and is equivalent to saying that there exists a bijection between the sets $s$ and $t$.

### Dependencies
This theorem appears to have minimal explicit dependencies in the code shown, but conceptually relies on:
- The definition of `pairsup` which represents pairing relations
- The `REL_TAC` tactic which seems to be a specialized tactic for reasoning about relations

### Porting notes
When porting this theorem:
- Ensure the target system has a definition of pairing relations (`pairsup`) or be prepared to define it
- The proof might need to be expanded into more basic steps since `REL_TAC` is likely a specialized HOL Light tactic that might not have direct counterparts in other systems
- In systems with strong automation for relations and functions (like Isabelle/HOL), similar automation might be available, but in Lean or Coq, you might need to prove the bijection properties more explicitly

---

## PERMUTES_EXPLICIT

### PERMUTES_EXPLICIT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PERMUTES_EXPLICIT = prove
 (`!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;
```

### Informal statement
This theorem characterizes when a relation $p$ permutes a set $s$. Specifically, for any relation $p$ and set $s$, $p$ permutes $s$ if and only if the following three conditions hold:
1. For all $x$ and $y$, if $p(x,y)$ holds, then both $x \in s$ and $y \in s$.
2. For all $x \in s$, there exists a unique $y \in s$ such that $p(x,y)$ holds.
3. For all $y \in s$, there exists a unique $x \in s$ such that $p(x,y)$ holds.

### Informal proof
The proof uses `REL_TAC`, which is a HOL Light tactic designed to prove theorems about relations. This suggests that the theorem follows directly from the definition of what it means for a relation to permute a set, and the tactic is able to automatically derive the equivalence by decomposing the definition into its constituent properties.

The proof establishes that a relation permutes a set precisely when it satisfies the three explicit conditions:
- The relation only relates elements within the set
- Every element in the set is related to exactly one other element in the set
- Every element in the set has exactly one element in the set related to it

These conditions together ensure that the relation represents a bijective mapping of the set to itself.

### Mathematical insight
This theorem provides an explicit characterization of what it means for a relation to permute a set. A permutation is typically understood as a bijective function from a set to itself. This theorem extends this concept to relations, specifying that a relation permutes a set when it behaves like the graph of a bijective function on that set.

The three conditions ensure that:
1. The relation stays within the set (closure)
2. The relation is functional and injective (from the set to itself)
3. The relation is surjective (onto the set)

This characterization is useful for reasoning about permutations in a relational context, which can be more general and flexible than the functional approach in certain applications.

### Dependencies
No specific dependencies were provided, but the theorem likely depends on:
- Basic definitions of relations and sets
- The definition of `permutes` which establishes when a relation represents a permutation

### Porting notes
When porting this theorem:
- Ensure that the target system has a notion of relations as binary predicates
- Check how the target system handles uniqueness quantifiers (`?!`)
- Verify that the definition of `permutes` in the target system aligns with HOL Light's definition
- Consider whether the target system has tactics similar to `REL_TAC` that can handle relation-based proofs automatically

---

## PAIRSUP_DOMRAN

### PAIRSUP_DOMRAN
- Theorem PAIRSUP_DOMRAN

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PAIRSUP_DOMRAN = prove
 (`!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t`,
  REL_TAC);;
```

### Informal statement
For any relation $p$ and sets $s$ and $t$, if $p$ is the pairwise supremum over the pair $(s,t)$, then the domain of $p$ is $s$ and the range of $p$ is $t$. In symbols:
$$\forall p, s, t.\ p \text{ pairsup } (s,t) \Rightarrow \text{domain}(p) = s \land \text{range}(p) = t$$

### Informal proof
The proof is carried out using the tactic `REL_TAC`, which is a specialized tactic for reasoning about relations and their properties. This tactic automates the reasoning about domains and ranges of relations, applying the appropriate definitions and theorems.

The proof essentially follows from the definition of `pairsup`, which constructs a relation from two sets such that the domain and range of the resulting relation match those sets exactly.

### Mathematical insight
This theorem establishes a fundamental property of the pairwise supremum operation on sets: when forming the pairwise supremum relation from two sets, the domain and range of the resulting relation are precisely those original sets. This is an important characteristic that ensures the pairwise supremum preserves the structure of the original sets.

The pairwise supremum operation is used in various contexts when working with relations, especially in set theory and order theory. This theorem provides a basic property that can be relied upon when manipulating relations constructed through the pairwise supremum.

### Dependencies
- `pairsup`: Definition of the pairwise supremum operation
- `domain`: Definition of the domain of a relation
- `range`: Definition of the range of a relation
- `REL_TAC`: A specialized tactic for relation reasoning

### Porting notes
When porting to other systems:
- Ensure the definitions of `domain`, `range`, and `pairsup` match the HOL Light definitions
- The proof might be trivial in systems with good automation for relation properties
- You may need to expand the proof steps that `REL_TAC` handles automatically in HOL Light

---

## PERMUTES_DOMRAN

### Name of formal statement
PERMUTES_DOMRAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_DOMRAN = prove
 (`!p s. p permutes s ==> domain p = s /\ range p = s`,
  REL_TAC);;
```

### Informal statement
For any relation $p$ and set $s$, if $p$ permutes $s$, then the domain of $p$ is equal to $s$ and the range of $p$ is equal to $s$.

Formally:
$$\forall p, s. \; p \text{ permutes } s \Rightarrow \text{domain}(p) = s \land \text{range}(p) = s$$

### Informal proof
The proof is accomplished using the `REL_TAC` tactic, which is designed to solve goals about relations.

This is a direct consequence of the definition of a permutation. When $p$ permutes $s$, it means that $p$ is a bijection from $s$ to $s$. By definition:
- A permutation must be defined on all elements of $s$ (so the domain is exactly $s$)
- A permutation must map to all elements of $s$ (so the range is exactly $s$)

The `REL_TAC` tactic automatically derives these properties from the definition of permutation.

### Mathematical insight
This theorem establishes a basic property of permutations represented as relations: permutations have identical domain and range, both equal to the set being permuted.

In mathematical terms, if $p$ is a permutation of $s$, then $p$ is a bijection from $s$ to $s$, which means its domain and range are both exactly $s$.

This result is fundamental for working with permutations as relations in HOL Light. It allows one to easily access the set being permuted by examining either the domain or range of the permutation relation.

### Dependencies
Since the proof uses `REL_TAC`, it likely relies on the fundamental definitions of:
- `permutes` (relation that defines a permutation on a set)
- `domain` (the set of all first components in a relation)
- `range` (the set of all second components in a relation)

### Porting notes
When porting to another system:
- Ensure that permutations are similarly defined as bijective relations
- Check that the target system has equivalent notions of domain and range for relations
- This property might be automatically derived or built into the definition in some systems, especially if they represent permutations differently (e.g., as functions rather than relations)

---

## PAIRSUP_FUNCTIONAL

### Name of formal statement
PAIRSUP_FUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_FUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;
```

### Informal statement
If a binary relation $p$ is a superpair relation (represented by $p \text{ pairsup } (s,t)$), then $p$ is functional in its second argument. Specifically, for all $x$, $y$, and $y'$, if $p(x,y)$ and $p(x,y')$ both hold, then $y = y'$.

Formally, for all binary relations $p$ and sets $s$ and $t$:
$$\forall p, s, t.\ p \text{ pairsup } (s,t) \Rightarrow \forall x, y, y'.\ (p(x,y) \land p(x,y')) \Rightarrow y = y'$$

### Informal proof
This theorem is proven using `REL_TAC`, which is a tactic specifically designed to handle relational properties. The proof follows directly from the definition of a superpair relation.

A superpair relation $p$ between sets $s$ and $t$ is one where:
1. For every $x \in s$, there exists a $y \in t$ such that $p(x,y)$
2. The relation is functional in its second argument

The second property is precisely what this theorem states. The `REL_TAC` tactic automatically derives this property from the definition of `pairsup`.

### Mathematical insight
This theorem establishes a fundamental property of superpair relations: they are functional in their second argument, meaning they behave like functions from the first set to the second. This is an essential characteristic that distinguishes superpair relations from arbitrary binary relations.

The theorem effectively extracts and proves one of the key properties built into the definition of `pairsup`, making this property explicit and available as a separate theorem for use in other proofs.

In the context of set theory and relation algebra, this property ensures that superpair relations can be used to represent functions, which is crucial for many mathematical constructions.

### Dependencies
No explicit dependencies are listed, but the theorem relies on:

- The definition of `pairsup` which defines superpair relations
- The `REL_TAC` tactic which handles relational properties automatically

### Porting notes
When porting this theorem:
- Ensure that your system has an equivalent definition of superpair relations
- The proof may be more explicit in other systems without access to a specialized tactic like `REL_TAC`
- In most systems, this would be proven by directly expanding the definition of `pairsup` and applying basic logic

---

## PERMUTES_FUNCTIONAL

### PERMUTES_FUNCTIONAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PERMUTES_FUNCTIONAL = prove
 (`!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;
```

### Informal statement
The theorem states that if $p$ is a permutation of a set $s$, then $p$ is functional in its second argument. Formally:

For all relations $p$ and sets $s$, if $p$ permutes $s$, then for all elements $x$, $y$, and $y'$, if $p(x,y)$ and $p(x,y')$ hold, then $y = y'$.

In other words, if a relation $p$ is a permutation of set $s$, then for each $x$ in the domain, there can be at most one $y$ in the range such that the pair $(x,y)$ is in the relation $p$.

### Informal proof
The proof is done using the `REL_TAC` tactic, which is designed to prove properties about relations.

The key insight is that a permutation, by definition, establishes a one-to-one correspondence between elements. Since $p$ permutes $s$, it must be both functional and injective:

- When $p(x,y)$ and $p(x,y')$ both hold, we can conclude that $y = y'$ because $p$ must be a function (i.e., each element in the domain maps to exactly one element in the range).

The proof follows directly from the properties of a permutation relation.

### Mathematical insight
This theorem captures an essential property of permutations: they are functional relations. In other words, a permutation defines a function where each input has exactly one corresponding output.

In the context of relation theory, this theorem establishes that permutations are right-unique (functional) relations. Combined with other properties (like being left-unique/injective), this helps characterize permutations as bijective functions between a set and itself.

This property is fundamental when working with permutations in formal mathematics and is part of establishing that permutations correspond to bijective functions.

### Dependencies
The theorem uses the tactic `REL_TAC`, which is designed to prove properties about relations, but no explicit theorem or definition dependencies are listed in the provided information.

### Porting notes
When porting this theorem:
- Ensure your target system has a suitable definition of "permutes" for relations
- Check whether the target system represents relations as sets of pairs or as predicates on pairs
- In some systems, you might need to prove this explicitly using the definition of permutation, especially if there's no direct equivalent to the `REL_TAC` tactic

---

## PAIRSUP_COFUNCTIONAL

I'll revise the documentation to correct the mathematical error in the interpretation of the theorem:

### Name of formal statement
PAIRSUP_COFUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_COFUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;
```

### Informal statement
For all binary relations $p$ and sets $s$ and $t$, if $p$ is related to $s$ and $t$ via the relation `pairsup` (denoted as $p \text{ pairsup } (s,t)$), then $p$ is cofunctional. That is, for all elements $x$, $x'$, and $y$, if both $(x, y) \in p$ and $(x', y) \in p$, then $x = x'$.

### Informal proof
This theorem is proved using `REL_TAC`, which is a tactic specifically designed for proving properties about relations. The tactic automatically verifies that when a relation $p$ satisfies $p \text{ pairsup } (s,t)$, it must be cofunctional.

It's important to note that `pairsup` in HOL Light does not simply denote the standard Cartesian product operation. Rather, $p \text{ pairsup } (s,t)$ expresses that $p$ has a particular relational property with respect to $s$ and $t$ that entails cofunctionality.

The theorem asserts that when $p$ is related to sets $s$ and $t$ via `pairsup`, then for any element $y$, if both $(x, y)$ and $(x', y)$ are in $p$, we must have $x = x'$. This is precisely the definition of a cofunctional relation (sometimes called "right-unique").

### Mathematical insight
This theorem establishes a specific property of relations that satisfy the `pairsup` connection to sets $s$ and $t$ in HOL Light. The cofunctionality property means that for each $y$ in the range of the relation, there is at most one $x$ such that $(x, y)$ belongs to the relation.

In relational theory, a relation is cofunctional (or right-unique) if whenever $(x, y)$ and $(x', y)$ are both in the relation, then $x = x'$. This can be viewed as the relation being injective when considered in the reverse direction.

Note that standard Cartesian products (in the conventional mathematical sense) are not generally cofunctional, as multiple elements from the first set can pair with the same element from the second set. Therefore, `pairsup` in HOL Light must represent a specialized relational construction or constraint that guarantees cofunctionality.

### Dependencies
No explicit dependencies are listed, but this theorem relies on:
- The definition of `pairsup`, which represents a specific relational connection in HOL Light
- The `REL_TAC` tactic, which handles relational reasoning in HOL Light

### Porting notes
When porting this theorem, ensure that:
- The target system's definition of `pairsup` matches HOL Light's meaning, which appears to enforce cofunctionality
- If the target system doesn't have a direct equivalent to `REL_TAC`, you may need to expand the proof to explicitly show the cofunctionality property
- Understand that this isn't about standard Cartesian products, but about a specific relational construction in HOL Light

---

## PERMUTES_COFUNCTIONAL

### Name of formal statement
PERMUTES_COFUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_COFUNCTIONAL = prove
 (`!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;
```

### Informal statement
For any binary relation $p$ and set $s$, if $p$ is a permutation of $s$, then $p$ is co-functional. That is, for all $x$, $x'$, and $y$, if $(x,y) \in p$ and $(x',y) \in p$, then $x = x'$.

### Informal proof
The proof is achieved using the `REL_TAC` tactic, which is designed to automate proofs about relational properties. 

In this case, the tactic establishes that if a relation represents a permutation of a set, then it must be co-functional (also known as right-unique or injective when viewed as a function).

The core of the argument is:
- If $p$ permutes $s$, then $p$ represents a bijective function on $s$
- A bijective function is injective
- If $(x,y) \in p$ and $(x',y) \in p$, then $y$ is mapped from both $x$ and $x'$
- By injectivity, this is only possible if $x = x'$

### Mathematical insight
This theorem captures an essential property of permutations: when viewed as a relation, a permutation must be co-functional. This means that each element in the codomain has exactly one corresponding element in the domain. In functional terms, this is equivalent to saying that the inverse of a permutation is a function, which follows from the bijective nature of permutations.

The result is part of the fundamental characterization of permutations as relations, establishing that they satisfy the properties needed to represent bijective functions.

### Dependencies
No explicit dependencies are listed, but the proof relies on:
- The `REL_TAC` tactic, which handles relational properties
- The definition of `permutes` and related permutation concepts

### Porting notes
When porting this theorem:
- Ensure that your system has an equivalent definition of permutation as a binary relation
- Check if your target system has similar automation for relational properties; if not, you may need to expand the proof to explicitly show that permutations are bijective and therefore co-functional
- The co-functional property is sometimes called "right-unique" or expressed as "if $f y = z$ and $f y' = z$ then $y = y'$" in different formal systems

---

## PAIRSUP_ID

### Name of formal statement
PAIRSUP_ID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_ID = prove
 (`!s. id(s) pairsup (s,s)`,
  REL_TAC);;
```

### Informal statement
For any set $s$, the identity relation on $s$ is in the relation "pairs up" with the Cartesian product $(s, s)$.

In mathematical notation:
$$\forall s. \text{id}(s) \text{ pairsup } (s, s)$$

where $\text{id}(s) = \{(x, x) \mid x \in s\}$ is the identity relation on set $s$.

### Informal proof
The proof is completed using the `REL_TAC` tactic, which is designed to solve simple relational algebra problems.

In this case, it shows that the identity relation on $s$ (which is the set of all pairs $(x,x)$ where $x \in s$) satisfies the "pairs up" relation with $(s,s)$. This means:
- The identity relation is a subset of $s \times s$
- For every $x \in s$, there exists a $y \in s$ such that $(x,y)$ is in the identity relation
- For every $y \in s$, there exists an $x \in s$ such that $(x,y)$ is in the identity relation

These conditions are satisfied because for any $x \in s$, $(x,x)$ is in the identity relation, ensuring both $x$ and $y$ ranges are covered.

### Mathematical insight
This theorem establishes a basic property about the identity relation - that it "pairs up" with the Cartesian product of a set with itself. 

The "pairs up" relation (denoted as `pairsup`) is a concept in relation theory that indicates a relation connects all elements from one set to at least one element in another set, and vice versa. Specifically, a relation $R$ "pairs up" with $(s,t)$ if:
1. $R \subseteq s \times t$
2. $\forall x \in s. \exists y \in t. (x,y) \in R$
3. $\forall y \in t. \exists x \in s. (x,y) \in R$

This theorem confirms that the identity relation is a perfect example of a relation that "pairs up" with a set's self-product, which is intuitive since each element in $s$ is related to exactly itself in the identity relation.

### Dependencies
This theorem relies on relational algebra concepts implemented in HOL Light:
- `id` - the identity relation on a set
- `pairsup` - the "pairs up" relation between relations and Cartesian products
- `REL_TAC` - a special tactic for solving relation-theoretic proofs

### Porting notes
When porting this theorem:
- Ensure the target system has definitions for identity relations and the concept of "pairing up" relations
- The `REL_TAC` tactic in HOL Light handles many relational proofs automatically; in other systems, this might require explicit proof steps showing the three conditions of the "pairs up" relation

---

## PERMUTES_ID

### Name of formal statement
PERMUTES_ID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_ID = prove
 (`!s. id(s) permutes s`,
  REL_TAC);;
```

### Informal statement
For any set $s$, the identity function on $s$ is a permutation of $s$.

Formally, this states that $\forall s. \text{id}(s) \permutes s$, where:
- $\text{id}(s)$ represents the identity function restricted to the set $s$
- $f \permutes s$ means that function $f$ is a permutation of set $s$

### Informal proof
The theorem is proved using the `REL_TAC` tactic, which is designed to prove statements about relations.

For a function to be a permutation of a set, it must be a bijection between the set and itself. The identity function satisfies this property by definition:

- For any $x \in s$, we have $\text{id}(s)(x) = x \in s$, so $\text{id}(s)$ maps elements of $s$ to elements of $s$
- The identity function is injective: if $\text{id}(s)(x) = \text{id}(s)(y)$, then $x = y$
- The identity function is surjective on $s$: for any $y \in s$, there exists $x \in s$ (namely, $x = y$) such that $\text{id}(s)(x) = y$

The `REL_TAC` tactic automatically applies these reasoning steps to establish that the identity function is a permutation.

### Mathematical insight
This theorem establishes one of the basic properties of permutations: the identity function is a permutation. This is a fundamental result in group theory, where the identity permutation is the identity element of the permutation group. In the context of HOL Light's formalization of permutations, this theorem confirms that the identity function satisfies the formal definition of a permutation.

This result is part of the basic infrastructure for working with permutations in HOL Light. It enables reasoning about permutation groups, as the identity permutation is necessary for the group structure.

### Dependencies
No explicit dependencies are listed. The proof relies on the definition of permutation (`permutes`) and the identity function (`id`), as well as the `REL_TAC` tactic which handles relational reasoning.

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it expresses a basic mathematical fact about permutations and the identity function. The definition of permutation might differ slightly between systems, but the concept that the identity function is a permutation of any set is universal.

When porting, ensure that:
1. The definition of "permutes" in the target system corresponds to a bijection on the set
2. The identity function is properly defined or available in the target system
3. The appropriate automation for relational reasoning is applied, as the proof is straightforward

---

## PAIRSUP_CONVERSE

### PAIRSUP_CONVERSE
- PAIRSUP_CONVERSE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PAIRSUP_CONVERSE = prove
 (`!p s t. p pairsup (s,t) ==> converse(p) pairsup (t,s)`,
  REL_TAC);;
```

### Informal statement
For all binary relations $p$ and sets $s$ and $t$, if $p$ has the $\text{pairsup}$ relation between $(s,t)$, then the converse relation $\text{converse}(p)$ has the $\text{pairsup}$ relation between $(t,s)$.

Formally: $\forall p, s, t. \, p \text{ pairsup } (s,t) \Rightarrow \text{converse}(p) \text{ pairsup } (t,s)$

### Informal proof
This theorem is proved using the tactic `REL_TAC`, which is designed to handle relational reasoning. 

The theorem follows directly from the definition of `pairsup` and `converse`. The `pairsup` relation between sets states that $p \text{ pairsup } (s,t)$ means $\forall x \in s, \forall y \in t, p(x,y)$. 

The converse relation $\text{converse}(p)$ is defined as $\text{converse}(p)(x,y) \iff p(y,x)$.

Therefore, if $p \text{ pairsup } (s,t)$, then $\forall x \in s, \forall y \in t, p(x,y)$. 
By the definition of converse, this means $\forall y \in t, \forall x \in s, \text{converse}(p)(y,x)$.
This is precisely the statement that $\text{converse}(p) \text{ pairsup } (t,s)$.

### Mathematical insight
This theorem captures a fundamental property of the relationship between the `pairsup` relation and the `converse` operation on binary relations. It demonstrates the duality that exists when reversing both the order of sets in a pair and the direction of a relation. 

The `pairsup` relation extends a binary relation on elements to a relation on sets, stating that every element of the first set is related to every element of the second set. This theorem shows that if we reverse the relation and swap the order of sets, the `pairsup` property is preserved.

This result is useful in relational algebra and set theory, providing a tool for transforming relational expressions while preserving their semantic meaning.

### Dependencies
No explicit dependencies are listed in the provided information, though the theorem relies on the definitions of `pairsup` and `converse` in HOL Light.

### Porting notes
When porting to other proof assistants:
- Ensure that the `pairsup` relation and `converse` operation are defined in the target system
- Most systems have built-in support for relational algebra, so the proof might be straightforward
- The `REL_TAC` tactic used in HOL Light is a specialized tactic for relational reasoning - in other systems, you might need to construct an equivalent proof using more basic tactics or use a similar specialized tactic if available

---

## PERMUTES_CONVERSE

### Name of formal statement
PERMUTES_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_CONVERSE = prove
 (`!p s. p permutes s ==> converse(p) permutes s`,
  REL_TAC);;
```

### Informal statement
For all relations $p$ and sets $s$, if $p$ permutes $s$, then the converse of $p$ also permutes $s$.

More formally: $\forall p, s. \, p \text{ permutes } s \Rightarrow \text{converse}(p) \text{ permutes } s$

### Informal proof
This theorem is proven using `REL_TAC`, which is a high-level tactic for proving basic properties of relations in HOL Light. 

The underlying proof follows from the definition of a permutation relation:
- If $p$ permutes $s$, then $p$ is a bijective relation on $s$
- The converse of a bijective relation is also bijective
- Therefore, the converse of $p$ also permutes $s$

`REL_TAC` handles these steps automatically by applying the appropriate relation theory results.

### Mathematical insight
This theorem establishes that the inverse of a permutation is also a permutation on the same set. In set-theoretic terms, if we represent a permutation as a relation $p$ that defines a bijection on set $s$, then the converse relation $\text{converse}(p)$ (which essentially swaps the domain and range) also defines a permutation on $s$.

This is a fundamental property of permutations that corresponds to the fact that the inverse of a bijective function is also bijective. In group theory, this reflects the fact that the inverse of an element in a permutation group is also in the group.

### Dependencies
No specific dependencies were provided in the list, but this theorem inherently relies on:
- The definition of `permutes` in HOL Light
- Properties of relations and their converses
- The relationship between permutations and bijections

### Porting notes
When porting to another system:
- Ensure the target system has a compatible definition of permutations as relations
- Check if "converse" has a different name in the target system (often called "inverse" or "transpose")
- The proof may be more direct in systems with extensive relation libraries

---

## PAIRSUP_COMPOSE

### Name of formal statement
PAIRSUP_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_COMPOSE = prove
 (`!p p' s t u. p pairsup (s,t) /\ p' pairsup (t,u) ==> (p % p') pairsup (s,u)`,
  REL_TAC);;
```

### Informal statement
For any relations $p$, $p'$ and sets $s$, $t$, $u$, if $p$ is an upper bound relation on the pair $(s,t)$ and $p'$ is an upper bound relation on the pair $(t,u)$, then the composition of $p$ and $p'$ is an upper bound relation on the pair $(s,u)$.

Formally: 
$$\forall p, p', s, t, u.\; p \text{ pairsup } (s,t) \land p' \text{ pairsup } (t,u) \Rightarrow (p \circ p') \text{ pairsup } (s,u)$$

where $\text{pairsup}$ denotes that the relation is an upper bound relation on the given pair of sets.

### Informal proof
The proof uses the `REL_TAC` tactic, which is designed to handle relational reasoning. For this specific theorem:

* The proof unfolds the definition of `pairsup`, which states that a relation $p$ is an upper bound relation on $(s,t)$ if for every $x \in s$, there exists $y \in t$ such that $p(x,y)$ holds.

* For the composition $(p \circ p')$ to be an upper bound relation on $(s,u)$, we need to show that for every $x \in s$, there exists $z \in u$ such that $(p \circ p')(x,z)$ holds.

* Given $x \in s$, by the first hypothesis, there exists $y \in t$ such that $p(x,y)$ holds.

* Then, by the second hypothesis, for this $y \in t$, there exists $z \in u$ such that $p'(y,z)$ holds.

* By the definition of relation composition, $(p \circ p')(x,z)$ holds if there exists a $y$ such that $p(x,y)$ and $p'(y,z)$ both hold, which we have established.

* Therefore, $(p \circ p')$ is an upper bound relation on $(s,u)$.

### Mathematical insight
This theorem establishes a fundamental property of upper bound relations: they compose transitively. This is important for relational calculus and category theory, as it shows that the composition of upper bound relations maintains the upper bound property across related pairs of sets.

The result can be seen as a formalization of the intuition that if we can "go up" from elements of $s$ to elements of $t$ via relation $p$, and from elements of $t$ to elements of $u$ via relation $p'$, then we can "go up" directly from elements of $s$ to elements of $u$ via the composition of these relations.

This theorem is particularly useful in formal constructions involving relations, such as when building Galois connections or when reasoning about relationship between sets in order theory.

### Dependencies
This theorem relies on the relational machinery in HOL Light, particularly:

- The definition of `pairsup`, which characterizes when a relation is an upper bound relation on a pair of sets
- The definition of relation composition (`%` operator)
- The `REL_TAC` tactic, which handles standard reasoning about relations

### Porting notes
When porting this theorem:
- Ensure the target system has equivalent definitions for relation composition and upper bound relations
- The proof is simple enough that it should be straightforward to reproduce using the target system's relational reasoning capabilities
- Be aware that different systems may use different syntax for relation composition (in HOL Light it's `%` but other systems might use `∘` or explicit notation)

---

## PERMUTES_COMPOSE

### Name of formal statement
PERMUTES_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_COMPOSE = prove
 (`!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s`,
  REL_TAC);;
```

### Informal statement
For all functions $p, p'$ and a set $s$, if $p$ permutes $s$ and $p'$ permutes $s$, then the composition $p \circ p'$ also permutes $s$.

### Informal proof
This theorem is proven using `REL_TAC`, which is a tactic designed to prove results about relations, functions, and their properties. For permutation-related theorems, it automatically handles the verification that function composition preserves permutation properties.

The proof essentially establishes that when two functions are permutations of the same set:
1. Their composition is a bijection on the set
2. The composition maps elements of the set back to the same set

Since these are precisely the conditions for a function to be a permutation of a set, the theorem follows directly.

### Mathematical insight
This theorem establishes an important algebraic property of permutations: they form a group under composition. Specifically, this theorem proves the closure property of permutations - that the composition of two permutations is again a permutation.

This is a fundamental result in group theory, particularly for the study of permutation groups. It allows us to combine permutations to create new permutations while preserving the essential structure of the set being permuted.

### Dependencies
The proof uses `REL_TAC`, a specialized tactic for proving results about relations and functions.

### Porting notes
When porting this theorem:
1. Ensure that your target system has a suitable definition of "permutes" that captures the notion of a function being a permutation of a set.
2. The proof might need to be expanded in systems without direct equivalents to `REL_TAC`. In those cases, you would need to explicitly prove that composition preserves the bijection property and that the composition maps elements within the set.
3. This result is straightforward in most systems that have basic permutation theory available.

---

## PERMUTES_SWAP

### PERMUTES_SWAP
- The formal statement name is `PERMUTES_SWAP`.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PERMUTES_SWAP = prove
 (`swap(a,b) permutes {a,b}`,
  REL_TAC);;
```

### Informal statement
The swap function $\text{swap}(a,b)$ is a permutation of the set $\{a,b\}$.

More formally, it states that the transposition that exchanges $a$ and $b$ is a permutation of the two-element set $\{a,b\}$.

### Informal proof
The proof uses the relational tactic (`REL_TAC`) which establishes the result by showing that `swap(a,b)` satisfies the properties of a permutation on the set $\{a,b\}$.

A permutation is a bijective function from a set to itself. The `swap(a,b)` function:
- Maps $a$ to $b$
- Maps $b$ to $a$
- Leaves all other elements unchanged

Since `swap(a,b)` is bijective on $\{a,b\}$ (it's both injective and surjective), it constitutes a permutation of this set.

### Mathematical insight
This theorem establishes a fundamental property of transpositions (swaps): they are permutations on the elements being swapped. Transpositions are important because they form the building blocks of permutation theory - any permutation can be expressed as a composition of transpositions.

The swap function is the simplest non-trivial permutation possible, and this theorem formalizes that this basic operation indeed satisfies the mathematical definition of a permutation on the set containing exactly the two elements being swapped.

This result serves as a foundational component for developing more complex permutation theory in HOL Light.

### Dependencies
No explicit dependencies are listed, but the proof relies on:
- The definition of `swap`
- The definition of `permutes` (a predicate that determines if a function is a permutation of a set)
- The `REL_TAC` tactic which establishes relational properties

### Porting notes
When porting this theorem:
1. Ensure the definitions of `swap` and `permutes` are properly established first
2. In most systems, this proof will be straightforward, potentially using tactics that establish basic properties of functions and relations
3. Some systems might require an explicit proof showing both injectivity and surjectivity of the swap function on the set $\{a,b\}$

---

## PAIRSUP_EMPTY

### PAIRSUP_EMPTY
- `PAIRSUP_EMPTY`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let PAIRSUP_EMPTY = prove
 (`p pairsup ({},{}) <=> (p = {})`,
  REL_TAC);;
```

### Informal statement
This theorem characterizes when a binary relation `p` is a pairwise supremum (pairsup) relation for the pair of empty sets. Specifically, it states:

$$p \text{ pairsup } (\emptyset, \emptyset) \iff (p = \emptyset)$$

Where "pairsup" represents a binary relation that contains all ordered pairs of suprema between elements of two sets.

### Informal proof
The proof uses the tactic `REL_TAC`, which is designed to solve goals about relational properties. In this case, it's proving that:

When we consider the pairwise supremum relation between two empty sets, the resulting relation must be empty.

This follows directly from the definition of pairwise supremum: since there are no elements in either of the empty sets, there are no pairs of elements to take suprema of, resulting in an empty relation.

### Mathematical insight
This theorem establishes a base case for the `pairsup` relation when both input sets are empty. It confirms the intuitive notion that the pairwise supremum relation between empty sets must itself be empty, as there are no elements to form pairs with.

This result is part of a collection of "clausal theorems" that characterize the behavior of the `pairsup` relation under different set configurations, making it easier to reason about this relation in proofs.

### Dependencies
The proof uses `REL_TAC`, which is a tactic specifically designed for relational reasoning.

### Porting notes
When porting this theorem:
- Ensure that your target system has a corresponding definition of the `pairsup` relation with the same semantics
- The automated tactic `REL_TAC` simplifies the proof in HOL Light, but in other proof assistants, you may need to expand the definition of `pairsup` and reason explicitly about the emptiness of the relations

---

## PAIRSUP_INSERT

### Name of formal statement
PAIRSUP_INSERT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_INSERT = prove
 (`!x:A s t:B->bool p.
        p pairsup (x INSERT s,t) <=>
          if x IN s then p pairsup (s,t)
          else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `x IN s ==> x INSERT s = s`] THEN EQ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `?y. y IN t /\ p(x:A,y:B)` MP_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  EXISTS_TAC `p DELETE (x:A,y:B)` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC);;
```

### Informal statement
For any element $x$ of type $A$, sets $s$ of type $A$ and $t$ of type $B \to \text{bool}$ (representing a set of elements of type $B$), and a relation $p$, the following equivalence holds:

$$p \text{ pairsup } (x \text{ INSERT } s, t) \iff 
\begin{cases}
p \text{ pairsup } (s, t) & \text{if } x \in s \\
\exists y, q.\ y \in t \land p = (x, y) \text{ INSERT } q \land q \text{ pairsup } (s, t \text{ DELETE } y) & \text{otherwise}
\end{cases}$$

where "pairsup" represents the set of all unordered pairs formed by choosing one element from each set.

### Informal proof
The proof proceeds by case analysis on whether $x \in s$:

* If $x \in s$, then $x \text{ INSERT } s = s$ (by the SET_RULE), so $p \text{ pairsup } (x \text{ INSERT } s, t) = p \text{ pairsup } (s, t)$, making the equivalence trivial.

* If $x \not\in s$, we prove the bidirectional implication:
  - For the forward direction ($\Rightarrow$):
    1. Assume $p \text{ pairsup } (x \text{ INSERT } s, t)$.
    2. We show there exists $y \in t$ such that $(x,y) \in p$ using the pairsup relation properties.
    3. For such a $y$, we define $q = p \setminus \{(x,y)\}$.
    4. Then prove that $q \text{ pairsup } (s, t \setminus \{y\})$, completing the forward direction.

  - For the backward direction ($\Leftarrow$):
    1. Assume there exists $y \in t$ and relation $q$ such that $p = (x,y) \text{ INSERT } q$ and $q \text{ pairsup } (s, t \text{ DELETE } y)$.
    2. By applying the definition of pairsup to these assumptions, we can derive $p \text{ pairsup } (x \text{ INSERT } s, t)$.

The proof uses the REL_TAC tactic to handle the reasoning about relations, effectively working with the definition of the pairsup relation.

### Mathematical insight
This theorem characterizes how the "pairsup" relation behaves when we insert an element into the first set. The insight is that:

1. If the element is already in the set, nothing changes.
2. If the element is new, then it must be paired with some element from the second set, and the rest of the relation pairs elements from the original first set with the remaining elements of the second set.

This provides an inductive characterization of the pairsup relation, which is useful for proofs about set operations and relations involving pairs of elements from different sets.

### Dependencies
No explicit dependencies were provided, but the proof uses:
- SET_RULE for set properties
- REL_TAC for reasoning about relations

### Porting notes
When porting this theorem:
- Ensure the "pairsup" relation is properly defined in the target system
- The conditional expression may require different syntax in other systems
- The relation properties used by REL_TAC might need explicit handling in systems without equivalent tactics

---

## NUMBER_OF_PAIRINGS

### NUMBER_OF_PAIRINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMBER_OF_PAIRINGS = prove
 (`!n s:A->bool t:B->bool.
        s HAS_SIZE n /\ t HAS_SIZE n
        ==> {p | p pairsup (s,t)} HAS_SIZE (FACT n)`,
  let lemma = prove
   (`{p | ?y. y IN t /\ A y p} = UNIONS {{p | A y p} | y IN t} /\
     {p | ?q. p = (a,y) INSERT q /\ A y q} =
           IMAGE (\q. (a,y) INSERT q) {q | A y q}`,
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN SET_TAC[]) in
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
    SIMP_TAC[PAIRSUP_EMPTY; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH; FACT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[PAIRSUP_INSERT; RIGHT_EXISTS_AND_THM; lemma; FACT] THEN
  MATCH_MP_TAC HAS_SIZE_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE_SUC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;
```

### Informal statement
For any natural number $n$ and sets $s \subseteq A$ and $t \subseteq B$ such that both $s$ and $t$ have size $n$, the set of all pairings between $s$ and $t$ has size $n!$ (factorial of $n$).

Formally:
$$\forall n \in \mathbb{N}, \forall s \subseteq A, \forall t \subseteq B. |s| = n \land |t| = n \implies |\{p \mid p \text{ pairs up } (s,t)\}| = n!$$

where $p$ "pairs up" $(s,t)$ means $p$ is a bijective relation between $s$ and $t$.

### Informal proof
The proof proceeds by induction on $n$.

**Base case ($n=0$):**
- When $n=0$, both $s$ and $t$ are empty sets.
- The only possible pairing between empty sets is the empty relation.
- Therefore, the set of pairings has size $0! = 1$.

**Inductive case ($n+1$):**
- Assume $s$ has size $n+1$ with some element $a \in s$, and $t$ has size $n+1$ with some element $b \in t$.
- Let $s' = s \setminus \{a\}$ and $t' = t \setminus \{b\}$.
- By the definition of `PAIRSUP_INSERT`, a pairing between $s$ and $t$ can be constructed by:
  1. Choosing an element $y \in t$
  2. Pairing $a$ with $y$
  3. Creating a pairing between $s'$ and $t \setminus \{y\}$

- This gives us a union of sets: $\bigcup_{y \in t} \{p \mid p \text{ is a pairing with } (a,y) \}$
- For each $y \in t$, there are $n!$ ways to pair up the remaining elements (by induction hypothesis).
- These sets are disjoint (since each assigns a different element to be paired with $a$).
- There are $(n+1)$ choices for $y$.
- Therefore, the total number of pairings is $(n+1) \times n! = (n+1)!$

### Mathematical insight
This theorem establishes that the number of ways to create a perfect matching (bijective pairing) between two sets of equal size $n$ is $n!$. This is equivalent to counting the number of permutations of $n$ elements, as each pairing corresponds to a unique permutation.

The result is fundamental in combinatorics and can be interpreted in several ways:
1. The number of bijections between two sets of size $n$
2. The number of ways to arrange $n$ distinct objects in $n$ distinct positions
3. The number of perfect matchings in a complete bipartite graph $K_{n,n}$

### Dependencies
- Theorems:
  - `HAS_SIZE_CLAUSES`: Relates the size of sets to their cardinality
  - `PAIRSUP_EMPTY`: Characterizes pairings between empty sets
  - `PAIRSUP_INSERT`: Describes how to construct pairings when inserting elements
  - `HAS_SIZE_SUC`: Relates the size of a set after adding an element
  - `HAS_SIZE_UNIONS`: Gives the size of a union of disjoint sets
  - `HAS_SIZE_IMAGE_INJ`: Preserves size under injective mappings

### Porting notes
When porting to other systems:
1. Ensure that the definition of "pairing up" (bijective relation) is properly established
2. The proof relies on set-theoretic manipulations and induction, which should be available in most systems
3. The tactic `REL_TAC` in HOL Light helps with relational reasoning - equivalent tactics or more explicit reasoning may be needed in other systems
4. The nested lemma about set operations might need to be proved separately in systems with different automation capabilities

---

## NUMBER_OF_PERMUTATIONS

### NUMBER_OF_PERMUTATIONS
- `NUMBER_OF_PERMUTATIONS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NUMBER_OF_PERMUTATIONS = prove
 (`!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`,
  SIMP_TAC[permutes; NUMBER_OF_PAIRINGS]);;
```

### Informal statement
For any set $s$ and natural number $n$, if $s$ has size $n$ (i.e., $s$ contains exactly $n$ elements), then the set of all permutations of $s$ has size $n!$ (factorial of $n$).

More formally, $\forall s, n. \, |s| = n \implies |\{p \mid p \text{ permutes } s\}| = n!$

### Informal proof
The proof employs a direct simplification approach using the definition of permutations and a related theorem about the number of pairings.

The theorem relies on two key dependencies:
1. The definition of what it means for a function to permute a set
2. A previous result about the number of pairings (likely establishing that the number of bijections between two sets of the same finite size is the factorial of their size)

The proof is completed by applying the simplification tactic with these dependencies, which directly establishes that the set of permutations of a finite set of size $n$ has size $n!$.

### Mathematical insight
This result provides a fundamental counting principle in combinatorics: the number of ways to arrange $n$ distinct objects is $n!$. In the formal context, it counts the number of permutation functions on a finite set.

The theorem is important because:
1. It formalizes a core combinatorial principle
2. It serves as a building block for more complex counting arguments in formal mathematics
3. It connects the abstract concept of permutations (as bijective functions) to their concrete enumeration

### Dependencies
- Theorems:
  - `NUMBER_OF_PAIRINGS` - likely establishes the counting principle for bijections between finite sets

- Definitions:
  - `permutes` - defines what it means for a function to be a permutation of a set
  - `HAS_SIZE` - defines what it means for a set to have a specific finite size
  - `FACT` - factorial function

### Porting notes
When porting to another system:
1. Ensure that permutations are defined as bijective functions on a set
2. The underlying theorem `NUMBER_OF_PAIRINGS` will likely need to be ported first
3. The proof relies on simplification tactics to resolve the goal, so in systems with less powerful automation, additional explicit steps might be required

---

## derangements

### Name of formal statement
derangements

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let derangements = define
 `(derangements 0 = 1) /\
  (derangements 1 = 0) /\
  (derangements(n + 2) = (n + 1) * (derangements n + derangements(n + 1)))`;;
```

### Informal statement
The `derangements` function defines the number of derangements of a set with $n$ elements, where a derangement is a permutation with no fixed points. The function is defined recursively as follows:

- $\text{derangements}(0) = 1$
- $\text{derangements}(1) = 0$
- $\text{derangements}(n + 2) = (n + 1) \cdot (\text{derangements}(n) + \text{derangements}(n + 1))$ for $n \geq 0$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition captures the number of permutations of a set that have no fixed points (i.e., no element maps to itself). The recurrence relation has a combinatorial interpretation:

- $\text{derangements}(0) = 1$ represents that there is exactly one way to arrange an empty set (the empty arrangement).
- $\text{derangements}(1) = 0$ reflects that it's impossible to derange a singleton set (the only element must map to itself, creating a fixed point).
- The recursive formula $\text{derangements}(n + 2) = (n + 1) \cdot (\text{derangements}(n) + \text{derangements}(n + 1))$ can be derived through a combinatorial argument:
  - When considering derangements of $n+2$ elements, we can look at where element $n+2$ goes.
  - If element $n+2$ goes to position $i$, then element $i$ can't go to position $n+2$ (or else we'd have a 2-cycle and not a complete derangement).
  - This leads to the recurrence relation after accounting for all possibilities.

This definition is essential in combinatorics and probability theory, with applications in the classic "hat-check problem" and computation of the probability of a random permutation having no fixed points.

### Dependencies
None specified in the information provided.

### Porting notes
When porting this definition to other proof assistants, take care with:
- The base cases (especially the fact that derangements(0) = 1, which might seem counterintuitive)
- The recursive pattern, which follows a second-order recurrence relation
- Some systems might require explicit termination arguments for recursive definitions

---

## DERANGEMENT_INDUCT

### Name of formal statement
DERANGEMENT_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;
```

### Informal statement
For any predicate $P$ on natural numbers, if:
1. $P(0)$ holds,
2. $P(1)$ holds, and
3. For all $n$, if both $P(n)$ and $P(n+1)$ hold, then $P(n+2)$ holds,

then $P(n)$ holds for all natural numbers $n$.

### Informal proof
The proof uses a strengthened induction claim and proceeds as follows:

1. We strengthen the goal by proving: "For all $n$, both $P(n)$ and $P(n+1)$ hold."
   This is stronger than the original goal and implies it immediately.

2. The strengthened claim is proven by mathematical induction on $n$:
   - Base case: Need to show $P(0)$ and $P(1)$ both hold, which we have by assumption.
   - Inductive step: Assume $P(n)$ and $P(n+1)$ for some $n$. We need to show:
     $P(n+1)$ and $P(n+2)$ hold.
     * We already know $P(n+1)$ from the induction hypothesis.
     * From the original third assumption and the induction hypothesis, 
       since $P(n)$ and $P(n+1)$ hold, we can derive that $P(n+2)$ holds.

3. This completes the induction, establishing that for all $n$, both $P(n)$ and $P(n+1)$ hold.
   Therefore, for all $n$, $P(n)$ holds.

### Mathematical insight
This theorem provides a specialized induction principle tailored for recursively defined sequences where each new term depends on the two preceding terms, similar to how Fibonacci numbers are defined. The name "DERANGEMENT_INDUCT" suggests it might be particularly useful for reasoning about derangements (permutations with no fixed points), whose counting sequence follows a second-order recurrence relation.

The key insight is that when working with second-order recurrence relations, it's often more convenient to prove properties simultaneously for consecutive terms rather than just individual terms. This theorem formalizes that approach by requiring the base cases for $n=0$ and $n=1$, and then providing a way to derive all subsequent cases.

### Dependencies
No explicit dependencies are listed, but the proof uses:
- Basic natural number arithmetic (`ADD1`, `ADD_ASSOC`, `ARITH`)
- Standard HOL Light tactics (`MESON_TAC`, `INDUCT_TAC`, `ASM_SIMP_TAC`)

### Porting notes
When porting to other systems:
- This is a fairly standard mathematical induction principle with a twist for second-order recurrences.
- Ensure that the target system can handle the strengthened induction hypothesis (proving a conjunction in the induction step).
- The proof is straightforward and should translate well to most proof assistants with basic induction and arithmetic capabilities.
- The name suggests a specific use case for derangements, but the theorem itself is general and could be used for any sequence with a second-order recurrence relation.

---

## DERANGEMENT_ADD2

### DERANGEMENT_ADD2
- `DERANGEMENT_ADD2`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD2 = prove
 (`!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`,
  REL_TAC);;
```

### Informal statement
For any relation $p$, set $s$, and elements $x$ and $y$, if:
- $p$ deranges $s$ (i.e., $p$ is a derangement of $s$)
- $x \notin s$
- $y \notin s$
- $x \neq y$

Then the relation $\{(x,y), (y,x)\} \cup p$ deranges the set $\{x, y\} \cup s$.

### Informal proof
The theorem is proven using the `REL_TAC` tactic, which is specialized for proving results about relations. 

The key idea of the proof is:
- We start with a derangement $p$ of set $s$
- We add two new elements $x$ and $y$ to the set $s$
- We extend the relation $p$ by adding two pairs $(x,y)$ and $(y,x)$
- These additions maintain the derangement property: 
  - Each element in the new set gets mapped to a different element
  - No element maps to itself

The `REL_TAC` tactic automatically handles the verification of the derangement properties for the extended relation and set.

### Mathematical insight
This theorem shows how to extend a derangement by adding two new elements. The key insight is that when adding new elements $x$ and $y$ to a set, you can maintain the derangement property by having them map to each other (adding both $(x,y)$ and $(y,x)$ to the relation).

This is an important construction for building larger derangements from smaller ones. A derangement is a permutation with no fixed points, and this theorem gives a simple way to grow derangements incrementally by adding pairs of elements that map to each other.

The result is useful in combinatorial contexts, particularly in counting and constructing derangements of sets.

### Dependencies
No explicit dependencies are listed in the information provided. However, the theorem relies on:
- The definition of "deranges" (a relation that represents a derangement)
- The `REL_TAC` tactic which handles relational reasoning

### Porting notes
When porting to other proof assistants:
- Ensure the definition of "deranges" is properly ported first
- The `REL_TAC` tactic in HOL Light automates much of the proof - other systems may require more explicit proof steps to verify that the extended relation is indeed a derangement
- The set operations and pair notation should translate straightforwardly to most systems, but some may use different syntax for relation operations

---

## DERANGEMENT_ADD1

### Name of formal statement
DERANGEMENT_ADD1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD1 = prove
 (`!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)`,
  REL_TAC);;
```

### Informal statement
For any relation $p$, set $s$, and elements $y$ and $x$, if:
- $p$ is a derangement of the set $s$ (i.e., $p$ is a bijection on $s$ where no element maps to itself)
- $y$ is not an element of $s$ (i.e., $y \notin s$)
- $(x,z) \in p$ for some $z$

Then the relation $\{(x,y), (y,z)\} \cup (p \setminus \{(x,z)\})$ is a derangement of the set $s \cup \{y\}$.

### Informal proof
This theorem is proved using the `REL_TAC` tactic, which is designed to handle relation-based proofs. The proof likely proceeds as follows:

1. Start with the given conditions: $p$ is a derangement of $s$, $y \notin s$, and $(x,z) \in p$.
2. Define the new relation $q = \{(x,y), (y,z)\} \cup (p \setminus \{(x,z)\})$.
3. Verify that $q$ is a bijection on $s \cup \{y\}$:
   - $q$ is a function: For each element in $s \cup \{y\}$, there is exactly one corresponding element.
   - $q$ is injective: If $q(a) = q(b)$, then $a = b$.
   - $q$ is surjective: For every element in $s \cup \{y\}$, there exists an element that maps to it.
4. Verify that $q$ is a derangement: For each $a \in s \cup \{y\}$, $q(a) \neq a$.
   - In particular, $q(x) = y \neq x$ (since $x \in s$ and $y \notin s$)
   - $q(y) = z \neq y$ (since $z \in s$ and $y \notin s$)
   - For other elements $a \in s \setminus \{x\}$, $q(a) = p(a) \neq a$ (since $p$ is a derangement of $s$)

### Mathematical insight
This theorem provides a method to extend a derangement of a set to include one additional element. Specifically, it shows how to modify an existing derangement $p$ of set $s$ to create a derangement of $s \cup \{y\}$ when adding a new element $y$.

The key insight is the specific modification to the relation: remove one pair $(x,z)$ from the original derangement and replace it with two pairs $(x,y)$ and $(y,z)$. This creates a "chain" where $x$ now maps to $y$ (the new element), which in turn maps to $z$. The result preserves the derangement property (no element maps to itself) while incorporating the new element into the bijection.

This construction is useful for inductive proofs about derangements or for building larger derangements from smaller ones.

### Dependencies
- The theorem likely depends on definitions of derangements and set operations, though specific dependencies are not provided in the input.
- The proof uses `REL_TAC`, a tactic designed for relation-based proofs in HOL Light.

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the definition of "deranges" is correctly translated (a derangement is a bijection where no element maps to itself)
- Note that the theorem assumes relations are represented as sets of ordered pairs
- The proof might require careful handling of relation/function composition and set operations in the target system

---

## DERANGEMENT_EMPTY

### DERANGEMENT_EMPTY
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DERANGEMENT_EMPTY = prove
 (`!p. p deranges {} <=> p = {}`,
  REL_TAC);;
```

### Informal statement
The theorem states that for any permutation $p$, $p$ deranges the empty set if and only if $p$ is the empty set.

Formally:
$$\forall p. \, p \text{ deranges } \emptyset \iff p = \emptyset$$

Where "deranges" refers to a permutation that has no fixed points (i.e., for all elements in the domain, the permutation maps them to different elements).

### Informal proof
This theorem is proved using `REL_TAC`, which is a tactic in HOL Light that automatically proves properties about relations.

The proof follows from the definition of a derangement. Since a derangement of a set is a permutation where no element is mapped to itself, and the empty set contains no elements, the only permutation that can derange the empty set is the empty permutation (which is the empty set when considered as a relation).

### Mathematical insight
This theorem establishes the base case for reasoning about derangements of sets. A derangement is a permutation with no fixed points, and this theorem confirms the edge case that there is exactly one way to derange the empty set - with the empty permutation.

This result is important for recursive calculations or inductive proofs involving derangements, as it provides a clear boundary condition.

### Dependencies
No explicit dependencies are listed in the provided information, but the proof likely relies on:

- The definition of what it means for a permutation to "derange" a set
- Basic properties of the empty set
- Relation theory in HOL Light

### Porting notes
When porting this theorem to other systems:
- Ensure that the definition of "deranges" is correctly implemented
- The proof might be simple enough in most systems to be handled by basic automation or rewriting with the definition
- Note that in some proof assistants, the empty relation may be represented differently than simply as the empty set

---

## DERANGEMENT_SING

### DERANGEMENT_SING
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DERANGEMENT_SING = prove
 (`!x p. ~(p deranges {x})`,
  REL_TAC);;
```

### Informal statement
For any element $x$ and any permutation $p$, $p$ does not derange the singleton set $\{x\}$.

Here, "deranges" means that $p$ is a permutation that moves every element of the set (i.e., for every $x$ in the set, $p(x) \neq x$).

### Informal proof
The theorem is proved using `REL_TAC`, which is a tactic for handling relational reasoning. In this case, it shows that a singleton set $\{x\}$ cannot be deranged because:

- A derangement must move every element in the set.
- For a permutation on a singleton set $\{x\}$, the only possible mapping is $p(x) = x$.
- Therefore, $p$ cannot derange $\{x\}$ because it cannot move the single element.

The proof follows directly from the definition of derangement and the constraints of permutations on singleton sets.

### Mathematical insight
This theorem establishes a fundamental limit on derangements: a singleton set cannot be deranged. Intuitively, this makes sense because:

1. A permutation on a singleton set $\{x\}$ must map $x$ to some element in the set.
2. Since there is only one element ($x$ itself), the permutation must map $x$ to $x$.
3. By definition, a derangement requires that no element maps to itself.

This result is a building block for understanding derangements on larger sets, establishing the base case that derangements require sets with at least two elements.

### Dependencies
No explicit dependencies are provided, but the theorem relies on the definition of "deranges" which would specify that a permutation deranges a set when it moves every element of that set (i.e., $\forall x \in S. p(x) \neq x$).

### Porting notes
When porting this theorem:
- Ensure your target system has a definition of permutations and derangements.
- The proof is straightforward and should be easily provable in most systems through direct application of the definitions.
- In more explicit proof assistants, you might need to explicitly show that any permutation on a singleton must be the identity on that element.

---

## NUMBER_OF_DERANGEMENTS

### NUMBER_OF_DERANGEMENTS
- `NUMBER_OF_DERANGEMENTS`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let NUMBER_OF_DERANGEMENTS = prove
 (`!n s:A->bool. s HAS_SIZE n ==> {p | p deranges s} HAS_SIZE (derangements n)`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[derangements] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `{}:A#A->bool` THEN
    ASM_REWRITE_TAC[DERANGEMENT_EMPTY; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN MESON_TAC[MEMBER_NOT_EMPTY];
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[DERANGEMENT_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN X_GEN_TAC `t:A->bool` THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `{p | p deranges (x:A INSERT s)} =
        (IMAGE (\(y,p). (x,y) INSERT (y,x) INSERT p)
               {(y,p) | y IN s /\ p IN {p | p deranges (s DELETE y)}}) UNION
        (IMAGE (\(y,p). let z = @z. p(x,z) in
                        (x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
               {(y,p) | y IN s /\
                        p IN {p | p deranges (x INSERT (s DELETE y))}})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[TAUT `(a <=> b) <=> (b ==> a) /\ (a ==> b)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNION; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`;
                  FORALL_AND_THM; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
      STRIP_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
         `y IN s ==> s = y INSERT (s DELETE y)`)) THEN
        MATCH_MP_TAC DERANGEMENT_ADD2 THEN ASM_REWRITE_TAC[IN_DELETE] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `z = @z. p(x:A,z:A)` THEN
      SUBGOAL_THEN `(p:A#A->bool)(x:A,z:A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `z:A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `(x:A) INSERT s = y INSERT (x INSERT (s DELETE y))`
      SUBST1_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC DERANGEMENT_ADD1 THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_INSERT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:A#A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y. y IN s /\ p(x:A,y:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN ASM_CASES_TAC `(p:A#A->bool)(y,x)` THENL
     [DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `y:A,(p DELETE (y,x)) DELETE (x:A,y:A)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PAIR_BETA_THM] THEN MAP_EVERY UNDISCH_TAC
         [`(p:A#A->bool)(x,y)`; `(p:A#A->bool)(y,x)`] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?z. p(y:A,z:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z:A IN s` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_BETA_THM] THEN
    EXISTS_TAC `y:A` THEN
    EXISTS_TAC `(x:A,z:A) INSERT ((p DELETE (x,y)) DELETE (y,z))` THEN
    SUBGOAL_THEN
     `(@w:A. ((x,z) INSERT (p DELETE (x,y) DELETE (y,z))) (x,w)) = z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; PAIR_BETA_THM] THEN
      REWRITE_TAC[IN; INSERT; DELETE; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
      ASM_CASES_TAC `u:A = x` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REWRITE_TAC[FUN_EQ_THM; INSERT; IN_ELIM_THM; FORALL_PAIR_THM;
                  PAIR_EQ] THEN
      UNDISCH_TAC `~(x:A IN s)` THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:A->bool) HAS_SIZE (n + 1)` THEN
    SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    ASM_REWRITE_TAC[ADD_SUB];

    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN MAP_EVERY X_GEN_TAC
       [`y:A`; `p:(A#A)->bool`; `y':A`; `p':(A#A->bool)`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      MAP_EVERY ABBREV_TAC [`z = @z. p(x:A,z:A)`; `z' = @z. p'(x:A,z:A)`] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `p(x:A,z:A) /\ p'(x:A,z':A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONJ_TAC THEN CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
      SUBGOAL_THEN `z:A IN s /\ z':A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
                           CONJ_TAC THEN MP_TAC th)
      THENL
       [DISCH_THEN(MP_TAC o C AP_THM `(x:A,y:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `z':A = z` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC;
        DISCH_THEN(MP_TAC o C AP_THM `(y:A,z:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `a INSERT b INSERT s = a INSERT b INSERT t
        ==> ~(a IN s) /\ ~(a IN t) /\ ~(b IN s) /\ ~(b IN t) ==> s = t`)) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:A->bool) HAS_SIZE n + 1` THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE] THEN
    ASM_SIMP_TAC[CARD_DELETE; CARD_CLAUSES; FINITE_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC;

    REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `q:A#A->bool`] THEN
    REWRITE_TAC[PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `w = @w. q(x:A,w:A)` THEN
    SUBGOAL_THEN `(q:A#A->bool)(x:A,w:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
      CONV_TAC SELECT_CONV THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `w:A IN s` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
    ASM_CASES_TAC `w:A = z` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w:A = y` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `y:A = z` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;
```

### Informal statement
For any natural number $n$ and set $s$ of type $A$, if $s$ has size $n$, then the set of all permutations that derange $s$ (i.e., all permutations where no element maps to itself) has size equal to $\text{derangements}(n)$.

Formally, for all $n ∈ ℕ$ and sets $s$ of type $A$:
$$|s| = n \implies |\{p \mid p \text{ deranges } s\}| = \text{derangements}(n)$$

where $\text{derangements}(n)$ represents the number of derangements of a set with $n$ elements.

### Informal proof
The proof proceeds by induction on $n$ using the recursive definition of the function `derangements`:

* **Base Case 1** ($n = 0$): When $s$ is empty, there is exactly one permutation (the empty function), which is a derangement. This matches $\text{derangements}(0) = 1$.

* **Base Case 2** ($n = 1$): For a singleton set, no permutation can be a derangement (since the single element must map to itself), so there are 0 derangements. This matches $\text{derangements}(1) = 0$.

* **Inductive Step** ($n + 2$): For a set $t$ of size $n + 2$, we express it as $t = x \cup s$ where $|s| = n + 1$ and $x \notin s$. The proof partitions the derangements of $t$ into two disjoint classes:

  1. Derangements where $x$ and some element $y \in s$ map to each other (i.e., form a 2-cycle):
     * For each $y \in s$, we count derangements of $s \setminus \{y\}$
     * Each such derangement can be extended to a derangement of $t$ by adding the mappings $x \mapsto y$ and $y \mapsto x$
     * This gives $|s| \cdot \text{derangements}(n)$ such derangements
  
  2. Derangements where $x$ and some element $y \in s$ are in different cycles:
     * For each $y \in s$, we count derangements of $x \cup (s \setminus \{y\})$
     * Each such derangement contains some mapping $x \mapsto z$ for $z \in s$
     * We transform it to a derangement of $t$ by replacing the mappings $x \mapsto z$ and $y \mapsto$ (some $w$) with $x \mapsto y$ and $y \mapsto z$
     * This gives $|s| \cdot \text{derangements}(n+1)$ such derangements

The total number of derangements is therefore $|s| \cdot \text{derangements}(n) + |s| \cdot \text{derangements}(n+1) = (n+1) \cdot \text{derangements}(n) + (n+1) \cdot \text{derangements}(n+1)$. This equals $(n+2) \cdot \text{derangements}(n+1) - \text{derangements}(n+1) + (n+1) \cdot \text{derangements}(n) = (n+2) \cdot \text{derangements}(n+1) - \text{derangements}(n+1) + (n+1) \cdot \text{derangements}(n) = \text{derangements}(n+2)$, completing the proof.

### Mathematical insight
This theorem establishes the fact that the number of derangements of a set with $n$ elements is given by the function `derangements(n)`, which follows the recurrence relation:
- $\text{derangements}(0) = 1$
- $\text{derangements}(1) = 0$
- $\text{derangements}(n+2) = (n+2) \cdot \text{derangements}(n+1) - \text{derangements}(n+1) + (n+1) \cdot \text{derangements}(n)$ 

This can be simplified to:
- $\text{derangements}(n+2) = (n+1) \cdot (\text{derangements}(n+1) + \text{derangements}(n))$

Derangements are important in combinatorics, probability theory (particularly in the matching problem and the "hat check problem"), and group theory. The number of derangements of an $n$-element set is often denoted $!n$ and can also be expressed as $n! \sum_{i=0}^{n} \frac{(-1)^i}{i!}$, which approximates to $\frac{n!}{e}$ for large $n$.

### Dependencies
- `DERANGEMENT_INDUCT`: An induction principle for derangements
- `derangements`: The function computing the number of derangements of an $n$-element set
- `DERANGEMENT_EMPTY`: Theorem about derangements of the empty set
- `DERANGEMENT_SING`: Theorem about derangements of a singleton set
- `DERANGEMENT_ADD1`: Theorem about extending derangements when adding one element
- `DERANGEMENT_ADD2`: Theorem about extending derangements when adding two elements

### Porting notes
When porting this theorem, consider:
1. Ensuring your target system has a formal concept of derangements or defining it first
2. Implementing the recursive definition of `derangements(n)`
3. The proof relies heavily on set manipulation and counting techniques, which may need different approaches in systems with different set theories
4. The theorem mixes combinatorial and set-theoretic reasoning, which might require different proof strategies in systems with weaker automation for either domain

---

## SUM_1

### SUM_1
- `SUM_1`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_1 = prove
 (`sum(0..1) f = f 0 + f 1`,
  REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0]);;
```

### Informal statement
For any function $f$, the sum of $f$ over the range from $0$ to $1$ is equal to $f(0) + f(1)$.

In mathematical notation:
$$\sum_{i=0}^{1} f(i) = f(0) + f(1)$$

### Informal proof
The proof applies three tactics:
1. First, the number `1` is converted to its Peano representation using `num_CONV`.
2. Then, `SUM_CLAUSES_NUMSEG` is applied, which provides the recursive definition for sums over numeric ranges.
3. Finally, `LE_0` is used, which states that $0 \leq n$ for any natural number $n$.

The proof essentially unfolds the definition of summation over the range $[0,1]$ and simplifies it to the explicit sum $f(0) + f(1)$.

### Mathematical insight
This is a trivial result that explicitly computes the sum of a function over the smallest non-trivial range of natural numbers. While simple, this theorem is useful as a base case for inductive proofs involving summations, and can serve as a convenient rewrite rule in simplification tasks.

### Dependencies
- `num_CONV`: Converts a numeral to its Peano representation
- `SUM_CLAUSES_NUMSEG`: Provides recursive clauses for summing over numeric ranges
- `LE_0`: States that 0 is less than or equal to any natural number

---

## SUM_2

### Name of formal statement
SUM_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_2 = prove
 (`sum(0..2) f = f 0 + f 1 + f 2`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0;
           REAL_ADD_AC]);;
```

### Informal statement
The theorem states that for a function $f$, the sum of the values of $f$ over the range from $0$ to $2$ is equal to the sum of the individual values:
$$\sum_{i=0}^{2} f(i) = f(0) + f(1) + f(2)$$

### Informal proof
The proof uses simplification tactics with several supporting theorems:

1. First, numeric constants 1 and 2 are converted to their Peano representations using `num_CONV`
2. Then, the `SUM_CLAUSES_NUMSEG` theorem is applied, which provides the recursive expansion of finite sums
3. `LE_0` is used to confirm that $0 \leq 2$ for the range validity
4. Finally, `REAL_ADD_AC` is used to handle associativity and commutativity of real addition as needed

The simplification tactic (`SIMP_TAC`) automatically expands the sum using these theorems to show that the sum equals $f(0) + f(1) + f(2)$.

### Mathematical insight
This is a simple but fundamental instance of the explicit computation of a finite sum. While trivial mathematically, it's useful to have this specific case explicitly proven as a theorem in the formal system. It provides a concrete example of how the general summation operator behaves on a specific range and can be used directly in other proofs without having to expand the summation manually each time.

### Dependencies
- **Theorems**:
  - `num_CONV`: Converts numeric literals to their Peano representations
  - `SUM_CLAUSES_NUMSEG`: Provides recursive clauses for sum over numeric ranges
  - `LE_0`: Theorem stating that 0 is less than or equal to any natural number
  - `REAL_ADD_AC`: Handles associativity and commutativity of real addition

### Porting notes
When porting to another theorem prover:
1. Make sure the target system has a similar summation operator that can handle numeric ranges
2. Verify that the basic arithmetic properties (like associativity and commutativity) are available
3. In some systems, you may be able to use built-in simplification of concrete finite sums, making this theorem unnecessary or automatically provable by the simplifier

---

## DERANGEMENTS

### Name of formal statement
DERANGEMENTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENTS = prove
 (`!n. ~(n = 0)
       ==> &(derangements n) =
           &(FACT n) * sum(0..n) (\k. --(&1) pow k / &(FACT k))`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[derangements; SUM_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[derangements; ARITH; SUM_2; SUM_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; SUM_SING_NUMSEG] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_pow] THEN REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `n:num` FACT_LT) THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM LT_NZ; REAL_POW_NEG; GSYM REAL_OF_NUM_LT; REAL_POW_ONE] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For any positive natural number $n$ (where $n \neq 0$), the number of derangements of $n$ elements can be expressed as:

$$\text{derangements}(n) = n! \sum_{k=0}^{n} \frac{(-1)^k}{k!}$$

where $\text{derangements}(n)$ counts the number of permutations of $n$ elements with no fixed points.

### Informal proof
The proof proceeds by induction using the `DERANGEMENT_INDUCT` theorem:

- First, we handle the base cases and rewrite using the definition of `derangements`.
- For $n = 1$:
  * We compute $\text{derangements}(1) = 0$ directly
  * The right-hand side evaluates to $1! \cdot (1 - 1) = 0$
  
- For the inductive step, assuming the formula holds for $n$, we show it holds for $n+1$:
  * We use the recurrence relation for derangements: $\text{derangements}(n+1) = n \cdot (\text{derangements}(n) + \text{derangements}(n-1))$
  * We split the sum $\sum_{k=0}^{n+1}$ into $\sum_{k=0}^{n} + $ the last term for $k=n+1$
  * After algebraic manipulations and applying the induction hypothesis, we verify that:
    $$(n+1)! \sum_{k=0}^{n+1} \frac{(-1)^k}{k!} = (n+1) \cdot n! \sum_{k=0}^{n} \frac{(-1)^k}{k!} + (-1)^{n+1} \cdot (n+1)$$
  
- The proof is completed using algebraic simplifications and properties of factorials.

### Mathematical insight
This theorem provides an elegant closed-form expression for counting derangements (permutations with no fixed points) using the alternating series formula. This is a classic result in combinatorics.

The formula $n! \sum_{k=0}^{n} \frac{(-1)^k}{k!}$ can also be written as $n! \cdot \sum_{k=0}^{n} \frac{(-1)^k}{k!} = \lfloor \frac{n!}{e} + \frac{1}{2} \rfloor$ for large $n$, showing the close connection between derangements and the constant $e$.

This result is important because:
1. It provides a direct formula for counting derangements without using recursion
2. It demonstrates the relationship between derangements and factorials
3. It offers insight into the asymptotic behavior of derangements, approaching $\frac{n!}{e}$ as $n$ grows

### Dependencies
- `DERANGEMENT_INDUCT`: The induction principle for derangements
- `derangements`: The definition of the derangement counting function
- Various arithmetic and algebraic simplification theorems

### Porting notes
When porting this theorem:
1. Ensure the definition of `derangements` is properly established first
2. The proof relies heavily on algebraic manipulation and simplification tactics
3. The alternating series representation might be approached differently in other systems
4. The recurrence relation for derangements should be established before proving this theorem

---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in
           abs(&(derangements n) - &(FACT n) / e) < &1 / &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DERANGEMENTS; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN ASM_CASES_TAC `n < 5` THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
     (ARITH_RULE `n < 5 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4`)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC(map (num_CONV o mk_small_numeral) (1--5)) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `abs x < a <=> --a < x /\ x < a`] THEN
    REWRITE_TAC[real_sub] THEN CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`-- &1`; `n + 1`] MCLAURIN_EXP_LE) THEN
  SIMP_TAC[PSUM_SUM_NUMSEG; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `(0 + n + 1) - 1 = n`; GSYM real_div] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs(a * b - a * (b + c)) = abs(a * c)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SIMP_TAC[REAL_OF_NUM_LT; FACT_LT; REAL_FIELD
   `&0 < a ==> a * b / ((&n + &1) * a) = b / (&n + &1)`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    UNDISCH_TAC `abs(u) <= abs(-- &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3` THEN CONJ_TAC THENL
   [CONV_TAC REALCALC_REL_CONV; ALL_TAC] THEN
  UNDISCH_TAC `~(n < 5)` THEN REWRITE_TAC[NOT_LT; GSYM REAL_OF_NUM_LE] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $n > 0$, let $e = \exp(1)$. Then the following inequality holds:
$$\left|\text{derangements}(n) - \frac{n!}{e}\right| < \frac{1}{2}$$

This states that for any positive integer $n$, the number of derangements of $n$ elements (permutations with no fixed points) differs from $\frac{n!}{e}$ by less than $\frac{1}{2}$.

### Informal proof
The proof proceeds by cases:

1. First, we consider the base case where $1 \leq n < 5$:
   - We consider each case $n = 1, 2, 3, 4$ individually
   - For each value, we compute the exact value of derangements($n$) and $\frac{n!}{e}$
   - We verify that their difference has absolute value less than $\frac{1}{2}$
   - This verification uses numerical computation (`REALCALC_REL_CONV`)

2. For the case $n \geq 5$:
   - We use the MacLaurin expansion of $e^{-1}$ up to $n+1$ terms (`MCLAURIN_EXP_LE`)
   - This gives us: $e^{-1} = \sum_{m=0}^{n} \frac{(-1)^m}{m!} + \frac{e^u \cdot (-1)^{n+1}}{(n+1)!}$ for some $u$ with $|u| \leq 1$
   - From the definition of derangements, we know: $\text{derangements}(n) = n! \sum_{m=0}^{n} \frac{(-1)^m}{m!}$
   - This gives us: $|\text{derangements}(n) - \frac{n!}{e}| = |\frac{n! \cdot e^u}{(n+1)!}| = \frac{e^u}{n+1}$
   - Since $|u| \leq 1$, we have $e^u \leq e^1 = e < 3$
   - For $n \geq 5$, we have $\frac{e}{n+1} < \frac{3}{6} = \frac{1}{2}$
   - Therefore, $|\text{derangements}(n) - \frac{n!}{e}| < \frac{1}{2}$

### Mathematical insight
This theorem provides a simple asymptotic approximation for derangements. The formula $\frac{n!}{e}$ serves as a remarkably accurate estimate for the number of derangements of $n$ objects, with an error less than $\frac{1}{2}$.

This result is significant because:
1. It gives an elegant connection between derangements and the mathematical constant $e$
2. Since the error is less than $\frac{1}{2}$, rounding $\frac{n!}{e}$ to the nearest integer gives exactly the number of derangements for $n > 0$
3. As noted in the comment, the bound $\frac{1}{2}$ could be tightened further to approximately $0.3678794 + \epsilon$

The approximation follows naturally from the classic formula for derangements: $D_n = n! \sum_{i=0}^{n} \frac{(-1)^i}{i!}$, which can be seen as $n!$ multiplied by a sum that converges to $\frac{1}{e}$ as $n$ increases.

### Dependencies
- `MCLAURIN_EXP_LE`: Provides the MacLaurin expansion of the exponential function with a remainder term

### Porting notes
When porting this theorem:
1. Ensure you have a good definition of derangements that matches the HOL Light definition
2. The proof relies on numerical computation for the base cases ($n < 5$)
3. The general case requires a precise formulation of the MacLaurin series for $e^x$ with remainder term
4. Consider that some proof assistants might need more explicit steps for the algebraic manipulations involving the MacLaurin series

---

## round

### Name of formal statement
round

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let round = new_definition
 `round x = @n. integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2`;;
```

### Informal statement
For a real number $x$, $\text{round}(x)$ is defined as the unique integer $n$ such that $n - \frac{1}{2} \leq x < n + \frac{1}{2}$.

Formally:
$$\text{round}(x) = n \text{ where } \text{integer}(n) \land (n - \frac{1}{2} \leq x) \land (x < n + \frac{1}{2})$$

This definition uses the Hilbert epsilon operator (denoted by `@n` in HOL Light) to choose the unique integer satisfying these constraints.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The `round` function implements standard rounding to the nearest integer with ties rounded to the nearest integer with a higher absolute value (also known as "round half away from zero"). 

This definition captures the intuitive notion of rounding where:
- A number is rounded to the nearest integer
- Numbers exactly halfway between two integers (like 1.5) are rounded up (to 2 in this case)
- Negative numbers follow the same pattern (-1.5 would round to -1)

This definition is crucial for many numerical algorithms and for bridging continuous mathematics with discrete applications.

### Dependencies
No explicit dependencies are listed in the provided information.

### Porting notes
When porting this definition:
1. Systems without epsilon operators (like Hilbert's choice operator `@`) will need to define this function constructively, possibly using floor and ceiling functions.
2. Ensure that the handling of edge cases like half-integers matches this definition's behavior.
3. In some proof assistants, you might need to prove that there is exactly one integer satisfying the constraints to ensure the definition is well-formed.
4. In systems like Lean or Isabelle, you might define this using a case analysis on `x - floor(x)` to determine whether to round up or down.

---

## ROUND_WORKS

### ROUND_WORKS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ROUND_WORKS = prove
 (`!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2`,
  GEN_TAC THEN REWRITE_TAC[round] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `floor(x + &1 / &2)` THEN MP_TAC(SPEC `x + &1 / &2` FLOOR) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers $x$, the rounded value of $x$ satisfies three properties:
1. $\text{round}(x)$ is an integer.
2. $\text{round}(x) - \frac{1}{2} \leq x$.
3. $x < \text{round}(x) + \frac{1}{2}$.

This is the standard mathematical characterization of rounding to the nearest integer, with the convention that half-integers are rounded up.

### Informal proof
The proof establishes that rounding a real number $x$ produces the nearest integer to $x$, with ties (distances of exactly $\frac{1}{2}$) rounded up.

- First, we rewrite using the definition of `round`.
- By applying the SELECT_CONV conversion, we need to provide an explicit value that satisfies the properties of rounding.
- We propose $\lfloor x + \frac{1}{2} \rfloor$ (the floor of $x + \frac{1}{2}$) as our candidate.
- We apply the `FLOOR` theorem to $x + \frac{1}{2}$, which states that:
  - $\lfloor x + \frac{1}{2} \rfloor$ is an integer
  - $\lfloor x + \frac{1}{2} \rfloor \leq x + \frac{1}{2}$
  - $x + \frac{1}{2} < \lfloor x + \frac{1}{2} \rfloor + 1$
- We then simplify using the `INTEGER_CLOSED` theorem to verify that our candidate maintains integer properties.
- Finally, we use real arithmetic to confirm that our candidate satisfies the required bounds:
  - $\lfloor x + \frac{1}{2} \rfloor - \frac{1}{2} \leq x$
  - $x < \lfloor x + \frac{1}{2} \rfloor + \frac{1}{2}$

### Mathematical insight
This theorem establishes the fundamental properties of the rounding function: it returns an integer, and this integer is the closest to the input value. The bounds indicate that $x$ is within $\frac{1}{2}$ of $\text{round}(x)$.

The definition of rounding implemented here uses the "round half up" convention, where numbers exactly halfway between two integers (like 2.5) are rounded to the next integer up (to 3). This is one of several common rounding conventions.

In numerical computation, understanding the exact behavior of rounding is crucial for analyzing error bounds and ensuring numerical stability.

### Dependencies
- Theorems:
  - `FLOOR`: Provides the core properties of the floor function, stating that $\lfloor x \rfloor$ is an integer, $\lfloor x \rfloor \leq x$, and $x < \lfloor x \rfloor + 1$.
  - `INTEGER_CLOSED`: Establishes that integers are closed under various operations.

### Porting notes
When porting this theorem:
- Ensure your target system has a compatible definition of the `round` function.
- The handling of half-integers should match HOL Light's convention of rounding up.
- Some proof assistants may have built-in rounding functions with different conventions (such as "round to even"), so verify the exact behavior.

---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in &(derangements n) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN LET_TAC THEN
  MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  REWRITE_TAC[INTEGER_CLOSED; ROUND_WORKS] THEN
  MP_TAC(SPEC `&(FACT n) / e` ROUND_WORKS) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DERANGEMENTS_EXP) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all $n \neq 0$, if $e = \exp(1)$ (the base of natural logarithm), then $\text{derangements}(n) = \text{round}(n! / e)$, where $\text{derangements}(n)$ denotes the number of derangements of $n$ elements.

### Informal proof
To prove that the number of derangements of $n$ elements equals the nearest integer to $n!/e$, we proceed as follows:

- Let $e = \exp(1)$. We need to show that $\text{derangements}(n) = \text{round}(n!/e)$.
- Apply `REAL_EQ_INTEGERS_IMP`, which states that if $x$ and $y$ are integers and $|x-y| < 1$, then $x = y$.
- We know that $\text{derangements}(n)$ is an integer, so we need to show:
  1. $\text{round}(n!/e)$ is an integer (which follows from the definition of the round function)
  2. $|\text{derangements}(n) - \text{round}(n!/e)| < 1$
- From `ROUND_WORKS`, we know that $|\text{round}(x) - x| \leq 1/2$ for any real number $x$.
- From `DERANGEMENTS_EXP`, we have that $\text{derangements}(n)$ is very close to $n!/e$.
- Combining these facts and using real arithmetic, we conclude that $\text{derangements}(n) = \text{round}(n!/e)$.

### Mathematical insight
This theorem provides a remarkable closed-form approximation for the number of derangements. A derangement of $n$ elements is a permutation where no element appears in its original position. 

The formula connects this combinatorial quantity to $n!/e$, which is the limit of the sequence $D_n = n! \cdot \sum_{k=0}^{n} \frac{(-1)^k}{k!}$ as $n$ approaches infinity. The theorem states that $D_n$ is actually the nearest integer to $n!/e$, which is a striking result showing how closely the number of derangements approximates this continuous function.

This result is particularly elegant as it connects a discrete counting problem (derangements) to a transcendental number ($e$). It's also computationally useful, as it provides a simple way to calculate the number of derangements for large values of $n$.

### Dependencies
- Theorems:
  - `INTEGER_CLOSED`: Collection of closure properties for integers under various operations.
  - `REAL_EQ_INTEGERS_IMP`: If $x$ and $y$ are integers and $|x-y| < 1$, then $x = y$.
  - `ROUND_WORKS`: The rounding function produces the nearest integer to its input.
  - `DERANGEMENTS_EXP`: A previous result about the relationship between derangements and $n!/e$.

### Porting notes
When porting this theorem:
1. Ensure the destination system has a proper definition of derangements.
2. The rounding function needs to be defined as returning the nearest integer to its input.
3. The proof relies on properties of the exponential function and factorial, which should be available in most proof assistants.
4. The theorem `DERANGEMENTS_EXP` appears to be a preliminary result that establishes the approximation; ensure this is ported first.

---

## THE_DERANGEMENTS_FORMULA

### THE_DERANGEMENTS_FORMULA
- THE_DERANGEMENTS_FORMULA

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let THE_DERANGEMENTS_FORMULA = prove
 (`!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS) THEN
  ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]);;
```

### Informal statement
For any finite set $s$ with cardinality $n > 0$, the set of derangements of $s$ is finite, and the number of derangements of $s$ is equal to the rounded value of $n! / e$, where $e$ is Euler's number.

Formally:
$$\forall n, s. \, |s| = n \land n \neq 0 \Rightarrow \text{FINITE}(\{p \mid p \text{ deranges } s\}) \land |\{p \mid p \text{ deranges } s\}| = \text{round}(n! / e)$$

### Informal proof
The proof follows from applying two key results:

1. First, we apply `NUMBER_OF_DERANGEMENTS`, which gives a formula for the number of derangements in terms of the factorial and a sum.

2. Then, we use `DERANGEMENTS_EXP` which relates the sum in the derangement formula to the value of $e$ (Euler's number).

Specifically, we:
- Start with the assumption that $s$ has size $n$ and $n \neq 0$.
- Apply `NUMBER_OF_DERANGEMENTS` to get the standard alternating sum formula for derangements.
- Use `DERANGEMENTS_EXP` to simplify this formula to $n!/e$ rounded to the nearest integer.
- The simplification is done using `ASM_SIMP_TAC` with the `HAS_SIZE` property.

### Mathematical insight
This theorem provides the well-known formula for counting derangements - permutations where no element remains in its original position. The formula $n!/e$ rounded to the nearest integer is a remarkably simple approximation that becomes exact when rounding is applied.

This result is significant because:
1. It demonstrates how the number of derangements approaches $n!/e$ as $n$ increases.
2. It connects combinatorial counting with the mathematical constant $e$.
3. It provides a computationally efficient way to calculate the number of derangements without using the alternating sum formula.

The formula can also be seen as stating that the probability that a random permutation is a derangement approaches $1/e$ as $n$ increases.

### Dependencies
#### Theorems
- `NUMBER_OF_DERANGEMENTS`: Provides the standard formula for the number of derangements.
- `DERANGEMENTS_EXP`: Relates the sum in the derangement formula to $e$.
- `HAS_SIZE`: Used to work with finite sets of a specific cardinality.

### Porting notes
When implementing this theorem in other systems:
1. Ensure that the system has a good representation of the mathematical constant $e$.
2. The rounding function should be properly defined to round to the nearest integer.
3. The definition of "derangement" should match HOL Light's definition - a permutation with no fixed points.
4. The proof relies on the specific formula for derangements, which may need to be proven separately in the target system.

---

