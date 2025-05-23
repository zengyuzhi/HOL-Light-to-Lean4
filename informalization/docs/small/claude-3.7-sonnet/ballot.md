# ballot.ml

## Overview

Number of statements: 23

This file formalizes the ballot problem, a classic combinatorial problem in probability theory. It builds on the binomial coefficients from the binomial library to prove that when two candidates receive a and b votes respectively (with a > b), the probability that the first candidate maintains the lead throughout the counting process is (a-b)/(a+b). The file contains definitions of ballot sequences and provides a rigorous formalization of the ballot theorem along with its proof.

## vote_INDUCT,vote_RECURSION

### Name of formal statement
vote_INDUCT, vote_RECURSION

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let vote_INDUCT,vote_RECURSION = define_type
 "vote = A | B";;
```

### Informal statement
The definition creates a new type `vote` with exactly two constructors: `A` and `B`. This represents a binary choice vote between two candidates or options.

### Informal proof
This is a type definition rather than a theorem, so there's no explicit proof. The definition uses HOL Light's `define_type` mechanism to create a new inductive type with two constructors.

The system automatically generates two theorems:
- `vote_INDUCT`: An induction principle for the type
- `vote_RECURSION`: A recursion principle for defining functions on this type

These principles allow for case analysis and function definition on values of type `vote`.

### Mathematical insight
This is a simple enumerated type representing two options, which serves as the foundation for the ballot problem being modeled. The ballot problem typically deals with counting votes between two candidates, often denoted as A and B.

The type is used in the broader context of a formal development related to counting and analyzing voting outcomes. Having a dedicated type for votes allows for type-safe reasoning about vote counting and manipulation.

The simplicity of having just two options (A and B) is canonical in many voting theory problems, as it represents the simplest case of binary choice that still exhibits interesting mathematical properties.

### Dependencies
None explicitly shown in this definition. The type is defined from first principles.

### Porting notes
This is a very simple type definition that should be straightforward to port to any proof assistant that supports algebraic data types or enumeration types:

- In Lean, this would be: `inductive vote | A | B`
- In Coq, this would be: `Inductive vote := A | B.`
- In Isabelle/HOL, this would be: `datatype vote = A | B`

The definition should not present any porting challenges as it's a fundamental construction in most type systems.

---

## all_countings

### Name of formal statement
all_countings

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let all_countings = new_definition
 `all_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b}`;;
```

### Informal statement
The function `all_countings a b` represents the number of ways to arrange `a` elements of type `A` and `b` elements of type `B` in a sequence of length `n = a + b`.

Formally, it is defined as the cardinality of the set of all functions `f` such that:
1. `f` maps from the set `{1, 2, ..., n}` to the set `{A, B}`
2. The number of indices `i ∈ {1, 2, ..., n}` such that `f(i) = A` is exactly `a`
3. The number of indices `i ∈ {1, 2, ..., n}` such that `f(i) = B` is exactly `b`

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
This definition counts the number of ways to arrange two types of objects in a sequence, where the order matters. It is equivalent to the number of ways to choose positions for `a` elements of type `A` (or equivalently, for `b` elements of type `B`) from a sequence of length `n = a + b`, which is the binomial coefficient $\binom{n}{a} = \binom{n}{b} = \frac{n!}{a! \cdot b!}$.

This definition is useful in combinatorial problems, particularly when counting arrangements or permutations where elements can be divided into distinct types. It has applications in probability theory (e.g., in the binomial distribution) and in computational tasks like counting bit strings with a specific number of 1's and 0's.

### Dependencies
No explicit dependencies are used in the definition.

### Porting notes
When porting this definition:
1. Ensure that the target system supports function spaces, set cardinality, and set comprehensions
2. Note that HOL Light's `-->` represents the type of total functions from one set to another
3. The definition uses `A` and `B` as literal elements of a set, not as type parameters or variables
4. In some systems, you may need to define `A` and `B` as distinct constants of an enumerated type

---

## valid_countings

### Name of formal statement
valid_countings

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let valid_countings = new_definition
 `valid_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b /\
                  !m. 1 <= m /\ m <= n
                      ==> CARD { i | i IN 1..m /\ f(i) = A} >
                          CARD { i | i IN 1..m /\ f(i) = B}}`;;
```

### Informal statement
The definition `valid_countings a b` counts the number of functions $f : \{1, 2, \ldots, n\} \rightarrow \{A, B\}$ such that:
1. $n = a + b$
2. $|\{i \in \{1, 2, \ldots, n\} : f(i) = A\}| = a$
3. $|\{i \in \{1, 2, \ldots, n\} : f(i) = B\}| = b$
4. For all $m$ such that $1 \leq m \leq n$, we have:
   $|\{i \in \{1, 2, \ldots, m\} : f(i) = A\}| > |\{i \in \{1, 2, \ldots, m\} : f(i) = B\}|$

In other words, it counts functions from $\{1,2,\ldots,n\}$ to $\{A,B\}$ that have exactly $a$ values equal to $A$ and $b$ values equal to $B$, with the additional constraint that at every prefix of the sequence, the number of $A$s strictly exceeds the number of $B$s.

### Informal proof
No proof is given as this is a definition.

### Mathematical insight
This definition captures the notion of "valid ballot sequences" or "valid counting sequences" in combinatorics. It represents paths in a grid starting at the origin that:
1. Use only steps to the right (representing $A$) and steps upward (representing $B$)
2. End at the point $(a,b)$
3. Always stay strictly above the diagonal line $y = x$

This concept is central to the Ballot theorem and has applications in various counting problems, including the Catalan numbers when $a = b + 1$. The valid counting sequences represent ways to count votes in an election where one candidate (represented by $A$) always maintains a strict lead over the other candidate (represented by $B$).

The definition effectively encodes the cardinality of this set of valid sequences, which is known to be equal to $\frac{a-b}{a+b}\binom{a+b}{a}$ when $a > b$.

### Dependencies
None explicitly listed in the provided dependency information.

### Porting notes
When porting this definition:
- Ensure the target system has a suitable way to represent finite sets and their cardinalities
- Be careful with the function space notation `(1..n --> {A,B})`, which represents all functions from the set $\{1,2,\ldots,n\}$ to the set $\{A,B\}$
- The definition uses counting constraints rather than existential constructions, so systems with good support for cardinality reasoning will handle this more naturally

---

## vote_CASES

### Name of formal statement
vote_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let vote_CASES = cases "vote"
and vote_DISTINCT = distinctness "vote";;
```

### Informal statement
The theorem `vote_CASES` is a case analysis theorem for the `vote` type. It states that for any element `v` of type `vote`, either `v = aei` or `v = bat`.

### Informal proof
This is not a theorem that requires a proof in the traditional sense. Rather, it's automatically generated from the declaration of the `vote` type using the `cases` function. The `cases` function creates a theorem asserting that any value of the specified type must be one of the constructors of that type.

### Mathematical insight
The `vote_CASES` theorem provides a fundamental property of the `vote` type: it establishes that the type has exactly two possible values (`aei` and `bat`). This is essential for reasoning about values of this type, as it allows for exhaustive case analysis. 

In the context of formal verification, particularly when modeling voting systems or protocols, such a type might represent the possible voting options or candidates. The case analysis theorem ensures that reasoning about all possible voting outcomes can be done by considering just these two cases.

### Dependencies
The theorem is automatically generated based on the definition of the `vote` type. The companion theorem `vote_DISTINCT` (also mentioned in the script but not the main focus here) establishes that the constructors of the `vote` type are distinct, i.e., `aei ≠ bat`.

### Porting notes
When porting to another proof assistant:
- Ensure the `vote` type is defined as an enumerated type with exactly two constructors: `aei` and `bat`
- Most proof assistants automatically generate case analysis theorems for inductive types, but the naming conventions may differ
- In Lean, for example, similar functionality would be available through the `cases` tactic
- In Coq, this might correspond to an automatically generated induction principle or a custom match expression
- In Isabelle/HOL, case analysis theorems are also automatically generated for datatypes

---

## FINITE_COUNTINGS

### Name of formal statement
FINITE_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_COUNTINGS = prove
 (`FINITE {f | f IN (1..n --> {A,B}) /\ P f}`,
  MATCH_MP_TAC FINITE_RESTRICT THEN
  MATCH_MP_TAC FINITE_FUNSPACE THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_INSERT; FINITE_RULES]);;
```

### Informal statement
The set $\{f \mid f \in (1..n \rightarrow \{A,B\}) \land P(f)\}$ is finite.

This represents a subset of functions from the interval $[1,n]$ to the two-element set $\{A,B\}$, where each function $f$ satisfies the predicate $P$.

### Informal proof
The proof proceeds in the following steps:

1. Apply `FINITE_RESTRICT` to reduce the problem to showing that the full function space $(1..n \rightarrow \{A,B\})$ is finite.
   
2. Apply `FINITE_FUNSPACE` to show that the function space $(1..n \rightarrow \{A,B\})$ is finite, provided that:
   - The domain $(1..n)$ is finite
   - The codomain $\{A,B\}$ is finite

3. Use `REWRITE_TAC` with:
   - `FINITE_NUMSEG` to establish that the interval $1..n$ is finite
   - `FINITE_INSERT` to help establish that $\{A,B\}$ is finite
   - `FINITE_RULES` to handle basic finite set operations

Combined, these steps prove that the original set of functions satisfying predicate $P$ is finite.

### Mathematical insight
This theorem establishes that any subset of functions from a finite interval to a two-element set is finite, provided the subset is defined by a predicate $P$. 

This result is a special case of a more general principle: the set of functions from a finite domain to a finite codomain is itself finite, and any subset of a finite set is finite. The cardinality of the full function space would be $2^n$, representing all possible binary sequences of length $n$.

Such finite function spaces are important in combinatorial counting problems, boolean functions, and when representing finite sequences over binary alphabets.

### Dependencies
- Theorems:
  - `FINITE_RESTRICT`: Shows that a subset of a finite set defined by a predicate is finite
  - `FINITE_FUNSPACE`: Shows that the set of all functions from a finite set to a finite set is finite
  - `FINITE_NUMSEG`: Shows that numeric intervals like $1..n$ are finite
  - `FINITE_INSERT`: Shows that adding an element to a finite set preserves finiteness
  - `FINITE_RULES`: Collection of basic results about finite sets

### Porting notes
When porting this theorem:
- Ensure your system has the necessary library support for finite sets and function spaces
- The approach should transfer directly to most proof assistants, as it relies on general set-theoretic principles about finiteness
- The notation for function spaces and set comprehensions may need adaptation depending on the target system

---

## UNIV_VOTE

### Name of formal statement
UNIV_VOTE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNIV_VOTE = prove
 (`(:vote) = {A,B}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY; vote_CASES]);;
```

### Informal statement
The universal set of all votes is equal to the set $\{A, B\}$. In other words, the set of all possible votes is exactly $\{A, B\}$.

### Informal proof
The proof establishes that the universal set of votes `(:vote)` is equal to the set $\{A, B\}$ by:

- Using the extensionality principle (`EXTENSION`) which states that two sets are equal if and only if they contain exactly the same elements
- Applying the property that any element belongs to the universal set (`IN_UNIV`)
- Using set theory properties about membership in insertion sets and empty sets (`IN_INSERT`, `NOT_IN_EMPTY`)
- Applying the fundamental property `vote_CASES` which states that any vote must be either $A$ or $B$

The combination of these principles establishes that the universal set of votes contains exactly the elements $A$ and $B$.

### Mathematical insight
This theorem formally characterizes the vote type as having exactly two possible values: $A$ and $B$. This establishes the binary nature of votes in this formal system, which is essential for modeling binary voting scenarios or systems where choices are limited to two options.

The theorem provides a complete specification of the possible values of the vote type, which is fundamental for any formal reasoning about voting systems built upon this type.

### Dependencies
- `EXTENSION` - The set extensionality principle
- `IN_UNIV` - The property that every element belongs to the universal set
- `IN_INSERT` - The property defining membership in an insertion set
- `NOT_IN_EMPTY` - The property that no element belongs to the empty set
- `vote_CASES` - The fundamental property stating that any vote must be either $A$ or $B$

### Porting notes
When porting this theorem to another system, ensure that:
- The vote type is properly defined as a binary type
- The system has appropriate set theory mechanisms to express universal sets and equality between sets
- The axiomatization or definition of votes in the target system maintains that votes can only be $A$ or $B$

---

## ADD1_NOT_IN_NUMSEG

### Name of formal statement
ADD1_NOT_IN_NUMSEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ADD1_NOT_IN_NUMSEG = prove
 (`!m n. ~((n + 1) IN m..n)`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $m$ and $n$, the value $n + 1$ is not an element of the set $\{m, m+1, \ldots, n\}$ (the integer range from $m$ to $n$).

Formally: $\forall m, n \in \mathbb{N}. (n + 1) \notin \{m, m+1, \ldots, n\}$

### Informal proof
The proof proceeds in two steps:

1. First, the theorem uses `REWRITE_TAC[IN_NUMSEG]` to expand the definition of membership in the range $m..n$. This rewrites the goal to show that $\lnot(m \leq n+1 \land n+1 \leq n)$, which is the negation of the condition for an element to be in the segment.

2. Then `ARITH_TAC` solves the goal by automatically handling the arithmetic reasoning. Since $n+1 > n$ for any natural number, the condition $n+1 \leq n$ is always false, making the conjunction $m \leq n+1 \land n+1 \leq n$ false regardless of the value of $m$.

### Mathematical insight
This theorem establishes a basic property of integer ranges: the successor of the upper bound always falls outside the range. This is straightforward but important for formal reasoning about ranges and segments.

The theorem is particularly useful when working with algorithms or proofs involving integer ranges, where understanding the boundaries of these ranges is crucial. It's a simple example of how arithmetic properties translate to set-theoretic properties in formalized mathematics.

### Dependencies
- `IN_NUMSEG`: Definition of membership in an integer range
- `ARITH_TAC`: Automatic tactic for solving arithmetic goals

### Porting notes
This theorem should be straightforward to port to other systems, as it relies only on basic integer arithmetic and the definition of integer ranges. When porting:

1. Ensure that the target system has an equivalent definition of integer ranges
2. The automation level may differ - in systems with weaker arithmetic automation, you might need to be more explicit about why $n+1 \leq n$ is false

---

## NUMSEG_1_CLAUSES

### Name of formal statement
NUMSEG_1_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMSEG_1_CLAUSES = prove
 (`!n. 1..(n+1) = (n + 1) INSERT (1..n)`,
  REWRITE_TAC[GSYM ADD1; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`]);;
```

### Informal statement
For all natural numbers $n$, the set $\{1, 2, \ldots, n+1\}$ is equal to $\{n+1\} \cup \{1, 2, \ldots, n\}$.

In mathematical notation:
$$\forall n.\ \{1, \ldots, n+1\} = \{n+1\} \cup \{1, \ldots, n\}$$

### Informal proof
The proof is straightforward:
- First, we rewrite `n+1` as `SUC n` using `GSYM ADD1`.
- Then we apply `NUMSEG_CLAUSES`, which contains the general rule for how to express a segment of numbers using set operations.
- Finally, we use `ARITH_RULE` to verify that `1 <= SUC n`, which is a necessary condition in the application of `NUMSEG_CLAUSES`.

### Mathematical insight
This theorem provides a basic recursive decomposition of a numeric segment, showing how to build $\{1, \ldots, n+1\}$ from $\{1, \ldots, n\}$ by adding the element $n+1$. This relationship is foundational for inductive proofs over finite sets of consecutive integers, and provides a simple way to reason about such sets by induction on the upper bound.

### Dependencies
- Theorems:
  - `NUMSEG_CLAUSES`: Provide properties of numeric segments
  - `ADD1`: Relates addition by 1 to the successor function
  - `ARITH_RULE`: Used for basic arithmetic reasoning

### Porting notes
This theorem should be straightforward to port to other systems. The main consideration is how the target system represents:
1. Numeric segments or ranges
2. Set insertion operations
3. Basic arithmetic facts

In most theorem provers, this result would be part of the basic library for working with finite sets of integers.

---

## NUMSEG_RESTRICT_SUC

### Name of formal statement
NUMSEG_RESTRICT_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMSEG_RESTRICT_SUC = prove
 (`{i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i}
        else {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NUMSEG_1_CLAUSES; IN_INSERT] THEN
  ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;
```

### Informal statement
The theorem states that for any natural number $n$ and predicate $P$, the set 
$$\{i \mid i \in \{1, 2, \ldots, n+1\} \land P(i)\}$$
can be expressed as:
$$\begin{cases}
\{n+1\} \cup \{i \mid i \in \{1, 2, \ldots, n\} \land P(i)\} & \text{if } P(n+1) \text{ holds} \\
\{i \mid i \in \{1, 2, \ldots, n\} \land P(i)\} & \text{if } P(n+1) \text{ does not hold}
\end{cases}$$

In HOL Light notation, `1..(n+1)` represents the segment of natural numbers from 1 to $n+1$ inclusive.

### Informal proof
The proof proceeds by splitting into cases based on whether $P(n+1)$ holds:

* First, we apply generalization tactics to introduce the variables.
* Then, we use the conditional cases tactic to split into two cases: when $P(n+1)$ holds and when it doesn't.
* For each case, we prove set equality by showing that the elements of both sets are the same:
  * We rewrite the goal using the following theorems:
    * `EXTENSION`: two sets are equal if they have the same elements
    * `IN_ELIM_THM`: expands set comprehension membership
    * `NUMSEG_1_CLAUSES`: properties of number segments starting from 1
    * `IN_INSERT`: membership in a set with a new element inserted
  * Finally, we use `ASM_MESON_TAC` with `ADD1_NOT_IN_NUMSEG` to handle the remaining cases. This uses the fact that $n+1$ is not in the set $\{1,2,\ldots,n\}$.

### Mathematical insight
This theorem gives a recursive characterization of a filtered number segment, showing how to break down a filtered segment from 1 to n+1 in terms of a filtered segment from 1 to n. It establishes a useful property when working with finite segments of natural numbers under a predicate filter.

The key insight is that when considering a restricted segment with a predicate, we can decompose it by separately handling the last element based on whether it satisfies the predicate. This is particularly useful for inductive proofs about filtered segments, as it provides a step case.

### Dependencies
- `EXTENSION`: Theorem asserting that two sets are equal if and only if they have the same elements
- `IN_ELIM_THM`: Theorem about membership in set comprehensions
- `NUMSEG_1_CLAUSES`: Properties of number segments starting from 1
- `IN_INSERT`: Theorems about membership in a set with an inserted element
- `ADD1_NOT_IN_NUMSEG`: Theorem stating that n+1 is not in the segment from 1 to n

### Porting notes
When porting this theorem:
- Ensure your target system has a representation of finite segments of natural numbers
- Verify that set comprehension syntax is properly translated
- The conditional expression (`if-then-else`) in the conclusion should be handled appropriately
- This theorem depends on basic set-theoretic operations and properties of natural numbers, which should be available in most proof assistants

---

## CARD_NUMSEG_RESTRICT_SUC

### CARD_NUMSEG_RESTRICT_SUC
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CARD_NUMSEG_RESTRICT_SUC = prove
 (`CARD {i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then CARD {i | i IN 1..n /\ P i} + 1
        else CARD {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_RESTRICT_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_THM; ADD1_NOT_IN_NUMSEG; ADD1]);;
```

### Informal statement
The theorem states that for any natural number $n$ and predicate $P$:

$$\text{CARD}(\{i \mid i \in \{1, \ldots, n+1\} \land P(i)\}) = 
\begin{cases}
\text{CARD}(\{i \mid i \in \{1, \ldots, n\} \land P(i)\}) + 1 & \text{if } P(n+1) \\
\text{CARD}(\{i \mid i \in \{1, \ldots, n\} \land P(i)\}) & \text{otherwise}
\end{cases}$$

where $\text{CARD}(S)$ denotes the cardinality of set $S$.

### Informal proof
The proof proceeds as follows:

1. Apply the theorem `NUMSEG_RESTRICT_SUC` which states that 
   $\{i \mid i \in \{1, \ldots, n+1\} \land P(i)\}$ can be rewritten as:
   * $\{i \mid i \in \{1, \ldots, n\} \land P(i)\} \cup \{n+1\}$ if $P(n+1)$ holds
   * $\{i \mid i \in \{1, \ldots, n\} \land P(i)\}$ if $P(n+1)$ does not hold

2. Consider the two cases separately:
   * When $P(n+1)$ holds, use `CARD_CLAUSES` to calculate the cardinality of the union
   * When $P(n+1)$ does not hold, the set remains unchanged from the $1..n$ case

3. Apply simplifications to prove that $n+1$ is not in the set $\{1,\ldots,n\}$ (using `ADD1_NOT_IN_NUMSEG`)

4. Complete the proof by showing the cardinality is incremented by 1 in the first case and unchanged in the second

### Mathematical insight
This theorem provides a recursive method for calculating the cardinality of a filtered sequence by considering elements one at a time. It's particularly useful for inductive proofs involving sets defined by predicates over integer ranges. The result is intuitive: when extending a filtered sequence by one element, the cardinality either increases by 1 (if the new element satisfies the predicate) or stays the same (if it doesn't).

This is a specialized counting result that helps decompose cardinality calculations on filtered numeric ranges, which appears frequently in combinatorial proofs.

### Dependencies
- **Theorems:**
  - `NUMSEG_RESTRICT_SUC` - Decomposition of a filtered range into cases based on the last element
  - `CARD_CLAUSES` - Basic cardinality rules for set operations
  - `FINITE_RESTRICT` - Finiteness of restricted sets
  - `FINITE_NUMSEG` - Finiteness of numeric ranges
  - `ADD1_NOT_IN_NUMSEG` - Property that n+1 is not in the range 1..n
  - `ADD1` - Definition of increment by 1

---

## FORALL_RANGE_SUC

### FORALL_RANGE_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FORALL_RANGE_SUC = prove
 (`(!i. 1 <= i /\ i <= n + 1 ==> P i) <=>
      P(n + 1) /\ (!i. 1 <= i /\ i <= n ==> P i)`,
  REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i <= n \/ i = n + 1`] THEN
  MESON_TAC[ARITH_RULE `1 <= n + 1`]);;
```

### Informal statement
For a predicate $P$ and a natural number $n$, the following are equivalent:
- $\forall i. (1 \leq i \land i \leq n + 1) \Rightarrow P(i)$
- $P(n + 1) \land (\forall i. (1 \leq i \land i \leq n) \Rightarrow P(i))$

This theorem states that a universal quantification over the range $[1, n+1]$ is equivalent to the conjunction of the statement for $n+1$ and the universal quantification over the range $[1, n]$.

### Informal proof
The proof proceeds as follows:

1. First, rewrite the condition $i \leq n + 1$ as $i \leq n \lor i = n + 1$ using the arithmetic rule
   $i \leq n + 1 \Leftrightarrow i \leq n \lor i = n + 1$

2. After this rewriting, the left-hand side becomes:
   $\forall i. (1 \leq i \land (i \leq n \lor i = n + 1)) \Rightarrow P(i)$

3. Use the MESON theorem prover with the arithmetic fact that $1 \leq n + 1$ to complete the proof.
   This step demonstrates that the rewritten formula is logically equivalent to 
   $P(n + 1) \land (\forall i. (1 \leq i \land i \leq n) \Rightarrow P(i))$

### Mathematical insight
This theorem provides a way to split a universal quantification over a range ending with $n+1$ into two parts: the statement for the endpoint $n+1$ and the statement for the rest of the range $[1,n]$. It's essentially proving the inductive step in a range-based universal quantification.

This decomposition is useful for proofs by induction and for simplifying statements that involve ranges. The theorem allows for a more modular approach to handling universally quantified statements over consecutive integer ranges.

### Dependencies
#### Tactics and Rules
- `REWRITE_TAC`
- `MESON_TAC`
- `ARITH_RULE`

### Porting notes
When porting to other systems:
- This is a relatively straightforward theorem about the properties of ranges of integers.
- The key arithmetic facts being used are simple properties of inequalities and can be found in most theorem proving libraries.
- The proof relies on the automated reasoners in HOL Light. In other systems, you may need to use different automation tactics or provide slightly more detailed proof steps.

---

## IN_NUMSEG_RESTRICT_FALSE

### Name of formal statement
IN_NUMSEG_RESTRICT_FALSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_NUMSEG_RESTRICT_FALSE = prove
 (`m <= n
   ==> (i IN 1..m /\ (if i = n + 1 then p i else q i) <=> i IN 1..m /\ q i)`,
  REWRITE_TAC[IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `i <= m /\ m <= n ==> ~(i = n + 1)`]);;
```

### Informal statement
If $m \leq n$, then for any $i$, the statement $i \in \{1, \ldots, m\} \land (\text{if } i = n+1 \text{ then } p(i) \text{ else } q(i))$ is equivalent to $i \in \{1, \ldots, m\} \land q(i)$.

### Informal proof
The proof proceeds in two main steps:

- First, we rewrite the numeric range expression `IN_NUMSEG` to expand $i \in \{1, \ldots, m\}$ to its defining condition $1 \leq i \land i \leq m$.

- Then, we use automated reasoning (via `MESON_TAC`) with the arithmetic fact that if $i \leq m$ and $m \leq n$, then $i \neq n+1$.

This arithmetic fact ensures that the condition $i = n+1$ in the conditional expression is always false when $i \in \{1, \ldots, m\}$ and $m \leq n$. Therefore, the conditional expression $(\text{if } i = n+1 \text{ then } p(i) \text{ else } q(i))$ always evaluates to $q(i)$.

### Mathematical insight
This theorem handles a common logical simplification pattern when working with numeric ranges and conditional expressions. It shows that when the condition $i = n+1$ cannot possibly be satisfied (because $i$ is bounded by $m$ which is at most $n$), the conditional expression can be simplified to just its "else" branch.

This type of simplification is useful in formalizations where case distinctions are made based on index values, particularly when manipulating finite sequences, arrays, or indexed families of objects.

### Dependencies
- Definitions:
  - `IN_NUMSEG` - Set membership in a numeric range from $i$ to $j$

### Porting notes
When porting this theorem, ensure that:
1. The numeric range notation is properly translated to the target system
2. The conditional expression (if-then-else construct) is handled correctly
3. The arithmetic reasoning capability is available to establish that $i \leq m \land m \leq n \implies i \neq n+1$

---

## CARD_NUMSEG_RESTRICT_EXTREMA

### Name of formal statement
CARD_NUMSEG_RESTRICT_EXTREMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_NUMSEG_RESTRICT_EXTREMA = prove
 (`(CARD {i | i IN 1..n /\ P i} = n <=> !i. 1 <= i /\ i <= n ==> P i) /\
   (CARD {i | i IN 1..n /\ P i} = 0 <=> !i. 1 <= i /\ i <= n ==> ~(P i))`,
  SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`{i | i IN 1..n /\ P i}`; `1..n`] SUBSET_CARD_EQ) THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; CARD_NUMSEG_1] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_NUMSEG; IN_ELIM_THM] THEN
  MESON_TAC[]);;
```

### Informal statement
This theorem characterizes the extreme cases of the cardinality of a restricted set in a numerical segment:

1. $\text{CARD} \{i \mid i \in 1..n \wedge P(i)\} = n \iff \forall i. (1 \leq i \wedge i \leq n \implies P(i))$
2. $\text{CARD} \{i \mid i \in 1..n \wedge P(i)\} = 0 \iff \forall i. (1 \leq i \wedge i \leq n \implies \neg P(i))$

In other words, the cardinality of the set of integers from 1 to n that satisfy predicate P:
- equals n if and only if all integers from 1 to n satisfy P
- equals 0 if and only if no integer from 1 to n satisfies P

### Informal proof
The proof proceeds as follows:

* First, we simplify the condition for when a set has cardinality 0 using `CARD_EQ_0` and establish that the restricted set is finite using `FINITE_RESTRICT` and `FINITE_NUMSEG`.

* For the first part (equality with n): 
  * We apply the theorem `SUBSET_CARD_EQ` which states that if A is a subset of B, then |A| = |B| if and only if A = B.
  * In this case, A = {i | i ∈ 1..n ∧ P(i)} and B = 1..n.
  * We know |B| = n by `CARD_NUMSEG_1`.
  * Therefore, |A| = n if and only if A = B, which means every element in 1..n satisfies P.

* For both parts:
  * We convert the problem to reasoning about set equality and emptiness.
  * Using the principle of extension (`EXTENSION`), the first part becomes: {i | i ∈ 1..n ∧ P(i)} = 1..n iff ∀i. (1 ≤ i ∧ i ≤ n ⟹ P(i))
  * The second part becomes: {i | i ∈ 1..n ∧ P(i)} = ∅ iff ∀i. (1 ≤ i ∧ i ≤ n ⟹ ¬P(i))

* The final proof step uses `MESON_TAC` to handle the remaining first-order logic reasoning.

### Mathematical insight
This theorem characterizes the extreme cases for the cardinality of a filtered subset of consecutive integers. It's a useful tool for reasoning about the relationship between predicates and the size of sets they define. The result is intuitive: if a predicate is true for all elements in a range, the filtered set will have the same size as the original range; if the predicate is false for all elements, the filtered set will be empty. These boundary conditions are often useful in formal proofs involving finite sets defined by predicates.

### Dependencies
- Theorems:
  - `CARD_EQ_0`: Characterizes when a set has cardinality 0
  - `FINITE_RESTRICT`: Establishes finiteness of a restricted set
  - `FINITE_NUMSEG`: Establishes finiteness of numerical segments
  - `SUBSET_CARD_EQ`: Relates subset relation and cardinality equality
  - `CARD_NUMSEG_1`: Gives the cardinality of a numerical segment
  - `EXTENSION`: Set extension principle
  - Other basic set-theoretic properties

### Porting notes
When porting this theorem:
- Ensure the target system has a good library for finite sets and cardinality
- The notation for set comprehension and numerical segments may differ across systems
- The `MESON_TAC` automation at the end might need to be replaced with appropriate automation in the target system
- Some systems might prefer to separate the two claims into distinct theorems rather than using a conjunction

---

## VOTE_NOT_EQ

### Name of formal statement
VOTE_NOT_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VOTE_NOT_EQ = prove
 (`(!x. ~(x = A) <=> x = B) /\
   (!x. ~(x = B) <=> x = A)`,
  MESON_TAC[vote_CASES; vote_DISTINCT]);;
```

### Informal statement
For all $x$ in the `vote` type:
- $x \neq A \iff x = B$
- $x \neq B \iff x = A$

### Informal proof
This theorem is proved using the `MESON_TAC` automated theorem prover with two key facts about the `vote` type:
1. `vote_CASES`: Every element of the `vote` type is either $A$ or $B$
2. `vote_DISTINCT`: $A \neq B$

The proof follows directly from these facts:
- Since there are only two distinct elements in the `vote` type ($A$ and $B$), if $x$ is not equal to one of them, it must be equal to the other.
- The first statement ($x \neq A \iff x = B$) holds because:
  - If $x \neq A$, then by `vote_CASES` it must be $B$
  - If $x = B$, then by `vote_DISTINCT` it cannot be $A$
- The second statement ($x \neq B \iff x = A$) follows by similar reasoning.

### Mathematical insight
This theorem establishes the basic logical relationship between the two elements of the `vote` type ($A$ and $B$). It formalizes the fact that in a two-element type, the negation of equality with one element is equivalent to equality with the other element.

The `vote` type appears to be a simple enumeration type with exactly two values, likely representing a binary choice (such as yes/no, true/false, or approve/reject). This theorem captures the fundamental property that in a binary choice system, not choosing one option necessarily means choosing the other.

### Dependencies
- `vote_CASES`: A theorem stating that every element of the `vote` type is either $A$ or $B$
- `vote_DISTINCT`: A theorem stating that $A \neq B$

### Porting notes
When porting this to other proof assistants:
- Most systems with enumeration types or inductive types with two constructors will have similar built-in properties
- In Lean, Coq, or Isabelle, this could be proved using case analysis and the fact that constructors are injective and distinct
- This theorem might be automatically available as a lemma in some systems for any two-element type

---

## FUNSPACE_FIXED

### Name of formal statement
FUNSPACE_FIXED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FUNSPACE_FIXED = prove
 (`{f | f IN (s --> t) /\ (!i. i IN s ==> f i = a)} =
   if s = {} \/ a IN t then {(\i. if i IN s then a else @x. T)} else {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; funspace; NOT_IN_EMPTY; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;
```

### Informal statement
This theorem characterizes the set $\{f \mid f \in (s \to t) \land (\forall i. i \in s \Rightarrow f(i) = a)\}$, which consists of all functions from $s$ to $t$ that map every element of $s$ to the constant value $a$. It states that this set is:

- If $s = \emptyset$ or $a \in t$, then $\{(\lambda i. \text{ if } i \in s \text{ then } a \text{ else } @x. T)\}$, where $@x. T$ represents an arbitrary choice (via the Hilbert choice operator)
- Otherwise (if $s \neq \emptyset$ and $a \notin t$), this set is empty

### Informal proof
The proof proceeds as follows:

- First, we use `EXTENSION` to prove set equality, meaning we need to show for any arbitrary element that it belongs to the left-hand side if and only if it belongs to the right-hand side.
- We apply case analysis on the condition $s = \emptyset \lor a \in t$:
  - In the case where $s = \emptyset$ or $a \in t$, we need to show that $\{f \mid f \in (s \to t) \land (\forall i. i \in s \Rightarrow f(i) = a)\} = \{(\lambda i. \text{ if } i \in s \text{ then } a \text{ else } @x. T)\}$
    - This is done by simplifying both sides using definitions of set membership, function space, and singleton sets
    - Using function extensionality (`FUN_EQ_THM`), we establish the equality
  - In the case where $s \neq \emptyset$ and $a \notin t$, we need to show that $\{f \mid f \in (s \to t) \land (\forall i. i \in s \Rightarrow f(i) = a)\} = \emptyset$
    - This follows from the definition of function space: if $a \notin t$, then no function mapping elements of $s$ to $a$ can be in the function space $s \to t$, as all outputs must be in the range type $t$

The proof is completed using MESON to handle the logical reasoning in the final step.

### Mathematical insight
This theorem provides a precise characterization of the set of constant functions with domain $s$, range type $t$, and fixed value $a$. The key insights are:

1. If $s$ is empty, then there's exactly one function meeting the criteria - the empty function
2. If $a$ is in $t$, then there's exactly one function mapping all elements of $s$ to $a$ (and handling other inputs arbitrarily)
3. If $s$ is non-empty and $a$ is not in $t$, then no such function can exist in the function space $s \to t$

This result is important for formalized mathematics because it precisely characterizes when constant functions exist in specific function spaces, which is a foundational concept for further development of function theory.

### Dependencies
- Set theory: `EXTENSION`, `NOT_IN_EMPTY`, `IN_ELIM_THM`, `IN_SING`  
- Function theory: `funspace`, `FUN_EQ_THM`
- Logic: `REWRITE_TAC`, `COND_CASES_TAC`, `ASM_REWRITE_TAC`, `ASM_MESON_TAC`

### Porting notes
When porting this theorem:
1. Ensure your function space notation `s --> t` has the same meaning as in HOL Light
2. Handle the Hilbert choice operator (`@x. T`) appropriately - in some systems, you might need to use a different approach for the "default" value outside the domain
3. Pay attention to the handling of the empty function case, which some systems treat differently

---

## COUNTING_LEMMA

### Name of formal statement
COUNTING_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COUNTING_LEMMA = prove
 (`CARD {f | f IN (1..(n+1) --> {A,B}) /\ P f} =
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then A else f i)} +
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then B else f i)}`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f} +
              CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = B /\ P f}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    REWRITE_TAC[FINITE_COUNTINGS; EXTENSION; IN_INTER; IN_UNION] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[vote_CASES; vote_DISTINCT];
    ALL_TAC] THEN
  BINOP_TAC THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\f i. if i = n + 1 then @x:vote. T else f i` THENL
   [EXISTS_TAC `\f i. if i = n + 1 then A else f i`;
    EXISTS_TAC `\f i. if i = n + 1 then B else f i`] THEN
  REWRITE_TAC[FINITE_COUNTINGS] THEN
  REWRITE_TAC[IN_ELIM_THM; funspace; GSYM UNIV_VOTE; IN_UNIV] THEN
  REWRITE_TAC[NUMSEG_1_CLAUSES; IN_INSERT] THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `P x ==> x = y ==> P y`))) THEN
  TRY(GEN_REWRITE_TAC I [FUN_EQ_THM]) THEN ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;
```

### Informal statement
For a property $P$ of functions from $\{1, 2, \ldots, n+1\}$ to $\{A, B\}$, the cardinality of the set of functions satisfying $P$ equals the sum of:
1. The cardinality of the set of functions $f: \{1, 2, \ldots, n\} \to \{A, B\}$ such that $P$ holds for the extension of $f$ that maps $n+1$ to $A$.
2. The cardinality of the set of functions $f: \{1, 2, \ldots, n\} \to \{A, B\}$ such that $P$ holds for the extension of $f$ that maps $n+1$ to $B$.

Formally:
$$\text{CARD}\{f \mid f \in (1..(n+1) \to \{A,B\}) \wedge P(f)\} = \\
\text{CARD}\{f \mid f \in (1..n \to \{A,B\}) \wedge P(\lambda i. \text{ if } i = n+1 \text{ then } A \text{ else } f(i))\} + \\
\text{CARD}\{f \mid f \in (1..n \to \{A,B\}) \wedge P(\lambda i. \text{ if } i = n+1 \text{ then } B \text{ else } f(i))\}$$

### Informal proof
The proof proceeds by establishing equality through bijections:

1. First, we express the original set as a disjoint union of functions where $f(n+1)=A$ and functions where $f(n+1)=B$:
   $$\text{CARD}\{f \mid f \in (1..(n+1) \to \{A,B\}) \wedge P(f)\} = \\
   \text{CARD}\{f \mid f \in (1..(n+1) \to \{A,B\}) \wedge f(n+1)=A \wedge P(f)\} + \\
   \text{CARD}\{f \mid f \in (1..(n+1) \to \{A,B\}) \wedge f(n+1)=B \wedge P(f)\}$$
   
   This uses `CARD_UNION_EQ` to split the set into disjoint parts, relying on the fact that $A \neq B$ and every function must map $n+1$ to either $A$ or $B$.

2. Next, we establish bijections between:
   - The set of functions $f: \{1,\ldots,n+1\} \to \{A,B\}$ with $f(n+1)=A$ and $P(f)$, and 
   - The set of functions $g: \{1,\ldots,n\} \to \{A,B\}$ where $P$ holds for the extension of $g$ that maps $n+1$ to $A$.
   
   Similarly for functions mapping $n+1$ to $B$.

3. These bijections are constructed by:
   - For each $f: \{1,\ldots,n+1\} \to \{A,B\}$ with $f(n+1)=A$, we associate the restriction of $f$ to $\{1,\ldots,n\}$.
   - Conversely, for each $g: \{1,\ldots,n\} \to \{A,B\}$, we associate the extension of $g$ that maps $n+1$ to $A$.

4. The bijections guarantee that corresponding sets have the same cardinality, establishing the desired equality.

### Mathematical insight
This counting lemma is a fundamental result about partitioning the set of functions based on their value at a specific point. It is particularly useful in combinatorial arguments where we need to count functions with certain properties. 

The lemma essentially provides a recursive way to count the number of functions satisfying a property by decomposing the problem into smaller, more manageable cases based on the final value. This technique is similar to the principle of inclusion-exclusion but applied to function spaces.

The result is particularly relevant in voting theory, game theory, or any setting where we're analyzing binary choices across multiple agents or dimensions.

### Dependencies
- `CARD_UNION_EQ`: Theorem stating that the cardinality of a union of disjoint finite sets equals the sum of their cardinalities
- `FINITE_COUNTINGS`: Theorem establishing that certain finite function spaces are finite
- `BIJECTIONS_CARD_EQ`: Theorem stating that sets connected by a bijection have the same cardinality
- `vote_CASES` and `vote_DISTINCT`: Theorems about the vote type (representing $\{A,B\}$), establishing that every vote is either $A$ or $B$ and that $A \neq B$

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate machinery for defining functions by cases.
2. Verify that your system's handling of function extension/restriction aligns with HOL Light's approach.
3. The proof relies on bijections and cardinality properties for finite sets, which most proof assistants support but may implement differently.
4. The theorem uses a voting type with two values (A and B) - you may need to adapt this to your system's representation of binary choices.

---

## ALL_COUNTINGS_0

### Name of formal statement
ALL_COUNTINGS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS_0 = prove
 (`!a. all_countings a 0 = 1 /\ all_countings 0 a = 1`,
  REWRITE_TAC[all_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH_SUC]);;
```

### Informal statement
For all natural numbers $a$, the following equations hold:
- $\text{all\_countings}(a, 0) = 1$
- $\text{all\_countings}(0, a) = 1$

### Informal proof
The proof proceeds by rewriting the definition of `all_countings` and simplifying:

- First, we apply the definition of `all_countings` and related theorems about cardinality of sets and numerical intervals.
- The expression is simplified using theorems about bounded intervals of numbers (`CARD_NUMSEG_RESTRICT_EXTREMA`).
- The `LET_DEF` and `LET_END_DEF` theorems help unfold the let-expressions in the definition.
- The result simplifies to counting functions in a function space with specific properties.
- When one of the parameters is 0, the cardinality of the set becomes 1 because there is only one possible counting function (the empty function).
- This is further simplified using `CARD_CLAUSES` and `FINITE_RULES` to arrive at the value 1.

### Mathematical insight
This theorem establishes the base cases for the `all_countings` function, which counts the number of ways to distribute votes under certain conditions. When either the number of voters or candidates is 0, there is exactly one way to distribute votes (trivially).

The `all_countings` function appears to be related to counting theory, particularly in the context of voting systems or combinatorial configurations. These base cases (when either parameter is 0) provide the foundation for recursive calculations of more complex counting scenarios.

### Dependencies
#### Theorems
- `CARD_NUMSEG_RESTRICT_EXTREMA` - Theorem about the cardinality of restricted numerical segments
- `GSYM IN_NUMSEG` - Symmetric version of membership in numerical segments
- `ADD_CLAUSES` - Properties of addition
- `VOTE_NOT_EQ` - Property related to voting functions
- `FUNSPACE_FIXED` - Properties of function spaces with fixed properties
- `CARD_CLAUSES` - Theorems about calculating cardinalities
- `FINITE_RULES` - Rules about finite sets
- `ARITH_SUC` - Arithmetic properties related to successor function

#### Definitions
- `all_countings` - Counts ways to distribute votes
- `LET_DEF`, `LET_END_DEF` - Definitions for let expressions

### Porting notes
When porting this theorem:
- Ensure the `all_countings` function is properly defined in the target system
- The proof relies heavily on HOL Light's simplification tactics, which may need different approaches in other systems
- Be aware of how the target system handles function spaces and cardinality of sets

---

## VALID_COUNTINGS_0

### Name of formal statement
VALID_COUNTINGS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS_0 = prove
 (`valid_countings 0 0 = 1 /\
   !a. valid_countings (SUC a) 0 = 1 /\ valid_countings 0 (SUC a) = 0`,
  let lemma = prove
   (`{x} INTER s = if x IN s then {x} else {}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  REWRITE_TAC[valid_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ;
              TAUT `a /\ a /\ b <=> a /\ b`] THEN
  REWRITE_TAC[CONJUNCT1 NUMSEG_CLAUSES; ARITH_EQ; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[funspace; IN_ELIM_THM; NOT_IN_EMPTY; GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ Q x /\ R x} =
                             {x | P x /\ Q x} INTER {x | R x}`] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT; lemma] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_TAC THEN CONJ_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> a > b`) THEN
    ASM_SIMP_TAC[CARD_NUMSEG_RESTRICT_EXTREMA] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 <= k /\ k <= a ==> 1 <= k /\ !i. i <= k ==> i <= a`)) THEN
    ASM_SIMP_TAC[IN_NUMSEG; vote_DISTINCT] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    EXISTS_TAC `1` THEN REWRITE_TAC[NUMSEG_SING; IN_SING] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> ~(b > a)`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}`] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    SIMP_TAC[vote_DISTINCT; SET_RULE `{x | F} = {} /\ {x | x = a} = {a}`;
             CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH]]);;
```

### Informal statement
This theorem establishes basic properties of the `valid_countings` function for edge cases:

1. `valid_countings 0 0 = 1`
2. For any natural number `a`:
   - `valid_countings (SUC a) 0 = 1` 
   - `valid_countings 0 (SUC a) = 0`

Where `valid_countings n m` counts the number of ways to assign votes such that there are exactly `n` votes for candidate 1 and `m` votes for candidate 2, with the constraint that candidate 1 is always ahead or tied with candidate 2 during the counting process.

### Informal proof
The proof establishes three base cases of the `valid_countings` function by working directly with its definition and set-theoretic properties.

First, a lemma is proven: For any set `s` and element `x`, `{x} ∩ s = {x}` if `x ∈ s`, and `{x} ∩ s = ∅` otherwise.

The main proof then proceeds by:
- Rewriting the definition of `valid_countings` and simplifying with various basic arithmetic and set-theoretic facts
- Handling each of the three cases separately:

1. For `valid_countings 0 0 = 1`:
   - This simplifies to counting functions from the empty set to `{vote_1, vote_2}`
   - There is exactly one such function (the empty function), so the result is 1

2. For `valid_countings (SUC a) 0 = 1`:
   - This counts functions that map all elements to `vote_1`
   - Since there's only one such function, the result is 1

3. For `valid_countings 0 (SUC a) = 0`:
   - This case is shown to be impossible by contradiction
   - If we had 0 votes for candidate 1 and (SUC a) votes for candidate 2, then candidate 2 would be ahead at some point
   - This contradicts the constraint that candidate 1 must always be ahead or tied
   - Therefore, there are 0 such valid vote arrangements

### Mathematical insight
This theorem establishes the base cases for the `valid_countings` function, which counts ballot sequences where candidate 1 is never behind. These base cases are:
- With no votes cast (0,0), there's exactly one valid arrangement (the empty arrangement)
- With votes only for candidate 1, there's exactly one valid arrangement (all votes to candidate 1)
- With no votes for candidate 1 but some votes for candidate 2, there are no valid arrangements

This result is related to the Catalan numbers and ballot counting problems in combinatorics. The constraint that one candidate is never behind the other is a classic constraint in ballot-counting problems, and understanding these edge cases is essential for recursive formulations or combinatorial arguments about such sequences.

### Dependencies
- `valid_countings`: Definition of the function counting valid vote arrangements
- `CARD_NUMSEG_RESTRICT_EXTREMA`: Theorem about cardinality of restricted number segments
- `vote_DISTINCT`: Theorem establishing that votes for different candidates are distinct
- Various set-theoretic and arithmetic operations from the HOL Light library

### Porting notes
When porting this theorem:
- Ensure the `valid_countings` function is correctly defined with its ballot-counting interpretation
- The proof relies heavily on set-theoretical reasoning, particularly about function spaces and cardinality
- Special attention should be paid to how function spaces are represented in the target system

---

## ALL_COUNTINGS_SUC

### Name of formal statement
ALL_COUNTINGS_SUC

### Type of formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS_SUC = prove
 (`!a b. all_countings (a + 1) (b + 1) =
                all_countings a (b + 1) + all_countings (a + 1) b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN
  REWRITE_TAC[] THEN BINOP_TAC THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL]);;
```

### Informal statement
For all natural numbers $a$ and $b$, the number of ways to count votes such that there are exactly $a + 1$ votes for the first candidate and $b + 1$ votes for the second candidate equals the sum of:
- the number of ways to count votes with exactly $a$ votes for the first candidate and $b + 1$ votes for the second candidate, and
- the number of ways to count votes with exactly $a + 1$ votes for the first candidate and $b$ votes for the second candidate.

Formally:
$$\forall a, b. \text{all\_countings}(a + 1, b + 1) = \text{all\_countings}(a, b + 1) + \text{all\_countings}(a + 1, b)$$

### Informal proof
The proof proceeds by manipulating the definition of `all_countings`:

- Apply the definition of `all_countings` to both sides of the equation.
- Perform arithmetic simplifications:
  * $(a + 1) + (b + 1) = (a + b + 1) + 1$
  * $(a + 1) + b = a + b + 1$
- Let $n = a + b + 1$ to simplify the expressions.
- Apply the counting lemma which relates to ways of counting votes.
- Apply various simplifications and rewrites using properties of sets and cardinality, particularly:
  * The fact that votes for different candidates are distinct
  * The cardinality of sets with restrictions on naturally ordered elements
  * Properties of "in set" predicates for numeric ranges with restrictions

The proof ultimately reduces to showing equality through manipulations of set cardinality expressions and arithmetic.

### Mathematical insight
This theorem establishes a recursive relationship for counting the number of possible vote sequences with specific outcomes. It's essentially a combinatorial identity that shows how to break down the problem of counting vote sequences into smaller subproblems.

The result is similar in structure to the recursive formula for binomial coefficients: $\binom{n}{k} = \binom{n-1}{k-1} + \binom{n-1}{k}$, which suggests this theorem might be related to paths in a grid or similar combinatorial structures.

In the context of vote counting, this theorem provides an efficient way to compute the number of possible vote sequences by building up from simpler cases, which is a fundamental technique in dynamic programming and combinatorics.

### Dependencies
- `all_countings`: Definition for counting vote sequences with specific outcomes
- `COUNTING_LEMMA`: A lemma about counting properties
- `CARD_NUMSEG_RESTRICT_SUC`: Theorem about cardinality of restricted numeric ranges
- `IN_NUMSEG_RESTRICT_FALSE`: Theorem about membership in restricted numeric ranges
- `vote_DISTINCT`: Theorem establishing that votes for different candidates are distinct

### Porting notes
When porting this theorem:
1. Ensure the formal definition of `all_countings` is properly translated first
2. The proof relies on several arithmetic simplifications - most proof assistants have similar tactics but might require different syntax
3. The use of `ONCE_DEPTH_CONV let_CONV` suggests handling of let-expressions, which might be treated differently in other systems
4. Set cardinality operations are used extensively - make sure the target system has equivalent notions and theorems

---

## VALID_COUNTINGS_SUC

### Name of formal statement
VALID_COUNTINGS_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS_SUC = prove
 (`!a b. valid_countings (a + 1) (b + 1) =
                if a <= b then 0
                else valid_countings a (b + 1) + valid_countings (a + 1) b`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `b:num < a` THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[valid_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[FORALL_RANGE_SUC] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL] THEN
  SIMP_TAC[MESON[] `x = a /\ y = b /\ P x y <=> x = a /\ y = b /\ P a b`] THEN
  ASM_REWRITE_TAC[GT; LT_ADD_RCANCEL] THEN
  REWRITE_TAC[SET_RULE `{x | F} = EMPTY`; CARD_CLAUSES; ADD_CLAUSES]);;
```

### Informal statement
For all natural numbers $a$ and $b$:
$$\text{valid\_countings}(a + 1, b + 1) = 
\begin{cases} 
0 & \text{if } a \leq b \\
\text{valid\_countings}(a, b + 1) + \text{valid\_countings}(a + 1, b) & \text{if } a > b
\end{cases}$$

This theorem provides a recursive relation for the function `valid_countings` which likely counts valid voting configurations with $a$ votes for one outcome and $b$ votes for another.

### Informal proof
The proof proceeds as follows:

- Begin by considering the two cases: either $b < a$ or $b \geq a$, using the fact that $\neg(b < a)$ is equivalent to $a \leq b$.
  
- Rewrite using the definition of `valid_countings`.

- Apply algebraic simplifications to rewrite expressions:
  - $(a + 1) + (b + 1) = (a + b + 1) + 1$
  - $(a + 1) + b = a + b + 1$
  
- Introduce an abbreviation $n = a + b + 1$ to simplify expressions.

- Apply the `COUNTING_LEMMA` to transform the expression.

- Handle conditional expressions and rewrite using distinctness properties of the `vote` type.

- Use properties of set cardinality, particularly focusing on the cardinality of sets constrained by numerical ranges.

- For the case where $a > b$, show that the recursive relation holds. 

- For the case where $a \leq b$, show that the result is 0 by demonstrating that the relevant set becomes empty.

- Complete the proof by applying set theory rules and arithmetic simplifications.

### Mathematical insight
This theorem establishes a recursive relationship for the function `valid_countings`, which appears to count the number of valid vote sequences where one option receives $a$ votes and another receives $b$ votes. The theorem shows that:

1. When $a \leq b$, there are no valid countings (returning 0)
2. When $a > b$, we can compute the result recursively by summing two simpler cases

This recursive structure is typical of combinatorial counting problems and likely allows for efficient computation of `valid_countings` for larger inputs. The condition $a > b$ suggests that the validity constraint may require the first option to be ahead in votes throughout the counting process - a common constraint in ballot-counting problems.

### Dependencies
- `valid_countings` - Definition of valid vote countings
- `COUNTING_LEMMA` - A lemma about counting vote sequences
- `vote_DISTINCT` - Distinctness properties of the vote type 
- `CARD_NUMSEG_RESTRICT_SUC` - Property about cardinality of restricted numerical segments
- Various arithmetic and set theory rules from HOL Light's standard library

### Porting notes
When porting this theorem:
1. Ensure that the `valid_countings` function is defined consistently with HOL Light's version
2. The proof relies on several specialized lemmas about vote counting that would need to be ported first
3. The proof uses HOL Light's conditional expression handling, which might need different treatment in other proof assistants
4. Pay special attention to the set-theoretic reasoning near the end of the proof, as set representations vary between proof assistants

---

## ALL_COUNTINGS

### Name of formal statement
ALL_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS = prove
 (`!a b. all_countings a b = binom(a + b,a)`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  REWRITE_TAC[ARITH_RULE `1 = a + 1 <=> a = 0`; BINOM_EQ_0;
              ARITH_RULE `a < SUC a`] THEN
  REWRITE_TAC[ALL_COUNTINGS_SUC; ADD1] THEN
  ASM_REWRITE_TAC[binom; GSYM ADD1] THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_AC]);;
```

### Informal statement
For all natural numbers $a$ and $b$, the number of all countings from $a$ to $b$ (represented by the function `all_countings`) equals the binomial coefficient $\binom{a+b}{a}$.

Formally: $\forall a, b \in \mathbb{N}. \text{all\_countings}(a, b) = \binom{a+b}{a}$

### Informal proof
The proof proceeds by induction on $a$ and $b$:

* **Base case for $a=0$**: 
  - We need to show $\text{all\_countings}(0, b) = \binom{0+b}{0}$
  - By the definition of `ALL_COUNTINGS_0`, we know $\text{all\_countings}(0, b) = 1$
  - And we have $\binom{b}{0} = 1$ from the binomial coefficient properties
  
* **Base case for $b=0$ (with arbitrary $a$)**:
  - We need to show $\text{all\_countings}(a, 0) = \binom{a+0}{a} = \binom{a}{a}$
  - By the property `BINOM_REFL`, we know $\binom{a}{a} = 1$
  - And from the definition of `all_countings`, we must have $\text{all\_countings}(a, 0) = 1$

* **Inductive step for $a>0$ and $b>0$**:
  - Using the recursive definition `ALL_COUNTINGS_SUC`, we have:
    $\text{all\_countings}(a+1, b+1) = \text{all\_countings}(a, b+1) + \text{all\_countings}(a+1, b)$
  - By the induction hypotheses:
    $\text{all\_countings}(a, b+1) = \binom{a+(b+1)}{a} = \binom{a+b+1}{a}$
    $\text{all\_countings}(a+1, b) = \binom{(a+1)+b}{a+1} = \binom{a+b+1}{a+1}$
  - We need to show: $\text{all\_countings}(a+1, b+1) = \binom{(a+1)+(b+1)}{a+1} = \binom{a+b+2}{a+1}$
  - Using the recursive property of binomial coefficients:
    $\binom{a+b+2}{a+1} = \binom{a+b+1}{a+1} + \binom{a+b+1}{a}$
  - Therefore, $\text{all\_countings}(a+1, b+1) = \binom{a+b+2}{a+1}$

The proof also handles special cases using properties such as `BINOM_EQ_0` to establish that $\binom{n}{k} = 0$ when $n < k$.

### Mathematical insight
This theorem establishes a direct relationship between the counting function `all_countings` and the standard binomial coefficient. The binomial coefficient $\binom{a+b}{a}$ counts the number of ways to choose $a$ elements from a set of $a+b$ elements, which is equivalent to the number of ways to partition a sequence of length $a+b$ into two groups of sizes $a$ and $b$.

This relationship is fundamental in combinatorial counting problems and demonstrates an important connection between the recursive definition of `all_countings` and the well-understood properties of binomial coefficients.

### Dependencies
#### Theorems:
- `BINOM_REFL`: Establishes that $\binom{n}{n} = 1$ for any $n$
- `BINOM_EQ_0`: States that $\binom{n}{k} = 0$ if and only if $n < k$

#### Definitions:
- `binom`: The recursive definition of binomial coefficients
- `ALL_COUNTINGS_0` (implied): Establishes the base case for the counting function
- `ALL_COUNTINGS_SUC` (implied): Provides the recursive step for the counting function

### Porting notes
When porting this theorem, ensure that:
1. The binomial coefficient function is defined with the same recursive properties
2. The `all_countings` function must be properly defined with its recursive structure
3. The arithmetic simplifications may need different approaches in other systems
4. The induction strategy on two variables should be adapted to the target system's induction tactics

---

## VALID_COUNTINGS

### Name of formal statement
VALID_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS = prove
 (`!a b. (a + b) * valid_countings a b = (a - b) * binom(a + b,a)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; SUB_0; MULT_CLAUSES] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[VALID_COUNTINGS_0; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; ADD_CLAUSES; BINOM_REFL; SUB_0];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1; VALID_COUNTINGS_SUC] THEN REWRITE_TAC[GSYM ADD1] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ARITH_RULE `a <= b ==> SUC a - SUC b = 0`] THEN
  MATCH_MP_TAC(NUM_RING
   `~(a + b + 1 = 0) /\
    (SUC a + SUC b) *
    ((SUC a + b) * (a + SUC b) * y + (a + SUC b) * (SUC a + b) * z) =
    (SUC a + b) * (a + SUC b) * w
    ==> (SUC a + SUC b) * (y + z) = w`) THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MP_TAC(SPECL [`SUC b`; `a:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`b:num`; `SUC a`] BINOM_FACT) THEN
  MP_TAC(SPECL [`SUC b`; `SUC a`] BINOM_FACT) THEN
  REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  SUBST1_TAC(ARITH_RULE `b + a:num = a + b`) THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT))
   [`a:num`; `b:num`; `a + b:num`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
    GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB; REAL_OF_NUM_LE; LT_NZ;
    ARITH_RULE `~(a <= b) ==> b <= SUC a /\ SUC b <= a /\ SUC b <= SUC a`] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For all natural numbers $a$ and $b$, the following equality holds:
$$(a + b) \cdot \text{valid\_countings}(a, b) = (a - b) \cdot \binom{a + b}{a}$$

Where $\text{valid\_countings}(a, b)$ counts valid arrangements and $\binom{a + b}{a}$ is the binomial coefficient.

### Informal proof
The proof proceeds by induction on $a$ and then on $b$.

**Base cases:**
- For $a = 0$:
  - Using `VALID_COUNTINGS_0` (which states that valid_countings(0,b) = 0)
  - When $a = 0$, the equation becomes $b \cdot 0 = (0 - b) \cdot \binom{b}{0}$
  - Since $b \cdot 0 = 0$ and $(0 - b) = 0$ for natural numbers, this holds
  - This is verified for all $b$ by induction

- For $a > 0$ and $b = 0$:
  - Using `VALID_COUNTINGS_0` and `BINOM_REFL` (which states $\binom{n}{n} = 1$)
  - When $b = 0$, we have $a \cdot \text{valid\_countings}(a, 0) = a \cdot \binom{a}{a} = a \cdot 1 = a$

**Inductive step for $a > 0$ and $b > 0$:**
- We use `VALID_COUNTINGS_SUC` which gives the recursive formula for valid_countings
- The proof handles the case distinction based on whether $a \leq b$
- When $a \leq b$, we use the fact that $\text{SUC}(a) - \text{SUC}(b) = 0$ 
- For the main case, we apply algebraic manipulation using `NUM_RING`
- The proof uses `BINOM_FACT` to relate binomial coefficients with factorials:
  - $n! \cdot k! \cdot \binom{n+k}{k} = (n+k)!$
- Several factorial properties (via `FACT_LT`) are used
- The side conditions and final verification are handled through real arithmetic

### Mathematical insight
This theorem establishes a beautiful connection between valid countings and binomial coefficients. The term "valid_countings" likely refers to specific combinatorial arrangements where certain ordering constraints must be satisfied.

The formula shows that valid countings can be expressed in terms of binomial coefficients multiplied by a simple factor $(a-b)/(a+b)$. This is a typical result in enumerative combinatorics where seemingly complex counting problems can be reduced to well-understood quantities like binomial coefficients.

The strategic use of factorials through `BINOM_FACT` demonstrates the deep connection between binomial coefficients and factorials, which is central to combinatorial mathematics.

### Dependencies
#### Theorems
- `BINOM_REFL`: $\forall n. \binom{n}{n} = 1$
- `BINOM_FACT`: $\forall n\,k. n! \cdot k! \cdot \binom{n+k}{k} = (n+k)!$

#### Definitions
- `binom`: The binomial coefficient function, defined recursively by:
  - $\forall n. \binom{n}{0} = 1$
  - $\forall k. \binom{0}{\text{SUC}(k)} = 0$
  - $\forall n\,k. \binom{\text{SUC}(n)}{\text{SUC}(k)} = \binom{n}{\text{SUC}(k)} + \binom{n}{k}$

#### Other (not explicitly listed)
- `VALID_COUNTINGS_0`: Appears to define base cases for valid_countings
- `VALID_COUNTINGS_SUC`: Recursive definition for valid_countings
- `FACT_LT`: Properties of factorials

### Porting notes
When porting this theorem:
1. You'll need to first implement or port the definition of `valid_countings`, which isn't provided in the dependencies
2. The proof relies heavily on arithmetic tactics (`NUM_RING`, `REAL_RING`, `ARITH_RULE`), which may need different approaches in other systems
3. The pattern matching and case handling through `COND_CASES_TAC` will need appropriate equivalents in the target system
4. Pay attention to the natural number subtraction, as different systems may handle $a - b$ when $a < b$ differently

---

## BALLOT

### Name of formal statement
BALLOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BALLOT = prove
 (`!a b. &(valid_countings a b) =
            if a <= b then if b = 0 then &1 else &0
            else (&a - &b) / (&a + &b) *  &(all_countings a b)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[ALL_COUNTINGS_0; VALID_COUNTINGS_0] THEN
  REWRITE_TAC[LE_REFL; REAL_MUL_LID; LE_0; NOT_SUC; CONJUNCT1 LE] THEN
  SIMP_TAC[REAL_ADD_RID; REAL_SUB_RZERO; REAL_DIV_REFL; REAL_OF_NUM_EQ;
           NOT_SUC; REAL_MUL_LID] THEN
  MP_TAC(SPECL [`SUC a`; `SUC b`] VALID_COUNTINGS) THEN
  REWRITE_TAC[GSYM ALL_COUNTINGS; LE_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> (SUC a - SUC b) = 0`] THEN
  REWRITE_TAC[MULT_EQ_0; MULT_CLAUSES; ADD_EQ_0; NOT_SUC; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
               GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB;
               ARITH_RULE `~(a <= b) ==> SUC b <= SUC a`] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $a$ and $b$, the number of valid countings $\text{valid\_countings}(a, b)$ is given by:

$$\text{valid\_countings}(a, b) = 
\begin{cases} 
1 & \text{if } a \leq b \text{ and } b = 0 \\
0 & \text{if } a \leq b \text{ and } b \neq 0 \\
\frac{a - b}{a + b} \cdot \text{all\_countings}(a, b) & \text{if } a > b
\end{cases}$$

This theorem relates the number of valid countings to the total number of all possible countings using the fraction $\frac{a-b}{a+b}$ in the case where $a > b$.

### Informal proof
The proof proceeds by induction on both $a$ and $b$:

- Base cases:
  * When either $a = 0$ or $b = 0$, we use the theorems `ALL_COUNTINGS_0` and `VALID_COUNTINGS_0` to handle these base cases.
  * For $a = 0$, we have $a \leq b$, so we check if $b = 0$:
    - If $b = 0$, then $\text{valid\_countings}(0, 0) = 1$
    - Otherwise, $\text{valid\_countings}(0, b) = 0$ for $b > 0$

- For the inductive case with $a$ and $b$, we consider $\text{valid\_countings}(\text{SUC}(a), \text{SUC}(b))$:
  * We apply the theorem `VALID_COUNTINGS` with $\text{SUC}(a)$ and $\text{SUC}(b)$.
  * We rewrite using the relationship to `ALL_COUNTINGS`.
  * We split the case analysis based on whether $a \leq b$:
    - If $a \leq b$, then $\text{SUC}(a) - \text{SUC}(b) = 0$ (simplifying with an arithmetic rule)
    - If $a > b$, we simplify the numerical expressions using properties of real number conversions
  * The final step uses the `REAL_FIELD` conversion to verify the algebraic equality.

### Mathematical insight
This theorem is related to the Ballot problem in combinatorics, which asks for the probability that candidate A maintains a lead over candidate B throughout the counting of votes, given that A receives a total of a votes and B receives b votes, with a > b.

The formula $\frac{a-b}{a+b}$ is a well-known result in ballot problems. It represents the probability that in a random counting order, candidate A always stays ahead of candidate B, given the final counts a and b.

The theorem provides a closed-form expression for counting valid ballot sequences, connecting the number of valid countings to the total number of possible countings. When a ≤ b, the result is straightforward (either 0 or 1 depending on b), but when a > b, the formula involves the relative difference between votes.

### Dependencies
- Theorems:
  - `ALL_COUNTINGS_0`: Likely defines base cases for counting all possible counting sequences
  - `VALID_COUNTINGS_0`: Likely defines base cases for counting valid sequences
  - `VALID_COUNTINGS`: Main theorem about valid countings relation
  
- Tactics and conversions:
  - `INDUCT_TAC`: Induction tactic
  - `REWRITE_TAC`: Rewriting tactic
  - `SIMP_TAC`: Simplification tactic
  - `REAL_FIELD`: Field arithmetic conversion for real numbers

### Porting notes
When porting this theorem:
- Ensure that `valid_countings` and `all_countings` are properly defined
- The proof relies heavily on arithmetic properties and real number conversions
- You'll need equivalents to the HOL Light arithmetic reasoning library, particularly for conversions between natural numbers and reals
- Case analysis on inequalities is central to the proof structure

---

