# combinations.ml

## Overview

Number of statements: 2

This file formalizes the relationship between binomial coefficients and the number of ways to choose k elements from an n-element set (combinations). It builds on the existing binomial coefficient definitions from the binomial.ml library, proving theorems that connect the combinatorial interpretation with the algebraic properties. The file establishes formal results about counting combinations and selections, including key identities relating to the cardinality of finite sets under various selection criteria.

## NUMBER_OF_COMBINATIONS

### NUMBER_OF_COMBINATIONS
- NUMBER_OF_COMBINATIONS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NUMBER_OF_COMBINATIONS = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`,
  MATCH_ACCEPT_TAC HAS_SIZE_RESTRICTED_POWERSET);;
```

### Informal statement
For any natural numbers $n$ and $m$, and any set $s$ of type $A$, if $s$ has size $n$ (that is, $s$ contains exactly $n$ elements), then the collection of all subsets $t$ of $s$ that have size $m$ (that is, $\{t \mid t \subseteq s \land |t| = m\}$) has size $\binom{n}{m}$ (the binomial coefficient "$n$ choose $m$").

Formally:
$$\forall n, m \in \mathbb{N}, \forall s \subseteq A. \; |s| = n \Rightarrow \left|\{t \mid t \subseteq s \land |t| = m\}\right| = \binom{n}{m}$$

### Informal proof
This theorem is proven by directly applying the theorem `HAS_SIZE_RESTRICTED_POWERSET`, which states exactly the same result.

The original proof in `HAS_SIZE_RESTRICTED_POWERSET` uses induction on the binomial coefficient definition, showing that the number of subsets of size $m$ from a set of size $n$ satisfies the same recurrence relation as the binomial coefficient.

### Mathematical insight
This theorem formalizes the well-known combinatorial interpretation of binomial coefficients: $\binom{n}{m}$ counts the number of ways to choose $m$ elements from a set of $n$ elements, or equivalently, the number of $m$-element subsets of an $n$-element set.

This result is fundamental in combinatorics and probability theory. It connects the algebraic definition of binomial coefficients (as defined by the recurrence relation) with its combinatorial interpretation.

The theorem confirms that the binomial coefficient function `binom` defined in HOL Light correctly captures this combinatorial meaning.

### Dependencies
- Theorems:
  - `HAS_SIZE_RESTRICTED_POWERSET`: The main theorem that establishes that the number of subsets of size $m$ from a set of size $n$ is equal to $\binom{n}{m}$
  
- Definitions:
  - `binom`: The binomial coefficient function defined recursively as:
    - $\binom{n}{0} = 1$ for all $n$
    - $\binom{0}{k+1} = 0$ for all $k$
    - $\binom{n+1}{k+1} = \binom{n}{k+1} + \binom{n}{k}$ for all $n,k$

### Porting notes
When porting this theorem:
1. Ensure the binomial coefficient is defined with the same recurrence relation
2. Verify that set operations like `SUBSET` and size predicates like `HAS_SIZE` have equivalent meanings
3. The proof is straightforward if `HAS_SIZE_RESTRICTED_POWERSET` has already been ported, as it's just a direct application

---

## NUMBER_OF_COMBINATIONS_EXPLICIT

### Name of formal statement
NUMBER_OF_COMBINATIONS_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMBER_OF_COMBINATIONS_EXPLICIT = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE
            (if n < m then 0 else FACT(n) DIV (FACT(m) * FACT(n - m)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP NUMBER_OF_COMBINATIONS) THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP; BINOM; MULT_AC]);;
```

### Informal statement
For any natural numbers $n$ and $m$, and a set $s$ of type $A$, if $s$ has cardinality $n$ (i.e., $s$ HAS_SIZE $n$), then the set of all subsets $t$ of $s$ such that $t$ has cardinality $m$ (i.e., $t$ SUBSET $s$ $\land$ $t$ HAS_SIZE $m$) has cardinality:
$$\begin{cases}
0 & \text{if}\ n < m \\
\frac{n!}{m!(n-m)!} & \text{if}\ n \geq m
\end{cases}$$

### Informal proof
This theorem is an explicit restatement of the `NUMBER_OF_COMBINATIONS` theorem, expressing the cardinality formula directly in terms of factorials.

The proof proceeds as follows:
- We apply the `NUMBER_OF_COMBINATIONS` theorem, which states that the number of subsets of size $m$ from a set of size $n$ is $\binom{n}{m}$
- We then use the `BINOM` theorem which gives the explicit formula for binomial coefficients: $\binom{n}{m} = \frac{n!}{m!(n-m)!}$ when $m \leq n$ and $0$ otherwise
- The conditions in the if-statement are adjusted using logical equivalences:
  - `GSYM NOT_LE` transforms "$m \leq n$" to "not $n < m$"
  - `COND_SWAP` reorders the conditional branches
- Finally, `MULT_AC` handles associativity and commutativity of multiplication in the factorial expression

### Mathematical insight
This theorem provides the explicit formula for the number of ways to choose $m$ elements from a set of $n$ elements, which is the binomial coefficient $\binom{n}{m}$. It is a fundamental result in combinatorics, often written as $\binom{n}{m} = \frac{n!}{m!(n-m)!}$. The result is important because:

1. It gives a closed-form formula for counting combinations
2. It connects set-theoretic concepts (subsets of a given size) with algebraic expressions (factorials and division)
3. It is used extensively in probability theory, statistics, and combinatorial arguments

This theorem makes explicit what the number of combinations formula is in terms of factorials, which is often more useful for computational purposes than recursive definitions of binomial coefficients.

### Dependencies
- `NUMBER_OF_COMBINATIONS`: States that the number of subsets of size $m$ from a set of size $n$ equals the binomial coefficient $\binom{n}{m}$
- `BINOM`: Provides the explicit formula for the binomial coefficient $\binom{n}{m}$ in terms of factorials
- `GSYM NOT_LE`: Symmetry property for negation of less-than-or-equal relation
- `COND_SWAP`: Tactic for reordering conditional branches
- `MULT_AC`: Associativity and commutativity properties of multiplication

### Porting notes
When porting this theorem:
1. Ensure that the target system has a definition of factorial and binomial coefficients
2. Verify that the division operation in the target system behaves correctly for integers (some systems might require explicit handling of division with natural numbers)
3. The proof relies on the NUMBER_OF_COMBINATIONS theorem, so that would need to be ported first
4. The definition of HAS_SIZE and SUBSET should be consistent with HOL Light's definitions

---

