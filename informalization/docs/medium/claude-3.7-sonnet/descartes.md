# descartes.ml

## Overview

Number of statements: 24

This file formalizes Descartes's Rule of Signs, which relates the number of positive real roots of a polynomial to sign variations in its coefficients. It builds upon real analysis concepts from the multivariate library to provide a complete formalization of Arthan's proof via induction. The implementation includes definitions for counting sign variations, theorems establishing the relationship between these variations and positive roots, and the formal proof of the rule itself.

## OPPOSITE_SIGNS

### OPPOSITE_SIGNS
- OPPOSITE_SIGNS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OPPOSITE_SIGNS = prove
 (`!a b:real. a * b < &0 <=> &0 < a /\ b < &0 \/ a < &0 /\ &0 < b`,
  REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < a * --b`; REAL_MUL_POS_LT] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any real numbers $a$ and $b$, the product $a \cdot b < 0$ if and only if either $0 < a$ and $b < 0$, or $a < 0$ and $0 < b$.

In other words, the product of two real numbers is negative if and only if exactly one of them is positive and the other is negative.

### Informal proof
The proof proceeds by rewriting the statement to an equivalent form and then using arithmetic reasoning:

1. First, the statement $a \cdot b < 0$ is rewritten as $0 < a \cdot (-b)$ using the real arithmetic fact that $a \cdot b < 0 \iff 0 < a \cdot (-b)$
2. Then, the theorem `REAL_MUL_POS_LT` is applied, which states that a product of real numbers is positive if and only if both factors have the same sign
3. Finally, `REAL_ARITH_TAC` completes the proof by handling the remaining real arithmetic reasoning

### Mathematical insight
This theorem captures the fundamental property that the sign of a product depends on the signs of its factors. It's a basic but essential result in real analysis and is used in various contexts, including:

- Analyzing the behavior of functions (e.g., where they change sign)
- In calculus, particularly when examining roots and critical points
- In algorithms like Descartes's Rule of Signs (as indicated in the comment)

The result is intuitive: a product is negative precisely when one factor is positive and the other is negative.

### Dependencies
- Theorems:
  - `REAL_ARITH`
  - `REAL_MUL_POS_LT`

### Porting notes
This theorem should be straightforward to port to other systems, as it relies on basic properties of real numbers that are standard in most mathematical libraries. The main requirement is having the equivalents of:
- Real arithmetic tactics
- The basic property that a product is positive iff both factors have the same sign

In some systems, this might already exist as a library theorem about signs of products.

AI Assistant: I've provided a comprehensive translation of the OPPOSITE_SIGNS theorem from HOL Light to mathematical English, including its formal structure, informal statement, proof approach, mathematical context, and porting considerations. The theorem establishes when the product of two real numbers is negative, which is a fundamental property used in many mathematical contexts, particularly in analysis of function behavior.

---

## VARIATION_SET_FINITE

### Name of formal statement
VARIATION_SET_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SET_FINITE = prove
 (`FINITE s ==> FINITE {p,q | p IN s /\ q IN s /\ P p q}`,
  REWRITE_TAC[SET_RULE
   `{p,q | p IN s /\ q IN t /\ R p q} =
    {p,q | p IN s /\ q IN {q | q IN t /\ R p q}}`] THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT]);;
```

### Informal statement
If $s$ is a finite set, then the set of all ordered pairs $(p, q)$ such that $p \in s$, $q \in s$, and $P(p, q)$ holds is also finite.

Formally: $\text{FINITE}(s) \Rightarrow \text{FINITE}(\{(p, q) \mid p \in s \land q \in s \land P(p, q)\})$

### Informal proof
The proof proceeds by rewriting the set of ordered pairs into a form suitable for applying existing theorems about finiteness:

1. First, we rewrite the set $\{(p, q) \mid p \in s \land q \in s \land P(p, q)\}$ as $\{(p, q) \mid p \in s \land q \in \{q \mid q \in s \land P(p, q)\}\}$ using the `SET_RULE`.

2. Then we apply `FINITE_PRODUCT_DEPENDENT` and `FINITE_RESTRICT` theorems:
   - `FINITE_RESTRICT` establishes that if $s$ is finite, then $\{q \in s \mid P(p, q)\}$ is also finite for any $p$
   - `FINITE_PRODUCT_DEPENDENT` shows that the set of pairs $(p, q)$ where $p \in s$ and $q \in t(p)$ is finite when $s$ is finite and $t(p)$ is finite for each $p \in s$

The proof is completed by applying these theorems through the simplification tactic `SIMP_TAC`.

### Mathematical insight
This theorem extends the basic property that finite sets generate finite products to the case where we have a relation-like structure defined by a predicate. It's a useful building block for proving finiteness of sets defined by relations or binary predicates over finite domains.

The result is particularly useful in contexts where we need to work with binary relations restricted to finite domains, such as in finite graph theory or when working with finite state machines.

### Dependencies
- Theorems:
  - `SET_RULE` (used for set rewriting)
  - `FINITE_PRODUCT_DEPENDENT` (finiteness of dependent products)
  - `FINITE_RESTRICT` (finiteness of restricted sets)

### Porting notes
When porting to other proof assistants:
- The underlying principle is straightforward, but the exact presentation may differ
- In systems like Lean or Coq, this might be proved using existing theorems about the cardinality of finite sets
- The approach would be similar: rewrite in terms of restricted sets and dependent products, then apply appropriate finiteness theorems

---

## variation

### Name of formal statement
variation

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let variation = new_definition
 `variation s (a:num->real) =
     CARD {(p,q) | p IN s /\ q IN s /\ p < q /\
                   a(p) * a(q) < &0 /\
                   !i. i IN s /\ p < i /\ i < q ==> a(i) = &0 }`;;
```

### Informal statement
The definition `variation s (a:num->real)` computes the number of variations in sign in a sequence of coefficients $a$ indexed by a set $s$ of natural numbers. Specifically, it counts the number of pairs $(p,q)$ such that:
- $p, q \in s$
- $p < q$
- $a(p) \cdot a(q) < 0$ (meaning they have opposite signs)
- For all $i \in s$ where $p < i < q$, we have $a(i) = 0$

Mathematically, this represents the count of sign changes in the sequence when skipping zero entries.

### Informal proof
This is a definition, so there is no proof to explain.

### Mathematical insight
The variation of sign in a sequence of coefficients is an important concept in algebraic analysis, particularly in Descartes' rule of signs and Sturm sequences for counting real roots of polynomials.

In polynomial analysis, the number of sign variations in the coefficient sequence provides an upper bound on the number of positive real roots of the polynomial. More generally, variations in sign sequences appear in numerous results concerning the location of zeros of functions.

This definition captures precisely when two non-zero terms have an actual sign change between them, while properly accounting for any zero terms that might appear between them (which are ignored for the purpose of counting sign changes).

### Dependencies
No explicit dependencies are provided, but the definition uses:
- Set theory operations
- The `CARD` operator, which returns the cardinality of a set
- Standard ordering on natural numbers
- Arithmetic operations on real numbers

### Porting notes
When porting this definition to other systems:
- Ensure that the system has a suitable way to represent the cardinality of finite sets
- Consider how the target system handles empty sets in this context
- The definition assumes that the set `s` is finite, as `CARD` is being applied to a derived set
- In systems with dependent types, you might need to provide an explicit proof that the set is finite

---

## VARIATION_EQ

### VARIATION_EQ
- The formal statement is named `VARIATION_EQ`.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VARIATION_EQ = prove
 (`!a b s. (!i. i IN s ==> a i = b i) ==> variation s a = variation s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
For all functions $a$ and $b$, and for any set $s$, if $a$ and $b$ agree on all points in $s$ (i.e., $\forall i \in s, a(i) = b(i)$), then $\text{variation}(s, a) = \text{variation}(s, b)$.

### Informal proof
The proof proceeds as follows:
- Apply the definition of `variation`.
- Apply functional extensionality (via `AP_TERM_TAC`) to show that equal functions applied to equal arguments produce equal results.
- Rewrite using the extensionality principle for sets (`EXTENSION`). This states that two sets are equal if they contain the same elements.
- Use the fact that two pairs are equal if and only if their corresponding components are equal (`FORALL_PAIR_THM` and `IN_ELIM_PAIR_THM`).
- Use the assumption that $a$ and $b$ agree on all points in $s$ to conclude the proof using the MESON automated reasoning tactic.

### Mathematical insight
This theorem establishes that the variation of functions over a set depends only on the values of the functions on that set. In other words, if two functions agree on all points of a set, then they have the same variation over that set. This is an intuitive property: the variation (which likely measures how a function changes over a set) should only depend on the function's behavior within the specified domain, not outside it.

This result would be important for simplifying proofs about variations, allowing substitution of functions that are equal on the relevant domain.

### Dependencies
#### Theorems
- `EXTENSION`: Two sets are equal if and only if they contain the same elements.
- `FORALL_PAIR_THM`: Universal quantification over pairs.
- `IN_ELIM_PAIR_THM`: Membership condition for pairs.

#### Definitions
- `variation`: The definition of variation of a function over a set (not provided in the dependencies).

### Porting notes
When porting this theorem:
1. Ensure the `variation` function is defined consistently in the target system.
2. The proof relies on extensionality principles for functions and sets, which most proof assistants support but may express differently.
3. The automated reasoning step using `ASM_MESON_TAC` may need to be replaced with appropriate automation or manual proof steps in the target system.

---

## VARIATION_SUBSET

### Name of formal statement
VARIATION_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SUBSET = prove
 (`!a s t. t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)
           ==> variation s a = variation t a`,
  REWRITE_TAC[IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL]);;
```

### Informal statement
For any function $a$ and sets $s$ and $t$, if $t \subseteq s$ and for all $i \in s \setminus t$, $a(i) = 0$, then $\text{variation}(s, a) = \text{variation}(t, a)$.

### Informal proof
The proof proceeds as follows:

- First, we rewrite the goals using the definitions of set difference (`IN_DIFF`) and subset (`SUBSET`).
- After stripping the assumptions, we rewrite the goal using the definition of `variation`.
- We apply `AP_TERM_TAC` to focus on showing the equality of the arguments.
- We then rewrite the goal to expand the extensional equality of sets using `EXTENSION` and `FORALL_PAIR_THM`.
- Finally, we use the assumptions along with properties of real multiplication (specifically that multiplication by zero gives zero) and the irreflexivity of the less-than relation to complete the proof.

The key insight is that elements in $s \setminus t$ don't contribute to the variation because $a(i) = 0$ for these elements, so the variation computed over $s$ equals the variation computed over $t$.

### Mathematical insight
This theorem states that the variation of a function over a set remains unchanged if we restrict the set by removing points where the function is zero. This is intuitive as zero-valued points don't contribute to the "variation" or changes in the function across the domain.

The result is useful for simplifying variation calculations by allowing us to ignore regions where the function is zero. It's particularly relevant in analysis when working with functions that are zero outside a compact support.

### Dependencies
#### Theorems
- `IN_DIFF` - Definition of set difference membership
- `SUBSET` - Definition of subset relation
- `variation` - Definition of variation
- `EXTENSION` - Extensional equality of sets
- `FORALL_PAIR_THM` - Quantification over pairs
- `IN_ELIM_PAIR_THM` - Membership of pairs in sets
- `REAL_MUL_LZERO` - Multiplication by zero on the left
- `REAL_MUL_RZERO` - Multiplication by zero on the right
- `REAL_LT_REFL` - Irreflexivity of the less-than relation

### Porting notes
When porting this theorem:
- Ensure that the `variation` function is defined correctly in the target system
- The proof relies on MESON automated reasoning, so in systems with weaker automation, you may need to expand some of the reasoning steps explicitly
- Pay attention to how set operations and extensionality are handled in the target system

---

## VARIATION_SPLIT

### Name of formal statement
VARIATION_SPLIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SPLIT = prove
 (`!a s n.
        FINITE s /\ n IN s /\ ~(a n = &0)
        ==> variation s a = variation {i | i IN s /\ i <= n} a +
                            variation {i | i IN s /\ n <= i} a`,
  REWRITE_TAC[variation] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_SIMP_TAC[VARIATION_SET_FINITE; FINITE_RESTRICT] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
    REWRITE_TAC[IN_UNION; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[] THEN ASSUME_TAC th) THEN
      SIMP_TAC[TAUT `~(a /\ b) <=> ~b \/ ~a`] THEN MATCH_MP_TAC MONO_OR] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    TRY(FIRST_ASSUM MATCH_MP_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[]) THEN
    ASM_ARITH_TAC]);;
```

### Informal statement
For any sequence $a$, finite set $s$, and number $n$ such that $n \in s$ and $a(n) \neq 0$, the variation of $a$ over $s$ equals the sum of the variation of $a$ over $\{i \in s \mid i \leq n\}$ and the variation of $a$ over $\{i \in s \mid n \leq i\}$.

Formally:
$$\forall a,s,n.\ \text{FINITE}(s) \land n \in s \land a(n) \neq 0 \implies \text{variation}(s,a) = \text{variation}(\{i \mid i \in s \land i \leq n\},a) + \text{variation}(\{i \mid i \in s \land n \leq i\},a)$$

### Informal proof
The proof proceeds as follows:

* First, we rewrite the goal using the definition of `variation`.
* We then apply `SYM_CONV` to convert the equality to its symmetric form.
* The key step is applying `CARD_UNION_EQ`, which states that the cardinality of a union of two sets equals the sum of their individual cardinalities minus the cardinality of their intersection, when the sets are finite.

* To apply this theorem, we need to verify:
  * Both restricted sets are finite (established using `VARIATION_SET_FINITE` and `FINITE_RESTRICT`)
  * The intersection of the two variation sets is empty
  * The union of the two variation sets equals the original variation set

* For the intersection being empty:
  * We show that the two sets $\{(i,j) \mid i,j \in s \land i < j \land \text{sgn}(a(i)) \neq \text{sgn}(a(j)) \land i \leq n \land j \leq n\}$ and $\{(i,j) \mid i,j \in s \land i < j \land \text{sgn}(a(i)) \neq \text{sgn}(a(j)) \land n \leq i \land n \leq j\}$ cannot have common elements because if $(i,j)$ is in both sets, then $i \leq n < n \leq i$ which is a contradiction.

* For the union equaling the original set:
  * We prove the equivalence: $(i,j)$ is in the variation set for $s$ if and only if it's in one of the two restricted variation sets.
  * The critical insight is that since $a(n) \neq 0$, any pair $(i,j)$ that crosses over $n$ (i.e., $i < n < j$) must have the same property as either $(i,n)$ or $(n,j)$ regarding sign changes.
  * This uses the fact that sign changes are transitive: if $\text{sgn}(a(i)) \neq \text{sgn}(a(n))$ and $\text{sgn}(a(n)) \neq \text{sgn}(a(j))$, then $\text{sgn}(a(i)) \neq \text{sgn}(a(j))$.

### Mathematical insight
This theorem provides a way to split the computation of variation into two parts at a point where the sequence is non-zero. This is useful for divide-and-conquer approaches to analyzing variations in a sequence.

The key insight is that when splitting at a point $n$ where $a(n) \neq 0$, we don't double-count or miss any sign changes. Because $a(n)$ has a definite sign, any sign change that crosses over $n$ is correctly accounted for in one of the two parts.

This result is important for analyzing properties of sequences with varying signs, which appears in various contexts like analyzing the number of roots of polynomials or studying oscillatory behavior of functions.

### Dependencies
- Definitions:
  - `variation`: Counts the number of sign changes in a sequence over a given set
  - `VARIATION_SET_FINITE`: States that the variation set is finite when the original set is finite
- Theorems:
  - `CARD_UNION_EQ`: Relates the cardinality of a union to the cardinalities of the individual sets
  - `FINITE_RESTRICT`: States that restricting a finite set results in a finite set

### Porting notes
When porting this theorem:
- Ensure the definition of variation is consistent, particularly regarding how sign changes are counted.
- The proof relies heavily on set-theoretic reasoning and transitive properties of sign changes.
- Be careful with the handling of the special point $n$ where the sequence is non-zero, as this is crucial for the proof's correctness.

---

## VARIATION_SPLIT_NUMSEG

### VARIATION_SPLIT_NUMSEG

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let VARIATION_SPLIT_NUMSEG = prove
 (`!a m n p. n IN m..p /\ ~(a n = &0)
             ==> variation(m..p) a = variation(m..n) a + variation(n..p) a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b /\ c ==> a ==> d`]
     VARIATION_SPLIT)) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC);;
```

### Informal statement
For all functions $a$ and all integers $m$, $n$, and $p$, if $n \in [m,p]$ (i.e., $m \leq n \leq p$) and $a(n) \neq 0$, then:

$$\text{variation}([m,p], a) = \text{variation}([m,n], a) + \text{variation}([n,p], a)$$

where $\text{variation}(S, a)$ represents the variation of the function $a$ over the set $S$.

### Informal proof
The proof proceeds as follows:

* We begin by applying the more general theorem `VARIATION_SPLIT` which handles arbitrary finite sets.
* We rewrite using the fact that numerical segments (`m..p`) are finite sets (`FINITE_NUMSEG`).
* We then use binary operation tactics (`BINOP_TAC`) and application theorems (`AP_THM_TAC`, `AP_TERM_TAC`) to break down the equality.
* We rewrite using the extensional equality of sets (`EXTENSION`), eliminating set membership (`IN_ELIM_THM`), and expanding membership in numerical segments (`IN_NUMSEG`).
* Finally, we use arithmetic reasoning to complete the proof, making use of our assumption that $n \in [m,p]$ which is rewritten as the numerical inequality $m \leq n \leq p$.

### Mathematical insight
This theorem is a specialized case of the more general `VARIATION_SPLIT` theorem, specifically for numerical segments. It establishes that the variation of a function over a segment can be split at any point within the segment where the function is non-zero. This additivity property is fundamental in analysis when working with variation of functions.

The condition that $a(n) \neq 0$ is crucial because the variation might behave differently at points where the function equals zero, particularly regarding sign changes.

### Dependencies
- Theorems:
  - `VARIATION_SPLIT`: The general theorem for splitting variation across sets
  - `FINITE_NUMSEG`: Theorem establishing that numerical segments are finite sets
  - `EXTENSION`: Theorem about extensional equality of sets
  - `IN_ELIM_THM`: Theorem for eliminating set membership
  - `IN_NUMSEG`: Theorem defining membership in numerical segments

### Porting notes
When porting this theorem:
- Ensure the receiving system has a compatible definition of the `variation` function
- The notation `m..p` represents a closed integer interval from m to p
- The HOL Light tactic `ASM_ARITH_TAC` handles linear arithmetic reasoning automatically - this may require more explicit steps in other proof assistants

---

## VARIATION_1

### VARIATION_1
- VARIATION_1

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VARIATION_1 = prove
 (`!a n. variation {n} a = 0`,
  REWRITE_TAC[variation; IN_SING] THEN
  REWRITE_TAC[ARITH_RULE `p:num = n /\ q = n /\ p < q /\ X <=> F`] THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]);;
```

### Informal statement
For any function $a$ and any natural number $n$, the variation of $a$ over the singleton set $\{n\}$ is 0. 

Formally, $\forall a, n. \text{variation}(\{n\}, a) = 0$.

### Informal proof
The proof follows from the definition of variation and properties of singleton sets:

1. By the definition of `variation`, we calculate the number of pairs $(p,q)$ where $p,q \in \{n\}$, $p < q$, and $a(p) \cdot a(q) < 0$.

2. For a singleton set $\{n\}$, the only element is $n$, so the only possible pair would be $(n,n)$.

3. However, for any pair $(p,q)$ in the variation computation, we require $p < q$, which is impossible when $p = q = n$.

4. Therefore, there are no valid pairs to count, meaning the set of such pairs is empty.

5. Since the cardinality of an empty set is 0, the variation is 0.

### Mathematical insight
This theorem establishes a basic boundary case for the variation function - a singleton set can have no variation because variation measures sign changes between different points, and a singleton set contains only one point, so there are no pairs of distinct points to compare.

The result is unsurprising but forms an important base case for reasoning about variation on larger sets. The variation function likely measures the number of sign changes of a function over a set, which is a concept used in various areas of analysis and algebra, such as Sturm's theorem for counting real roots of polynomials.

### Dependencies
- `variation`: Definition of variation of a function over a set
- `IN_SING`: Theorem about membership in singleton sets
- `CARD_CLAUSES`: Theorem about cardinality of sets
- `EXTENSION`: Theorem about set equality via extensionality
- `FORALL_PAIR_THM`: Theorem about universal quantification over pairs
- `IN_ELIM_PAIR_THM`: Theorem about membership of pairs
- `NOT_IN_EMPTY`: Theorem stating that no element belongs to the empty set

### Porting notes
When porting this theorem, ensure that the definition of `variation` is correctly implemented first. The proof relies on set-theoretic properties that should be available in most proof assistants, though the exact theorems used may have different names or slightly different formulations.

---

## VARIATION_2

### VARIATION_2
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VARIATION_2 = prove
 (`!a m n. variation {m,n} a = if a(m) * a(n) < &0 then 1 else 0`,
  GEN_TAC THEN MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_AC; VARIATION_1; GSYM REAL_NOT_LE; REAL_LE_SQUARE];
    REWRITE_TAC[INSERT_AC; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[variation; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ c /\ d /\ e <=> (a /\ b /\ c) /\ d /\ e`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `m:num < n
      ==> ((p = m \/ p = n) /\ (q = m \/ q = n) /\ p < q <=>
           p = m /\ q = n)`] THEN
    REWRITE_TAC[MESON[] `(p = m /\ q = n) /\ X p q <=>
                         (p = m /\ q = n) /\ X m n`] THEN
    REWRITE_TAC[ARITH_RULE `(i:num = m \/ i = n) /\ m < i /\ i < n <=> F`] THEN
    ASM_CASES_TAC `a m * a(n:num) < &0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[SET_RULE `{p,q | p = a /\ q = b} = {(a,b)}`] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
      SIMP_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]]]);;
```

### Informal statement
For all real-valued functions $a$ and all natural numbers $m$ and $n$, the variation of $a$ on the set $\{m,n\}$ is:
$$\text{variation}(\{m,n\}, a) = \begin{cases}
1 & \text{if } a(m) \cdot a(n) < 0 \\
0 & \text{otherwise}
\end{cases}$$

This theorem states that the variation of a function on a two-element set counts the number of sign changes, which can only be either 0 or 1.

### Informal proof
The proof proceeds as follows:

* We first use the "without loss of generality" principle (`WLOG_LT`) to assume that $m < n$, since:
  - The variation on $\{m,n\}$ is the same as the variation on $\{n,m\}$ (by the commutativity of sets)
  - The condition $a(m) \cdot a(n) < 0$ is symmetric with respect to $m$ and $n$ (by commutativity of multiplication)

* When $m < n$, we expand the definition of variation:
  $$\text{variation}(\{m,n\}, a) = \text{CARD}\{\,(p,q) \mid p,q \in \{m,n\} \wedge p < q \wedge a(p) \cdot a(q) < 0\,\}$$

* Since $m < n$ and $p,q \in \{m,n\}$ with $p < q$, the only possible pair is $(p,q) = (m,n)$

* So we have two cases:
  - If $a(m) \cdot a(n) < 0$: The set contains exactly the pair $(m,n)$, so its cardinality is 1
  - If $a(m) \cdot a(n) \geq 0$: The set is empty, so its cardinality is 0

* This matches the statement of the theorem.

### Mathematical insight
This theorem characterizes the variation function for the simplest non-trivial case: a set with just two points. The variation counts sign changes of a function, which is a fundamental concept in the analysis of functions and is used in results like Descartes' rule of signs.

The result shows that on a two-element set, the variation is binary (either 0 or 1) and directly corresponds to whether the function values at these points have opposite signs.

### Dependencies
- `VARIATION_1`: Likely defines the variation function or gives its basic properties
- `INSERT_AC`: Properties about set insertion operation being associative and commutative
- `GSYM REAL_NOT_LE`: Conversion between negated inequalities for real numbers
- `REAL_LE_SQUARE`: Properties of squares of real numbers
- `REAL_MUL_SYM`: Commutativity of real multiplication
- Various arithmetic rules and set-theoretic operations

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the variation function is defined first with the same semantics
- The proof relies heavily on set operations and cardinality, which might have different representations in other systems
- The WLOG (without loss of generality) principle might require different tactics in other systems

---

## VARIATION_3

### Name of formal statement
VARIATION_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_3 = prove
 (`!a m n p.
        m < n /\ n < p
        ==> variation {m,n,p} a = if a(n) = &0 then variation{m,p} a
                                  else variation {m,n} a + variation{n,p} a`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC VARIATION_SUBSET THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`a:num->real`; `{m:num,n,p}`; `n:num`] VARIATION_SPLIT) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC]);;
```

### Informal statement
For any function $a: \mathbb{N} \to \mathbb{R}$ and natural numbers $m$, $n$, and $p$ such that $m < n < p$, the following equality holds:

$$\text{variation} \{m,n,p\} \, a = \begin{cases}
\text{variation} \{m,p\} \, a & \text{if } a(n) = 0 \\
\text{variation} \{m,n\} \, a + \text{variation} \{n,p\} \, a & \text{otherwise}
\end{cases}$$

This theorem describes how the variation of a function over a set of three points can be decomposed, depending on whether the middle point evaluates to zero.

### Informal proof
The proof proceeds in two cases, based on whether $a(n) = 0$:

1. **Case 1**: When $a(n) = 0$
   * Apply the `VARIATION_SUBSET` theorem, which states that removing points where the function vanishes does not change the variation
   * Since $a(n) = 0$, we can remove the point $n$ from the set $\{m,n,p\}$, resulting in $\{m,p\}$
   * Therefore, $\text{variation} \{m,n,p\} \, a = \text{variation} \{m,p\} \, a$

2. **Case 2**: When $a(n) \neq 0$
   * Apply the `VARIATION_SPLIT` theorem with appropriate instantiations:
     * For function $a$
     * For set $\{m,n,p\}$
     * For splitting point $n$
   * This gives us $\text{variation} \{m,n,p\} \, a = \text{variation} (\{m,n,p\} \cap \{k \mid k \leq n\}) \, a + \text{variation} (\{m,n,p\} \cap \{k \mid k \geq n\}) \, a$
   * Simplify the sets:
     * $\{m,n,p\} \cap \{k \mid k \leq n\} = \{m,n\}$ since $m < n < p$
     * $\{m,n,p\} \cap \{k \mid k \geq n\} = \{n,p\}$ 
   * Therefore, $\text{variation} \{m,n,p\} \, a = \text{variation} \{m,n\} \, a + \text{variation} \{n,p\} \, a$

### Mathematical insight
This theorem provides an important decomposition principle for the variation of a function over three points. It shows how the total variation can be split into two components based on the middle point:

1. If the function vanishes at the middle point, we can ignore that point entirely
2. Otherwise, the variation is the sum of variations across the two intervals

This result is particularly useful in analyzing the behavior of functions with respect to sign changes and variation counts. It aligns with the intuitive idea that zero points serve as "neutral" elements in the calculation of variation.

### Dependencies
- Theorems:
  - `VARIATION_SUBSET`: States that removing points where a function vanishes doesn't change the variation
  - `VARIATION_SPLIT`: Allows splitting the variation of a function across a partition of points

### Porting notes
When implementing this in other systems:
- The set operations and interval notation might need careful translation
- The variation function may need to be defined first with its appropriate properties
- Make sure the system correctly handles the proper treatment of zero values in the function

---

## VARIATION_OFFSET

### VARIATION_OFFSET
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem (proved using `prove`)

### Formal Content
```ocaml
let VARIATION_OFFSET = prove
 (`!p m n a. variation(m+p..n+p) a = variation(m..n) (\i. a(i + p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[variation] THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN MAP_EVERY EXISTS_TAC
   [`\(i:num,j). i - p,j - p`; `\(i:num,j). i + p,j + p`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[VARIATION_SET_FINITE; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `y < &0 ==> x = y ==> x < &0`)) THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i - p:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;
```

### Informal statement
For all functions $a$, and natural numbers $p$, $m$, and $n$, the variation of $a$ in the segment $[m+p, n+p]$ equals the variation of the function $i \mapsto a(i+p)$ in the segment $[m, n]$. Formally:

$$\forall p,m,n,a.\ \text{variation}(m+p..n+p)\ a = \text{variation}(m..n)\ (\lambda i.\ a(i+p))$$

### Informal proof
The proof shows that shifting the domain of a function by $p$ doesn't affect its variation count:

1. The theorem is first rewritten using the definition of `variation`.

2. To establish equality between the cardinalities of two sets, we use `BIJECTIONS_CARD_EQ`, which states that if there exists a bijection between two sets, then their cardinalities are equal.

3. We provide two mapping functions that establish the bijection:
   - From $(m+p..n+p) \times (m+p..n+p)$ to $(m..n) \times (m..n)$: $(i,j) \mapsto (i-p, j-p)$
   - From $(m..n) \times (m..n)$ to $(m+p..n+p) \times (m+p..n+p)$: $(i,j) \mapsto (i+p, j+p)$

4. We then prove that for corresponding pairs in these sets:
   - $a(i) \cdot a(j) < 0$ if and only if $a(i+p) \cdot a(j+p) < 0$
   - This is justified by the real arithmetic fact that if $y < 0$ and $x = y$, then $x < 0$

5. Various arithmetic simplifications are used to handle the indexing relationships.

### Mathematical insight
This theorem demonstrates an important invariance property of the variation function: shifting the domain of a function by a constant offset does not affect its variation count. This makes intuitive sense because the variation counts sign changes, and shifting the domain doesn't introduce or remove any sign changes.

This result is useful for normalizing intervals when working with variations, allowing us to reduce problems on arbitrary intervals to ones starting at a convenient point (like 0).

### Dependencies
- **Definitions**:
  - `variation`: Counts the variation (number of sign changes) of a function over a discrete interval
  - `variation_set`: The set of pairs where the function values have opposite signs

- **Theorems**:
  - `BIJECTIONS_CARD_EQ`: If there exists a bijection between two finite sets, their cardinalities are equal
  - `VARIATION_SET_FINITE`: The variation set for a function over a numeric segment is finite
  - `FINITE_NUMSEG`: Numeric segments are finite sets
  - Various arithmetic and logical theorems for manipulating the indices

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition of variation (sign changes) that matches HOL Light's
2. The proof relies on constructing explicit bijections between index sets, which should translate straightforwardly to most proof assistants
3. The arithmetic reasoning is relatively simple and should be automated in most systems

---

## ARTHAN_LEMMA

### Name of formal statement
ARTHAN_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARTHAN_LEMMA = prove
 (`!n a b.
        ~(a n = &0) /\ (b n = &0) /\ (!m. sum(0..m) a = b m)
        ==> ?d. ODD d /\ variation (0..n) a = variation (0..n) b + d`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 2 <= n`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `1` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. 1 < p /\ p <= n /\ ~(a p = &0)` MP_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `2 <= n ==> 1 < n`; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ c /\ ~d) <=> a /\ b /\ c ==> d`] THEN
    STRIP_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN(MP_TAC o SPECL
   [`(\i. if i + 1 = 1 then a 0 + a 1 else a(i + 1)):num->real`;
    `(\i. b(i + 1)):num->real`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1) /\ n - 1 + 1 = n`] THEN
  REWRITE_TAC[GSYM(SPEC `1` VARIATION_OFFSET)] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(0..m+1) a` THEN CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 <= n + 1`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUM_OFFSET] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ABBREV_TAC `a':num->real = \m. if m = 1 then a 0 + a 1 else a m` THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 <= n ==> n - 1 + 1 = n /\ n - 1 - 1 + 1 = n - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV] THEN
  SUBGOAL_THEN
   `variation (1..n) a' = variation {1,p} a' + variation (p..n) a /\
    variation (0..n) a = variation {0,1,p} a + variation (p..n) a`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
     [EXISTS_TAC `variation(1..p) a' + variation(p..n) a'`;
      EXISTS_TAC `variation(0..p) a + variation(p..n) a`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN EXPAND_TAC "a'" THEN
       REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
       BINOP_TAC THENL
        [MATCH_MP_TAC VARIATION_SUBSET; MATCH_MP_TAC VARIATION_EQ] THEN
       EXPAND_TAC "a'" THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
       REWRITE_TAC[IN_NUMSEG] THEN TRY(GEN_TAC THEN ASM_ARITH_TAC) THEN
       (CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IN_DIFF]]) THEN
       REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
       REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
       TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (INT_ARITH
   `a + b:int = c + d ==> c = (a + b) - d`)) THEN
  REWRITE_TAC[INT_ARITH `a + b:int = c + d <=> d = (a + b) - c`] THEN
  ASM_CASES_TAC `a 0 + a 1 = &0` THENL
   [SUBGOAL_THEN `!i. 0 < i /\ i < p ==> b i = &0` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `i:num`) THEN
      ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LE_0;
                   ARITH_RULE `0 < i ==> 0 + 1 <= i`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LID] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:num->real) p = a p` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
      ASM_REWRITE_TAC[REAL_EQ_ADD_RCANCEL_0] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `variation(0..n) b = variation {0,p} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..p) b + variation(p..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `p:num`) THEN
        SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `~(ap = &0) ==> s = &0 ==> ~(s + ap = &0)`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        BINOP_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
        MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        (CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC];
    SUBGOAL_THEN `variation(0..n) b = variation {0,1} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..1) b + variation(1..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `1`) THEN
        SIMP_TAC[SUM_CLAUSES_NUMSEG; num_CONV `1`] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        ARITH_TAC];
      SUBGOAL_THEN `(b:num->real) 1 = a 0 + a 1` ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC]]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  ASM_SIMP_TAC[VARIATION_3; ARITH; OPPOSITE_SIGNS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS; REAL_LT_REFL] THEN
  EXPAND_TAC "a'" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < p ==> ~(p = 1)`; REAL_LT_REFL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(BINDER_CONV(RAND_CONV(RAND_CONV INT_POLY_CONV))) THEN
  REWRITE_TAC[INT_ARITH `x:int = y + --z <=> x + z = y`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[ODD_ADD; ARITH_ODD; ARITH_EVEN] THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
Let $n$ be a natural number, and let $a$ and $b$ be sequences of real numbers. If:
1. $a(n) \neq 0$
2. $b(n) = 0$
3. For all $m$, $\sum_{i=0}^m a(i) = b(m)$

Then there exists an odd number $d$ such that:
$$\text{variation}(0..n)(a) = \text{variation}(0..n)(b) + d$$

Where $\text{variation}(0..n)(f)$ counts the number of sign changes in the sequence $f(0), f(1), \ldots, f(n)$.

### Informal proof
The proof proceeds by well-founded induction on $n$.

* **Base case**: $n = 0$
  - This case is contradictory since we have $a(0) \neq 0$ and $\sum_{i=0}^0 a(i) = b(0) = 0$, which implies $a(0) = 0$.

* **Case**: $n = 1$
  - In this case, we have $a(0) + a(1) = b(1) = 0$ and $a(1) \neq 0$.
  - We take $d = 1$ (which is odd).
  - The variation in $a$ on $\{0,1\}$ is 1 because $a(0)$ and $a(1)$ have opposite signs.
  - The variation in $b$ on $\{0,1\}$ is 0 because $b(1) = 0$ and $b(0) = a(0) \neq 0$.
  - Thus, $\text{variation}(0..1)(a) = \text{variation}(0..1)(b) + 1$, as required.

* **Case**: $n \geq 2$
  - Let $p$ be the least number such that $1 < p \leq n$ and $a(p) \neq 0$.
  - Apply the induction hypothesis to $n-1$ with modified sequences:
    - $a'(i) = \begin{cases} a(0) + a(1) &\text{if}~i = 1 \\ a(i+1) &\text{otherwise} \end{cases}$
    - $b'(i) = b(i+1)$
  - Note that $a'(n-1) = a(n) \neq 0$ and $b'(n-1) = b(n) = 0$.
  - We verify that $\sum_{i=0}^m a'(i) = b'(m)$ for all $m$.
  
  - Now we analyze the variation:
    - $\text{variation}(1..n)(a') = \text{variation}(\{1,p\})(a') + \text{variation}(p..n)(a)$
    - $\text{variation}(0..n)(a) = \text{variation}(\{0,1,p\})(a) + \text{variation}(p..n)(a)$
  
  - Two subcases arise depending on whether $a(0) + a(1) = 0$:
    
    1. If $a(0) + a(1) = 0$:
       - We can show that $b(i) = 0$ for all $i$ where $0 < i < p$.
       - We deduce that $b(p) = a(p) \neq 0$.
       - The variation calculation shows that:
         $\text{variation}(0..n)(a) = \text{variation}(0..n)(b) + d$
         for some odd $d$.
    
    2. If $a(0) + a(1) \neq 0$:
       - We show that $b(1) = a(0) + a(1)$.
       - The variation calculation again yields:
         $\text{variation}(0..n)(a) = \text{variation}(0..n)(b) + d$
         for some odd $d$.

* In all cases, we find an odd number $d$ satisfying the claim.

### Mathematical insight
This lemma is a crucial part of Sturm's theorem, which counts real roots of polynomials using sign variations. The result establishes a relationship between the sign variations in a sequence and the sign variations in its partial sums.

The key insight is that when we have a sequence $a$ whose partial sums form sequence $b$, there is a well-defined relationship between their sign variations. Specifically, they differ by an odd number.

This is important because in applications of Sturm's theorem, sequences of polynomial evaluations are analyzed for their sign variations. The lemma helps establish that these variations behave in a predictable way that can be used to count roots.

### Dependencies
- `variation`: Function that counts sign changes in a sequence
- `opposite_signs`: Predicate indicating that two real numbers have opposite signs
- `num_WF`: Well-founded induction principle for natural numbers

### Porting notes
When porting this theorem:
- Ensure the definition of `variation` correctly counts sign changes in a sequence (ignoring zeros)
- The proof uses well-founded induction, which might require different implementation in other proof assistants
- The case analysis is quite detailed, with several subcases that need careful attention
- The handling of sequences and subsections of sequences (using interval notation) might require different approaches in other systems

---

## VARIATION_OPPOSITE_ENDS

### Name of formal statement
VARIATION_OPPOSITE_ENDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_OPPOSITE_ENDS = prove
 (`!a m n.
    m <= n /\ ~(a m = &0) /\ ~(a n = &0)
    ==> (ODD(variation(m..n) a) <=> a m * a n < &0)`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `n - m:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i:num. m < i /\ i < n ==> a i = &0` THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ODD(variation {m,n} a)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG; IN_DIFF; EMPTY_SUBSET] THEN
      REWRITE_TAC[LE_REFL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[VARIATION_2] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ARITH]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
        MP_TAC(SPECL [`n:num`; `p:num`] th) THEN
        MP_TAC(SPECL [`p:num`; `m:num`] th)) THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ODD(variation(m..p) a + variation(p..n) a)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN
      ASM_SIMP_TAC[LT_IMP_LE; IN_NUMSEG];
      ASM_REWRITE_TAC[ODD_ADD; OPPOSITE_SIGNS] THEN ASM_REAL_ARITH_TAC]]);;
```

### Informal statement
For all real-valued functions $a$ and natural numbers $m, n$ with $m \leq n$, if $a(m) \neq 0$ and $a(n) \neq 0$, then the number of sign variations in the sequence $\{a(m), a(m+1), \ldots, a(n)\}$ is odd if and only if $a(m) \cdot a(n) < 0$ (i.e., the endpoints have opposite signs).

### Informal proof
The proof proceeds by well-founded induction on $n-m$:

- Base case: When $n-m$ is minimal (i.e., when $m=n$ or $m+1=n$), the result follows directly.

- Inductive step: Assume the theorem holds for all cases with smaller differences than $n-m$.

The proof then considers two cases:

1. **Case 1**: If all points in between $m$ and $n$ have zero values, i.e., $a(i) = 0$ for all $i$ with $m < i < n$:
   - Then the variation count is equivalent to the variation of just the set $\{m,n\}$
   - By `VARIATION_2`, this count is odd if and only if $a(m)$ and $a(n)$ have opposite signs.

2. **Case 2**: If there exists some $p$ where $m < p < n$ with $a(p) \neq 0$:
   - Apply the induction hypothesis to the subintervals $[m,p]$ and $[p,n]$
   - By `VARIATION_SPLIT_NUMSEG`, the variation over $[m,n]$ equals the sum of variations over $[m,p]$ and $[p,n]$
   - The number of variations is odd if and only if exactly one of these subintervals has an odd number of variations
   - By the induction hypothesis, this occurs when exactly one of the pairs $(a(m),a(p))$ and $(a(p),a(n))$ has opposite signs
   - This is equivalent to $a(m)$ and $a(n)$ having opposite signs.

### Mathematical insight
This theorem provides a fundamental characterization of sign variations in a sequence of real numbers, connecting the parity of variations to the relationship between endpoint values. It generalizes Descartes' rule of signs and is particularly useful in polynomial root finding and stability analysis. The key insight is that when traversing from one endpoint to another, an odd number of sign changes means the endpoints must have opposite signs.

The result can be used in algorithms that need to count sign changes or find roots of continuous functions, as it provides a simple test based only on endpoint values to determine the parity of sign variations.

### Dependencies
- `VARIATION_SUBSET`: Relates variations of a function on different sets
- `VARIATION_2`: Characterizes the variation of a function on a two-element set
- `VARIATION_SPLIT_NUMSEG`: Shows how variation over an interval can be split into variations over subintervals
- `ODD_ADD`: Relates the oddness of a sum to the oddness of its terms
- `OPPOSITE_SIGNS`: Characterizes when two real numbers have opposite signs

### Porting notes
When porting this theorem:
- Ensure the supporting theorems about variations are ported first
- The numeric interval notation `m..n` in HOL Light represents the set $\{m, m+1, \ldots, n\}$
- The proof uses well-founded induction, which might need different tactics in other proof assistants
- The concept of "variation" may be defined differently in different systems, so check the exact definition being used

---

## REAL_POLYFUN_SGN_AT_INFINITY

### REAL_POLYFUN_SGN_AT_INFINITY
- REAL_POLYFUN_SGN_AT_INFINITY

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_POLYFUN_SGN_AT_INFINITY = prove
 (`!a n. ~(a n = &0)
         ==> ?B. &0 < B /\
                 !x. B <= abs x
                     ==> real_sgn(sum(0..n) (\i. a i * x pow i)) =
                         real_sgn(a n * x pow n)`,
  let lemma = prove
   (`abs(x) < abs(y) ==> real_sgn(x + y) = real_sgn y`,
    REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; SUM_SING_NUMSEG];
    ALL_TAC] THEN
  ABBREV_TAC `B = sum (0..n-1) (\i. abs(a i)) / abs(a n)` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; SUM_POS_LE_NUMSEG];
    ALL_TAC] THEN
  EXISTS_TAC `&1 + B` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN MATCH_MP_TAC lemma THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum(0..n-1) (\i. abs(a i)) * abs x pow (n - 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(x:real) pow n = x * x pow (n - 1)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]]]);;
```

### Informal statement
For any polynomial $\sum_{i=0}^{n} a_i x^i$ with $a_n \neq 0$, there exists a positive real number $B$ such that for all $x$ with $|x| \geq B$, the sign of the polynomial equals the sign of its leading term $a_n x^n$. 

Formally, for all coefficients $a$ and degree $n$, if $a_n \neq 0$, then there exists $B > 0$ such that for all $x$ with $|x| \geq B$:
$$\text{sgn}\left(\sum_{i=0}^{n} a_i x^i\right) = \text{sgn}(a_n x^n)$$

### Informal proof
The proof shows that for sufficiently large values of $|x|$, the leading term of the polynomial dominates all other terms, determining the sign of the entire polynomial.

First, a lemma is established: if $|x| < |y|$, then $\text{sgn}(x + y) = \text{sgn}(y)$.

The main proof proceeds as follows:

* For the base case $n = 0$, the polynomial is just a constant $a_0$, so we can choose $B = 1$, and the statement is trivially true.

* For $n > 0$, we define $B = \frac{\sum_{i=0}^{n-1} |a_i|}{|a_n|}$.

* We first show that $B \geq 0$ since it's a ratio of non-negative terms.

* We choose the bound as $1 + B$ to ensure it's positive.

* For any $x$ with $|x| \geq 1 + B$, we split the polynomial sum at the last term:
  $$\sum_{i=0}^{n} a_i x^i = \sum_{i=0}^{n-1} a_i x^i + a_n x^n$$

* We show that $|\sum_{i=0}^{n-1} a_i x^i| < |a_n x^n|$, which means that the sign of the polynomial equals the sign of its leading term.

* This is done by showing that:
  $$\left|\sum_{i=0}^{n-1} a_i x^i\right| \leq \sum_{i=0}^{n-1} |a_i| \cdot |x|^i \leq \sum_{i=0}^{n-1} |a_i| \cdot |x|^{n-1} = \left(\sum_{i=0}^{n-1} |a_i|\right) \cdot |x|^{n-1}$$

* Then, comparing with the absolute value of the leading term:
  $$|a_n x^n| = |a_n| \cdot |x|^n = |a_n| \cdot |x| \cdot |x|^{n-1}$$

* Given that $|x| \geq 1 + B$, we have $|x| \cdot |a_n| > \sum_{i=0}^{n-1} |a_i|$, which completes the proof.

### Mathematical insight
This theorem establishes a fundamental property of polynomials: for sufficiently large absolute values of the input, the sign of a polynomial is determined by its leading term. This is intuitive because as $|x|$ grows, the term with the highest power dominates all other terms.

This result is crucial for analyzing polynomial behavior "at infinity" and is essential for understanding the asymptotic behavior of polynomial functions. It's also a key component in real algebraic geometry and when studying the number and location of polynomial roots.

The theorem is particularly important when analyzing polynomial sign changes, which relate to the number of real roots (as mentioned in the comment about polynomials with odd variation having at least one positive root).

### Dependencies
No explicit dependencies were provided in the input.

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined notion of real polynomials and sign function.
2. The proof relies heavily on algebraic manipulation and inequality reasoning, which might require different tactics in other proof assistants.
3. The bound construction $B = \frac{\sum_{i=0}^{n-1} |a_i|}{|a_n|}$ is critical to the proof and should be preserved.

---

## REAL_POLYFUN_HAS_POSITIVE_ROOT

### Name of formal statement
REAL_POLYFUN_HAS_POSITIVE_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_POLYFUN_HAS_POSITIVE_ROOT = prove
 (`!a n. a 0 < &0 /\ &0 < a n
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x. &0 < x /\ &0 <= sum(0..n) (\i. a i * x pow i)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:num->real`; `n:num`] REAL_POLYFUN_SGN_AT_INFINITY) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `real_sgn(a n * x pow n) = &1` SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_SGN_EQ; REAL_LT_MUL; REAL_POW_LT; real_gt] THEN
    REWRITE_TAC[REAL_LT_IMP_LE];
    MP_TAC(ISPECL [`\x. sum(0..n) (\i. a i * x pow i)`;
                   `&0`; `x:real`; `&0`] REAL_IVT_INCREASING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL;
                 REAL_POW_ZERO; COND_RAND] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real` THEN
      SIMP_TAC[REAL_LT_LE] THEN ASM_CASES_TAC `y:real = &0` THEN
      ASM_SIMP_TAC[REAL_POW_ZERO; COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN ASM_REAL_ARITH_TAC]]);;
```

### Informal statement
For any sequence of real coefficients $a_0, a_1, \ldots, a_n$ where $a_0 < 0$ and $a_n > 0$, there exists a positive real number $x > 0$ such that the polynomial $\sum_{i=0}^n a_i x^i = 0$.

### Informal proof
We need to show that for a polynomial with negative constant term ($a_0 < 0$) and positive leading coefficient ($a_n > 0$), there exists a positive root.

The proof proceeds in two main steps:

* First, we prove that there exists some positive $x$ such that the polynomial value at $x$ is non-negative:
  * We invoke `REAL_POLYFUN_SGN_AT_INFINITY` which ensures that for sufficiently large positive values of $x$, the sign of the polynomial is determined by its leading term $a_n x^n$.
  * Since $a_n > 0$, for a sufficiently large $x$ the polynomial value becomes positive.
  * This is achieved through the sign analysis: the sign of $a_n \cdot x^n$ is positive (equal to $1$) when both $a_n > 0$ and $x > 0$.

* Then, we apply the Intermediate Value Theorem to find a root:
  * We know that at $x = 0$, the polynomial evaluates to $a_0$, which is negative.
  * We also know there exists some positive $x$ where the polynomial value is non-negative.
  * Since the polynomial is continuous on the interval $[0,x]$ (proven by applying continuity properties to each term), by the Intermediate Value Theorem, there must be a point $y \in [0,x]$ where the polynomial equals zero.
  * The proof ensures that this $y$ is positive by analyzing the case when $y = 0$ and showing that would lead to a contradiction, as we'd have $a_0 = 0$, which contradicts our assumption $a_0 < 0$.

### Mathematical insight
This theorem establishes the existence of a positive root for polynomials with negative constant term and positive leading coefficient. It's a specific form of Descartes' rule of signs, which more generally relates the number of sign changes in the sequence of coefficients to the number of positive real roots.

The key insight is that a polynomial with these properties must cross the x-axis at least once in the positive domain because it starts negative at $x=0$ (due to the constant term) and eventually becomes positive as $x$ grows (due to the dominant leading term).

This result is useful in various mathematical contexts, including the analysis of polynomial behavior, stability theory, and algebraic geometry.

### Dependencies
- **Theorems:**
  - `REAL_POLYFUN_SGN_AT_INFINITY`: Behavior of polynomial sign for large values
  - `REAL_IVT_INCREASING`: Intermediate Value Theorem for increasing functions
  - `REAL_CONTINUOUS_ON_SUM`: Continuity of finite sums
  - `REAL_CONTINUOUS_ON_LMUL`: Continuity of scalar multiplication
  - `REAL_CONTINUOUS_ON_POW`: Continuity of power functions
  - `REAL_CONTINUOUS_ON_ID`: Continuity of the identity function

### Porting notes
When porting this theorem:
1. Ensure your target system has a well-developed theory of polynomial functions and real analysis.
2. The key dependencies to port first include the Intermediate Value Theorem and theorems about continuity of polynomial functions.
3. The proof relies on sign analysis of polynomials for large values - ensure your target system has similar capabilities or develop them.
4. Carefully handle the conditional reasoning about the sign of polynomial evaluations at different points.

---

## ODD_VARIATION_POSITIVE_ROOT

### ODD_VARIATION_POSITIVE_ROOT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODD_VARIATION_POSITIVE_ROOT = prove
 (`!a n. ODD(variation(0..n) a)
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?M. !i. i IN 0..n /\ ~(a i = &0) ==> i <= M` MP_TAC THENL
   [EXISTS_TAC `n:num` THEN SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `?i. i IN 0..n /\ ~(a i = &0)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `((!i. P i ==> Q i) ==> F) ==> ?i. P i /\ ~Q i`) THEN
    DISCH_TAC THEN SUBGOAL_THEN `variation (0..n) a = variation {0} a`
     (fun th -> SUBST_ALL_TAC th THEN ASM_MESON_TAC[VARIATION_1; ODD]) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    ASM_SIMP_TAC[IN_DIFF] THEN REWRITE_TAC[IN_NUMSEG; SING_SUBSET; LE_0];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> a ==> a /\ b ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN REWRITE_TAC[num_MAX] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> p /\ q ==> ~r`; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p:num <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:num->real) p * a q < &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VARIATION_OPPOSITE_ENDS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `ODD p ==> p = q ==> ODD q`)) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. (a:num->real)(p + i) / a q`; `q - p:num`]
        REAL_POLYFUN_HAS_POSITIVE_ROOT) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `p:num <= q ==> p + q - p = q`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_div; OPPOSITE_SIGNS; REAL_MUL_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPPOSITE_SIGNS]) THEN
    REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; GSYM REAL_INV_NEG] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_RING
   `!a. y = a * x ==> x = &0 ==> y = &0`) THEN
  EXISTS_TAC `(a:num->real) q * x pow p` THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_ARITH
   `(aq * xp) * api / aq * xi:real = (aq / aq) * api * (xp * xi)`] THEN
  ASM_CASES_TAC `(a:num->real) q = &0` THENL
   [ASM_MESON_TAC[REAL_MUL_LZERO; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_ADD; REAL_DIV_REFL; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MP_TAC(SPEC `p:num` SUM_OFFSET) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC));;
```

### Informal statement
If a polynomial $\sum_{i=0}^n a_i x^i$ has an odd number of variations in sign in its coefficient sequence $a_0, a_1, \ldots, a_n$, then there exists a positive real number $x$ such that $\sum_{i=0}^n a_i x^i = 0$.

More precisely, for any sequence of real coefficients $a: \mathbb{N} \to \mathbb{R}$ and any natural number $n$, if the variation count of signs in the sequence $a_0, a_1, \ldots, a_n$ is odd, then there exists a positive real number $x$ such that $\sum_{i=0}^n a_i x^i = 0$.

### Informal proof
This proof establishes a special case of Descartes' rule of signs, showing that a polynomial with an odd number of sign variations must have a positive real root.

- First, we establish that there exists a maximum index $M$ such that all non-zero coefficients $a_i$ for $i \in [0,n]$ satisfy $i \leq M$. This is trivially true by taking $M = n$.

- Next, we prove there exists at least one non-zero coefficient in the sequence. If all coefficients were zero, then the variation count would be 0 (an even number), contradicting our assumption that it's odd.

- Using the well-ordering principle for natural numbers, we identify the minimum index $p$ such that $a_p \neq 0$ for $p \in [0,n]$.

- Similarly, we find some other index $q$ such that $a_q \neq 0$ and $p \leq q$.

- We show that $a_p \cdot a_q < 0$ (they have opposite signs). This follows from the fact that the variation count on $[0,n]$ is odd, and removing indices with zero coefficients doesn't change the variation count.

- We then apply a theorem about polynomial functions having positive roots (`REAL_POLYFUN_HAS_POSITIVE_ROOT`) to the normalized polynomial $\sum_{i=0}^{q-p} \frac{a_{p+i}}{a_q} x^i$. This polynomial has a negative constant term (because $\frac{a_p}{a_q} < 0$) and a positive leading coefficient ($\frac{a_q}{a_q} = 1$), so it has a positive root.

- Finally, we convert this root back to a root of our original polynomial by appropriate algebraic manipulations, showing that if $x$ is a positive root of the normalized polynomial, then $x$ is also a positive root of $\sum_{i=0}^n a_i x^i$.

### Mathematical insight
This theorem is a special case of Descartes' rule of signs, which relates the number of positive real roots of a polynomial to the number of sign variations in its coefficients. 

The full rule states that the number of positive real roots of a polynomial is either equal to the number of sign variations in its coefficients, or less than it by an even number. This theorem addresses the case where the number of variations is odd, which implies there must be at least one positive real root.

This result is important in polynomial theory and has applications in numerical methods for finding roots of polynomials, as it provides information about the existence and location of roots without explicitly computing them.

The proof technique uses clever manipulations of the polynomial to reduce to a simpler case where we can apply known results about polynomials with specific sign patterns in their coefficients.

### Dependencies
- `VARIATION_OPPOSITE_ENDS`: Relates the variation count to the signs of coefficients at the endpoints.
- `VARIATION_SUBSET`: Shows how variation count behaves under subset operations.
- `VARIATION_1`: Property of variation count for a singleton set.
- `REAL_POLYFUN_HAS_POSITIVE_ROOT`: Ensures existence of positive roots for polynomials with certain sign patterns.
- Various arithmetic and logical theorems for manipulating expressions.

### Porting notes
When porting this theorem:
1. Ensure that the destination system has a similar definition of "variation count" for coefficient sequences, which counts sign changes in non-zero terms.
2. The proof relies on well-ordering principles for natural numbers, which should be available in most theorem provers.
3. Special attention should be paid to how the normalized polynomial is constructed and how its roots relate to the original polynomial.
4. The theorem `REAL_POLYFUN_HAS_POSITIVE_ROOT` is a key dependency and may need to be ported first.

---

## multiplicity

### Name of formal statement
multiplicity

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let multiplicity = new_definition
 `multiplicity f r =
        @k. ?a n. ~(sum(0..n) (\i. a i * r pow i) = &0) /\
                  !x. f(x) = (x - r) pow k * sum(0..n) (\i. a i * x pow i)`;;
```

### Informal statement
For a function $f$ and a value $r$, the multiplicity of $r$ as a root of $f$ is defined as the natural number $k$ such that there exists a natural number $n$ and a sequence $a_0, a_1, \ldots, a_n$ where:

1. The sum $\sum_{i=0}^{n} a_i r^i \neq 0$
2. For all $x$, $f(x) = (x - r)^k \cdot \sum_{i=0}^{n} a_i x^i$

This captures the standard notion of the multiplicity of a root in a polynomial or analytic function.

### Informal proof
This is a definition, so there is no proof to translate.

### Mathematical insight
The multiplicity of a root $r$ of a function $f$ represents how many times the function can be factored by the term $(x - r)$. It is a fundamental concept in algebra and analysis:

- When $k = 0$, $r$ is not a root of $f$
- When $k = 1$, $r$ is a simple root of $f$
- When $k > 1$, $r$ is a multiple root of $f$ with multiplicity $k$

The definition uses Hilbert's epsilon operator (the `@k` notation in HOL Light) to select the unique natural number $k$ that satisfies the condition. The condition ensures that $f(x)$ can be expressed as $(x - r)^k$ multiplied by a function that doesn't vanish at $r$.

This definition is important for analyzing the behavior of functions near their roots, especially in contexts like polynomial factorization, complex analysis, and differential equations.

### Dependencies
This definition uses basic HOL Light concepts like the epsilon operator, but has no specific theorem or definition dependencies from the provided information.

### Porting notes
When porting this definition:
- Systems without the epsilon operator (`@`) will need to use an equivalent approach, such as defining a function that returns the multiplicity based on the properties given
- Ensure the ported definition handles edge cases correctly, such as when $f$ is not a polynomial
- Consider that in some systems, you might need to specify the appropriate type universes for the function $f$ and the value $r$

---

## MULTIPLICITY_UNIQUE

### MULTIPLICITY_UNIQUE
- MULTIPLICITY_UNIQUE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let MULTIPLICITY_UNIQUE = prove
 (`!f a r b m k.
        (!x. f(x) = (x - r) pow k * sum(0..m) (\j. b j * x pow j)) /\
        ~(sum(0..m) (\j. b j * r pow j) = &0)
        ==> k = multiplicity f r`,
  let lemma = prove
   (`!i j f g. f real_continuous_on (:real) /\ g real_continuous_on (:real) /\
               ~(f r = &0) /\ ~(g r = &0)
               ==> (!x. (x - r) pow i * f(x) = (x - r) pow j * g(x))
                   ==> j = i`,
    MATCH_MP_TAC WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`atreal r`; `f:real->real`;
                   `(f:real->real) r`; `&0`]
          REALLIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_ATREAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
      ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                    IN_UNIV];
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\x:real. (x - r) pow (j - i) * g x` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < abs(x - r) <=> ~(x = r)`] THEN
        X_GEN_TAC `x:real` THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_RING
         `!a. a * x = a * y /\ ~(a = &0) ==> x = y`) THEN
        EXISTS_TAC `(x - r:real) pow i` THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; REAL_POW_EQ_0] THEN
        ASM_SIMP_TAC[REAL_SUB_0; ARITH_RULE `i:num < j ==> i + j - i = j`];
        SUBST1_TAC(REAL_ARITH `&0 = &0 * (g:real->real) r`) THEN
        MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_NULL_POW THEN
          REWRITE_TAC[GSYM REALLIM_NULL; REALLIM_ATREAL_ID] THEN ASM_ARITH_TAC;
          REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
          ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                        REAL_OPEN_UNIV; IN_UNIV]]]]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[multiplicity] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For a function $f$ of the form
$$f(x) = (x - r)^k \cdot \sum_{j=0}^{m} b_j x^j$$
where the sum $\sum_{j=0}^{m} b_j r^j \neq 0$, then $k$ is the multiplicity of $f$ at $r$.

More precisely, for any real function $f$, real number $r$, natural numbers $m$ and $k$, and sequence of real coefficients $b_j$ for $j = 0,\ldots,m$, if 
$$f(x) = (x - r)^k \cdot \sum_{j=0}^{m} b_j x^j$$ 
for all $x$, and $\sum_{j=0}^{m} b_j r^j \neq 0$, then $k$ equals the multiplicity of $f$ at $r$.

### Informal proof
We want to prove that $k$ is the multiplicity of $f$ at $r$, as defined by the `multiplicity` function in HOL Light. Since multiplicity is defined using the `SELECT` operator, we need to show that $k$ is the unique value satisfying the multiplicity property.

The proof proceeds in several key steps:

1. First, a lemma is established: if $f$ and $g$ are continuous functions on $\mathbb{R}$ with $f(r) \neq 0$ and $g(r) \neq 0$, and $(x-r)^i f(x) = (x-r)^j g(x)$ for all $x$, then $i = j$.

   The lemma proof uses:
   - Without loss of generality, assume $i < j$
   - If $i < j$, then by rearranging: $f(x) = (x-r)^{j-i} g(x)$
   - This implies $f(r) = 0$ (since $j-i > 0$), contradicting our assumption

2. For the main theorem, we use the `SELECT_UNIQUE` tactic to show that $k$ is the unique value satisfying the definition of multiplicity.

3. We show that $k$ satisfies the multiplicity property by applying our lemma:
   - The function $\sum_{j=0}^{m} b_j x^j$ is continuous on $\mathbb{R}$ (shown using `REAL_CONTINUOUS_ON_SUM`, `REAL_CONTINUOUS_ON_LMUL`, `REAL_CONTINUOUS_ON_POW`, and `REAL_CONTINUOUS_ON_ID`)
   - At $r$, this function equals $\sum_{j=0}^{m} b_j r^j$ which is non-zero by assumption
   - Therefore $k$ is indeed the unique multiplicity of $f$ at $r$

The proof effectively shows that the multiplicity of a function at a point is determined by the highest power of $(x-r)$ that can be factored out while leaving a non-zero value when evaluated at $r$.

### Mathematical insight
The multiplicity of a function at a point is a fundamental concept in analysis. Intuitively, it represents how many times a function "touches" or "crosses" zero at a given point.

This theorem establishes a canonical form for functions with a known multiplicity: a function with multiplicity $k$ at point $r$ can always be written as $(x-r)^k$ times a function that is non-zero at $r$. The key insight is that this representation is unique - the exponent $k$ is precisely the multiplicity.

In the context of polynomials, this corresponds to how many times $(x-r)$ appears as a factor in the polynomial. But the theorem applies to a broader class of functions that can be expressed in the given form.

This result is important for understanding the local behavior of functions near their zeros, which has applications in numerical analysis, approximation theory, and differential equations.

### Dependencies
#### Theorems
- `REALLIM_UNIQUE`: Uniqueness of limits in real-valued functions
- `TRIVIAL_LIMIT_ATREAL`: The limit `atreal a` is not trivial
- `REALLIM_TRANSFORM_EVENTUALLY`: If two functions are eventually equal and one has a limit, so does the other
- `REALLIM_MUL`: Limit of product equals product of limits
- `REALLIM_NULL_POW`: If a function converges to zero, so does any positive power of it
- `REALLIM_ATREAL_ID`: The identity function converges to `a` at the point `a`
- `REAL_CONTINUOUS_ATREAL`: Continuity at a point is equivalent to the function converging to its value at that point
- `REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT`: For open sets, continuity on the set is equivalent to continuity at each point
- `REAL_CONTINUOUS_ON_SUM`: Finite sum of continuous functions is continuous
- `REAL_CONTINUOUS_ON_LMUL`: Scalar multiple of a continuous function is continuous
- `REAL_CONTINUOUS_ON_POW`: Power of a continuous function is continuous
- `REAL_CONTINUOUS_ON_ID`: The identity function is continuous on any set

#### Definitions
- `atreal`: Represents the neighborhood around a point in the real line
- `real_continuous_on`: Defines continuity of a real-valued function on a set

### Porting notes
When porting this theorem:
1. Ensure that your system has a well-defined concept of multiplicity
2. The proof relies on continuity properties of polynomial functions, which should be available in most proof assistants
3. The proof uses the "without loss of generality" pattern for comparing natural numbers, which may require different tactics in other systems
4. The theorem uses the SELECT operator to handle the uniqueness of multiplicity, which might need to be implemented differently in systems without this operator
5. Special attention should be paid to how limits and continuity at a point are defined in the target system

---

## MULTIPLICITY_WORKS

### Name of formal statement
MULTIPLICITY_WORKS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLICITY_WORKS = prove
 (`!r n a.
    (?i. i IN 0..n /\ ~(a i = &0))
    ==> ?b m.
        ~(sum(0..m) (\i. b i * r pow i) = &0) /\
        !x. sum(0..n) (\i. a i * x pow i) =
            (x - r) pow multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r *
            sum(0..m) (\i. b i * x pow i)`,
  REWRITE_TAC[multiplicity] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `sum(0..n) (\i. a i * r pow i) = &0` THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_TAC `sum (0..n) (\i. a i * r pow i) = &0` THEN
      ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2; SUM_SING] THEN
      REWRITE_TAC[real_pow; REAL_MUL_RID] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(GEN `x:real` (ISPECL [`a:num->real`; `x:real`; `r:real`; `n:num`]
        REAL_SUB_POLYFUN)) THEN ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN
    ABBREV_TAC `b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
     [EXISTS_TAC `n - 1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0] THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SUB_ADD; LE_1; SUM_SING_NUMSEG; real_pow; REAL_MUL_RID;
                   ARITH_RULE `n - (n - 1) - 1 = 0`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (fun th ->
        EXISTS_TAC `SUC k` THEN MP_TAC th)) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC];
    MAP_EVERY EXISTS_TAC [`0`; `a:num->real`; `n:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]]);;
```

### Informal statement
For any real number $r$, any natural number $n$, and any sequence of real coefficients $a_0, a_1, \ldots, a_n$ where at least one coefficient $a_i$ with $i \in \{0,1,\ldots,n\}$ is non-zero, there exists:
- a sequence of real numbers $b_0, b_1, \ldots, b_m$ and 
- a natural number $m$

such that:
1. $\sum_{i=0}^{m} b_i r^i \neq 0$
2. For all real $x$, the polynomial $\sum_{i=0}^{n} a_i x^i$ can be factored as:
   $\sum_{i=0}^{n} a_i x^i = (x - r)^{\text{multiplicity}(P, r)} \cdot \sum_{i=0}^{m} b_i x^i$
   
where $P(x) = \sum_{i=0}^{n} a_i x^i$ and $\text{multiplicity}(P, r)$ denotes the multiplicity of $r$ as a root of the polynomial $P$.

### Informal proof
The proof proceeds by well-founded induction on $n$.

* First, the theorem uses the definition of multiplicity, and converts the select operator using `SELECT_CONV`.

* For the induction, we consider two main cases:
  
  **Case 1**: $a_n = 0$
  * If $n = 0$, this contradicts our hypothesis that some $a_i$ is non-zero.
  * If $n > 0$, we apply the induction hypothesis to the polynomial with degree $n-1$, using the fact that if coefficient $a_n = 0$, then the polynomial is effectively of lower degree.

  **Case 2**: $a_n \neq 0$
  * Subcase 2.1: $\sum_{i=0}^{n} a_i r^i = 0$ (i.e., $r$ is a root of the polynomial)
    * If $n = 0$, this leads to a contradiction with our assumption $a_0 \neq 0$.
    * If $n > 0$, we apply the polynomial division factorization:
      $\sum_{i=0}^{n} a_i x^i = (x - r) \cdot \sum_{j=0}^{n-1} b_j x^j$
      where $b_j$ is defined as $\sum_{i=j+1}^{n} a_i r^{i-j-1}$.
    * Then we apply the induction hypothesis to the quotient polynomial (with coefficients $b_j$) to get the result.

  * Subcase 2.2: $\sum_{i=0}^{n} a_i r^i \neq 0$ (i.e., $r$ is not a root)
    * Take $m = n$, $b_i = a_i$, and the multiplicity of $r$ is 0, which gives the desired result directly.

### Mathematical insight
This theorem formalizes a fundamental result in polynomial algebra: any polynomial can be factored as $(x - r)^k \cdot Q(x)$ where $k$ is the multiplicity of $r$ as a root and $Q(r) \neq 0$. 

The multiplicity of a root $r$ represents how many times the factor $(x - r)$ appears in the polynomial factorization. The theorem shows that after factoring out all instances of $(x - r)$, the remaining polynomial $\sum_{i=0}^{m} b_i x^i$ does not vanish at $x = r$.

This result is important because:
1. It confirms that the concept of multiplicity is well-defined for polynomials
2. It provides a constructive way to decompose a polynomial in terms of its roots
3. It forms the basis for polynomial factorization and root-finding algorithms

### Dependencies
None explicitly provided in the input.

### Porting notes
When porting this theorem:
- Ensure that the `multiplicity` function is properly defined in the target system
- The proof relies heavily on polynomial manipulation lemmas (like `REAL_SUB_POLYFUN`), which need to be available
- The recursive structure involving polynomial division might need different tactics in other proof assistants
- Well-founded induction on natural numbers (`num_WF`) will need a corresponding construct in the target system

---

## MULTIPLICITY_OTHER_ROOT

### Name of formal statement
MULTIPLICITY_OTHER_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLICITY_OTHER_ROOT = prove
 (`!a n r s.
    ~(r = s) /\ (?i. i IN 0..n /\ ~(a i = &0))
     ==> multiplicity (\x. (x - r) pow m * sum(0..n) (\i. a i * x pow i)) s =
         multiplicity (\x.  sum(0..n) (\i. a i * x pow i)) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real`; `n:num`; `a:num->real`]
        MULTIPLICITY_WORKS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `p:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `?b q. !x. sum(0..q) (\j. b j * x pow j) =
              (x - r) pow m * sum (0..p) (\i. c i * x pow i)`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_RING `r * x = s * r * y <=> r = &0 \/ s * y = x`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0]] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`c:num->real`; `p:num`; `m:num`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [MAP_EVERY EXISTS_TAC [`c:num->real`; `p:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `c:num->real`]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `n:num`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  EXISTS_TAC `\i. (if 0 < i then a(i - 1) else &0) -
                  (if i <= n then r * a i else &0)` THEN
  EXISTS_TAC `n + 1` THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN X_GEN_TAC `x:real` THEN
  BINOP_TAC THENL
   [MP_TAC(ARITH_RULE `0 <= n + 1`) THEN SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[SUM_OFFSET; LT_REFL] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; ARITH_RULE `0 < i + 1`] THEN
    REWRITE_TAC[GSYM SUM_LMUL; ADD_SUB; REAL_POW_ADD; REAL_POW_1];
    SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; ARITH_RULE `0 < n + 1`] THEN
    REWRITE_TAC[ADD_SUB; ARITH_RULE `~(n + 1 <= n)`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM SUM_LMUL]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
Let $a$ be a sequence of real numbers indexed by naturals, let $n$ be a natural number, and let $r$ and $s$ be distinct real numbers. If there exists an index $i \in \{0, 1, \ldots, n\}$ such that $a_i \neq 0$, then the multiplicity of $s$ as a root of the function $f(x) = (x - r)^m \cdot \sum_{i=0}^{n} a_i x^i$ equals the multiplicity of $s$ as a root of the polynomial $g(x) = \sum_{i=0}^{n} a_i x^i$.

### Informal proof
The proof demonstrates that multiplying a polynomial by a power of $(x - r)$ does not affect the multiplicity of roots at any point $s \neq r$.

* We begin by applying `MULTIPLICITY_UNIQUE` to establish that we need to show the two functions have the same behavior near $s$.

* We use `MULTIPLICITY_WORKS` to represent the second polynomial $\sum_{i=0}^{n} a_i x^i$ in the form $\sum_{i=0}^{p} c_i x^i$ where $c_0 \neq 0$ and the multiplicity of $s$ is captured.

* The main part of the proof proceeds by induction on $m$ (the power of $(x-r)$):
  - Base case ($m = 0$): When $m = 0$, $(x-r)^m = 1$, so the functions are identical.
  - Inductive step: Assuming the result holds for $m$, we prove it for $m+1$.

* For the inductive step, we construct a polynomial sequence $b$ such that:
  $\sum_{j=0}^{q} b_j x^j = (x-r)^{m+1} \cdot \sum_{i=0}^{p} c_i x^i$

* We define $b_i$ carefully to handle the multiplication by $(x-r)$:
  $b_i = \begin{cases} 
    a_{i-1} - r \cdot a_i & \text{if } 0 < i \leq n \\
    -r \cdot a_0 & \text{if } i = 0 \\
    a_n & \text{if } i = n+1 \\
    0 & \text{otherwise}
  \end{cases}$

* By algebraic manipulation and properties of summation, we verify that this construction satisfies our requirement, completing the induction.

### Mathematical insight
This theorem establishes that multiplying a polynomial by a power of $(x-r)$ doesn't affect the multiplicity of roots at any other point $s \neq r$. This is an important property in polynomial theory and root finding. 

The result is intuitive: if we multiply a polynomial by $(x-r)^m$, we're adding a root of multiplicity $m$ at $x=r$, but not changing the behavior of the polynomial at other points. The theorem formalizes this intuition and provides a precise statement about root multiplicities.

This result is particularly useful in polynomial factorization and when analyzing the behavior of rational functions, as it allows us to separate the analysis of different roots.

### Dependencies
#### Theorems
- `MULTIPLICITY_UNIQUE` - establishes when two functions have the same multiplicity at a point
- `MULTIPLICITY_WORKS` - provides a canonical form for a polynomial based on its root multiplicity

### Porting notes
When porting this theorem:
1. Ensure that the definition of root multiplicity in your target system matches HOL Light's definition.
2. The proof relies on algebraic manipulation of polynomials and summations, which should be available in most proof assistants.
3. The construction of the polynomial sequence in the inductive step may need careful handling, depending on how polynomials are represented in your target system.

---

## VARIATION_POSITIVE_ROOT_FACTOR

### VARIATION_POSITIVE_ROOT_FACTOR
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_FACTOR = prove
 (`!a n r.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b. ~(b(n - 1) = &0) /\
            (!x. sum(0..n) (\i. a i * x pow i) =
                 (x - r) * sum(0..n-1) (\i. b i * x pow i)) /\
            ?d. ODD d /\ variation(0..n) a = variation(0..n-1) b + d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `b = \j. sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
  EXISTS_TAC `b:num->real` THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; ARITH_RULE `n - (n - 1) - 1 = 0`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_RID];
    MP_TAC(GEN `x:real` (SPECL [`a:num->real`; `x:real`; `r:real`; `n:num`]
        REAL_SUB_POLYFUN)) THEN
    ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:num->real) n = &0` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `\i. if i <= n then a i * (r:real) pow i else &0`;
    `\i. if i <= n then --b i * (r:real) pow (i + 1) else &0`]
   ARTHAN_LEMMA) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_LT_IMP_NZ; REAL_NEG_0;
               LE_REFL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:num <= n` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `!i:num. i <= j ==> i <= n` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
      REWRITE_TAC[REAL_ARITH `a:real = --b * c <=> a + b * c = &0`] THEN
      REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[ARITH_RULE `j + 1 <= k ==> k - j - 1 + j + 1 = k`] THEN
      ASM_SIMP_TAC[SUM_COMBINE_R; LE_0];
      REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE
      `~(j <= n) ==> ((0 <= i /\ i <= j) /\ i <= n <=> 0 <= i /\ i <= n)`] THEN
      ASM_REWRITE_TAC[GSYM numseg]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `x':num = x /\ y' = y ==> x' = y' + d ==> x = y + d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. a i * r pow i)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n-1) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
        CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
        SUBGOAL_THEN `i:num = n` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ALL_TAC]] THEN
    REWRITE_TAC[variation] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `(a * x) * (b * x'):real = (x * x') * a * b`] THEN
    SIMP_TAC[NOT_IMP; GSYM CONJ_ASSOC; GSYM REAL_POW_ADD;
             REAL_ARITH `--x * --y:real = x * y`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_POW_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_RNEG; REAL_ENTIRE; REAL_NEG_EQ_0; REAL_POW_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;
```

### Informal statement
For any real polynomial $\sum_{i=0}^n a_i x^i$ with $a_n \neq 0$ that has a positive root $r > 0$ (i.e., $\sum_{i=0}^n a_i r^i = 0$), there exists a polynomial $\sum_{i=0}^{n-1} b_i x^i$ with $b_{n-1} \neq 0$ such that:

1. $\sum_{i=0}^n a_i x^i = (x - r) \cdot \sum_{i=0}^{n-1} b_i x^i$ for all $x$
2. There exists an odd number $d$ where the variation in sign sequences satisfies: $\text{variation}_{0..n}(a) = \text{variation}_{0..n-1}(b) + d$

### Informal proof
The proof establishes how the number of sign variations changes when factoring out a positive root from a polynomial. The proof proceeds as follows:

* First handle the trivial case when $n = 0$: this leads to a contradiction since we would have $a_0 \cdot r^0 = a_0 = 0$, which contradicts our assumption that $a_n \neq 0$.

* For $n > 0$, define the coefficients $b_j$ of the quotient polynomial as:
  $b_j = \sum_{i=j+1}^{n} a_i \cdot r^{i-j-1}$

* We verify that $b_{n-1} \neq 0$ by showing it equals $a_n$, which is non-zero by assumption.

* Next, we confirm that the polynomial factorization holds:
  $\sum_{i=0}^n a_i x^i = (x - r) \cdot \sum_{i=0}^{n-1} b_i x^i$
  This is justified by applying the polynomial division theorem.

* We note that $b_n = 0$ by definition, since the summation is empty.

* The proof then applies Arthan's lemma to compare the sign variations between the original polynomial and the quotient polynomial.

* We show that the sequence $a_i \cdot r^i$ has the same sign variations as $a_i$, and the sequence $-b_i \cdot r^{i+1}$ has the same sign variations as $b_i$.

* The theorem is completed by demonstrating that the difference in sign variations is odd, which follows from the properties of sign variations when factoring out a positive root.

### Mathematical insight
This theorem is an important step in proving Descartes' Rule of Signs, which relates the number of positive real roots of a polynomial to the number of sign variations in its coefficients. 

The key insight is that when a polynomial has a positive root $r$, factoring out $(x-r)$ changes the number of sign variations in a predictable way - specifically, the sign variations decrease by an odd number. This is crucial because it leads to the conclusion that the number of positive roots of a polynomial is bounded by the number of sign variations in its coefficients, and they differ by an even number.

This result thus forms part of the mathematical foundation for analyzing the location of polynomial roots, which has applications in numerous areas including numerical analysis, control theory, and computational geometry.

### Dependencies
- `REAL_SUB_POLYFUN`: Used to establish the polynomial division relationship
- `ARTHAN_LEMMA`: Key lemma that relates sign variations between polynomials
- `VARIATION_EQ`: Used to show equality of variations under certain transformations
- `VARIATION_SUBSET`: Used to relate variations over different domains
- `variation`: The definition of sign variations in a sequence

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-defined notion of sign variations in a sequence
2. The polynomial division theorem (REAL_SUB_POLYFUN) needs to be available
3. Special attention should be paid to how polynomial functions are represented in the target system
4. Arthan's lemma is a specialized result that may need to be proven separately in the target system

---

## VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR

### Name of formal statement
VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b k m. 0 < k /\ m < n /\ ~(b m = &0) /\
                (!x. sum(0..n) (\i. a i * x pow i) =
                     (x - r) pow k * sum(0..m) (\i. b i * x pow i)) /\
                ~(sum(0..m) (\j. b j * r pow j) = &0) /\
                ?d. EVEN d /\ variation(0..n) a = variation(0..m) b + k + d`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:num->real`; `n:num`; `r:real`]
        VARIATION_POSITIVE_ROOT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:num->real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `sum(0..n-1) (\i. c i * r pow i) = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `c:num->real`)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_ASSOC] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[ADD1; ADD_ASSOC] THEN EXISTS_TAC `d - 1 + e`;
    MAP_EVERY EXISTS_TAC [`c:num->real`; `1`; `n - 1`] THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    EXISTS_TAC `d - 1`] THEN
  UNDISCH_TAC `ODD d` THEN GEN_REWRITE_TAC LAND_CONV [ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[SUC_SUB1; EVEN_ADD; EVEN_MULT; ARITH] THEN ARITH_TAC);;
```

### Informal statement
For any positive real number $r$, any natural number $n$, and any sequence $a_0, a_1, \ldots, a_n$ of real numbers such that:
- $a_n \neq 0$
- $\sum_{i=0}^n a_i \cdot r^i = 0$

There exist a natural number $k > 0$, a natural number $m < n$, and a sequence $b_0, b_1, \ldots, b_m$ of real numbers such that:
1. $b_m \neq 0$
2. For all real $x$, $\sum_{i=0}^n a_i \cdot x^i = (x - r)^k \cdot \sum_{i=0}^m b_i \cdot x^i$
3. $\sum_{j=0}^m b_j \cdot r^j \neq 0$
4. There exists an even number $d$ such that $\text{variation}(0..n, a) = \text{variation}(0..m, b) + k + d$

where $\text{variation}(0..n, a)$ refers to the number of sign variations in the sequence $a_0, a_1, \ldots, a_n$.

### Informal proof
This theorem is proven by well-founded induction on the natural number $n$:

* For the base case $n = 0$, we have $a_0 \cdot r^0 = a_0 = 0$, which contradicts our assumption that $a_n \neq 0$ (since $n=0$).

* For the inductive case, we apply the theorem `VARIATION_POSITIVE_ROOT_FACTOR` to our polynomial $\sum_{i=0}^n a_i \cdot x^i$ with the root $r$, which gives us a sequence $c_0, c_1, \ldots, c_{n-1}$ such that:
  - For all real $x$, $\sum_{i=0}^n a_i \cdot x^i = (x - r) \cdot \sum_{i=0}^{n-1} c_i \cdot x^i$
  - There exists an odd number $d$ such that $\text{variation}(0..n, a) = \text{variation}(0..n-1, c) + d$

  We then consider two cases:
  
  1. If $\sum_{i=0}^{n-1} c_i \cdot r^i = 0$:
     - We apply the induction hypothesis to $c$ and $n-1$, obtaining a sequence $b_0, b_1, \ldots, b_m$ and a number $k > 0$ such that all the required properties hold for $c$ and $n-1$.
     - We then set the new $k$ to be $k+1$ and use the fact that $(x-r)^{k+1} = (x-r) \cdot (x-r)^k$ to establish the equation for our original polynomial.
     - For the variation count, we use $d-1+e$ (where $e$ is the even number from the induction hypothesis) as our even number, making the equation balanced.
  
  2. If $\sum_{i=0}^{n-1} c_i \cdot r^i \neq 0$:
     - We set $b = c$, $k = 1$, and $m = n-1$.
     - Since $d$ is odd, we can write $d = 2p+1$ for some $p$, making $d-1 = 2p$ even.
     - This directly satisfies all the required properties.

### Mathematical insight
This theorem extends the fundamental theorem of algebra by providing a more detailed analysis of polynomials with a positive root. It decomposes a polynomial with a root at $r$ into a factor of $(x-r)^k$ multiplied by another polynomial that does not vanish at $r$. 

The key insight is the connection between this factorization and the variation of signs in the coefficient sequences. The theorem establishes that the number of sign variations in the original polynomial coefficients equals the number of sign variations in the reduced polynomial plus the multiplicity of the root plus an even number.

This result is part of a broader framework related to Descartes' rule of signs, which bounds the number of positive real roots of a polynomial based on sign variations in its coefficients. This theorem helps refine that analysis when we know a specific positive root exists.

### Dependencies
No explicit dependencies provided in the input.

### Porting notes
When implementing this in other systems, special attention should be given to:
1. The definition of the `variation` function, which counts sign changes in a sequence
2. Representing polynomial operations, especially polynomial factorization
3. The well-founded induction principle used in the proof

This theorem uses the theorem `VARIATION_POSITIVE_ROOT_FACTOR` which should be ported first, as it handles the single-factor case of this more general multiple-factor theorem.

---

## VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR

### Name of formal statement
VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b m. m < n /\ ~(b m = &0) /\
              (!x. sum(0..n) (\i. a i * x pow i) =
                   (x - r) pow
                   (multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r) *
                   sum(0..m) (\i. b i * x pow i)) /\
              ~(sum(0..m) (\j. b j * r pow j) = &0) /\
              ?d. EVEN d /\
                  variation(0..n) a = variation(0..m) b +
                     multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r + d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r = k`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
Let $r > 0$ be a positive real number, $n$ be a natural number, and $a$ be a sequence of real numbers indexed from $0$ to $n$ such that $a_n \neq 0$ and $\sum_{i=0}^{n} a_i r^i = 0$. Then there exists a sequence $b$ of real numbers and a natural number $m < n$ such that:

1. $b_m \neq 0$
2. For all real $x$, $\sum_{i=0}^{n} a_i x^i = (x - r)^k \cdot \sum_{i=0}^{m} b_i x^i$, where $k$ is the multiplicity of $r$ as a root of the polynomial $\sum_{i=0}^{n} a_i x^i$
3. $\sum_{j=0}^{m} b_j r^j \neq 0$
4. There exists an even number $d$ such that $\text{variation}(0..n, a) = \text{variation}(0..m, b) + k + d$

Where $\text{variation}(0..n, a)$ represents the number of sign changes in the sequence $a_0, a_1, \ldots, a_n$.

### Informal proof
This theorem is proven by leveraging the result of `VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR`. The proof follows these steps:

* We apply `VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR` to the assumption, which gives us the existence of a sequence $b$ and a number $k$ satisfying the factorization property.
* We then need to show that $k$ equals the multiplicity of $r$ as a root of the polynomial $\sum_{i=0}^{n} a_i x^i$.
* This is done by applying the `MULTIPLICITY_UNIQUE` theorem, which states that if a polynomial can be factored as $(x-r)^k$ times another polynomial that doesn't have $r$ as a root, then $k$ is uniquely determined as the multiplicity of $r$.
* Since we already have from the assumptions that $\sum_{i=0}^{m} b_i r^i \neq 0$, this means $r$ is not a root of the polynomial $\sum_{i=0}^{m} b_i x^i$, confirming that $k$ must be the multiplicity of $r$.

### Mathematical insight
This theorem relates the number of sign variations in a polynomial's coefficients to the multiplicity of its positive roots. It's a refinement of Descartes' Rule of Signs, which states that the number of positive real roots of a polynomial is bounded by the number of sign variations in its coefficients.

The key insight is that when a polynomial has a positive root $r$ with multiplicity $k$, this contributes exactly $k$ to the total sign variations, plus possibly some even number (which represents "lost" variations that don't correspond to actual roots). This helps in understanding how the structure of a polynomial's roots relates to patterns in its coefficients.

This result is important for numerical analysis and algebraic geometry, as it provides a way to analyze properties of polynomials based solely on the sign patterns of their coefficients.

### Dependencies
- **Theorems**
  - `VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR` - Provides the factorization property for polynomials with positive roots
  - `MULTIPLICITY_UNIQUE` - Establishes that the multiplicity of a root in a polynomial factorization is unique

### Porting notes
When porting this theorem, special attention should be paid to:
- The definition of "variation" or "sign changes" in a sequence
- The definition of "multiplicity" of a root
- The representation of polynomials (in HOL Light they are represented as coefficient sequences)

The proof relies on factorizing a polynomial with respect to a root, which might require different techniques in other proof assistants depending on how they represent and manipulate polynomials.

---

## DESCARTES_RULE_OF_SIGNS

### Name of formal statement
DESCARTES_RULE_OF_SIGNS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DESCARTES_RULE_OF_SIGNS = prove
 (`!f a n. f = (\x. sum(0..n) (\i. a i * x pow i)) /\
           (?i. i IN 0..n /\ ~(a i = &0))
           ==> ?d. EVEN d /\
                   variation(0..n) a =
                   nsum {r | &0 < r /\ f(r) = &0} (\r. multiplicity f r) + d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`a:num->real`; `n:num`] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:num->real` THEN ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `a:num->real`)] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[IN_NUMSEG; ARITH_RULE `i <= n ==> i <= n - 1 \/ i = n`];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
      ASM_SIMP_TAC[LE_0; LE_1; SUM_CLAUSES_RIGHT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      MATCH_MP_TAC VARIATION_SUBSET THEN
      REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
      SUBGOAL_THEN `i:num = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    DISCH_THEN(K ALL_TAC)] THEN
  ASM_CASES_TAC `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} = {}` THENL
   [ASM_REWRITE_TAC[NSUM_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1] THEN
    ONCE_REWRITE_TAC[GSYM NOT_ODD] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ODD_VARIATION_POSITIVE_ROOT) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real`; `n:num`; `a:num->real`]
    VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:num->real`; `m:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
   [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `d1 + d2:num` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[EVEN_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `x + y = z ==> (x + d1) + (y + d2):num = z + d1 + d2`) THEN
  SUBGOAL_THEN
   `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} =
    r INSERT {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `x IN s /\ s DELETE x = t ==> s = x INSERT t`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `s:real` THEN
      FIRST_X_ASSUM(K ALL_TAC o SPEC_VAR) THEN
      ASM_CASES_TAC `s:real = r` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | sum(0..m) (\i. b i * r pow i) = &0}` THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_POLYFUN_FINITE_ROOTS] THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL];
    SIMP_TAC[NSUM_CLAUSES; IN_ELIM_THM] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `s1:num = s2 ==> s1 + m = m + s2`) THEN
  MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [t]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_OTHER_ROOT THEN
  REWRITE_TAC[MESON[] `(?i. P i /\ Q i) <=> ~(!i. P i ==> ~Q i)`] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(sum (0..m) (\j. b j * r pow j) = &0)` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SUM_0]);;
```

### Informal statement
For a real polynomial $f(x) = \sum_{i=0}^{n} a_i x^i$ with at least one non-zero coefficient (i.e., there exists some $i \in \{0,1,\dots,n\}$ such that $a_i \neq 0$), there exists an even number $d$ such that:

$$\text{variation}(0..n)(a) = \sum_{r > 0, f(r) = 0} \text{multiplicity}(f, r) + d$$

where $\text{variation}(0..n)(a)$ counts the number of sign variations in the sequence of coefficients $a_0, a_1, \dots, a_n$, and $\text{multiplicity}(f, r)$ denotes the multiplicity of $r$ as a root of $f$.

### Informal proof
We proceed by well-founded induction on $n$.

* Let $f(x) = \sum_{i=0}^{n} a_i x^i$ with at least one non-zero coefficient.

* Case 1: If $a_n = 0$:
  - If $n = 0$, then the conclusion follows trivially since we assumed at least one coefficient is non-zero.
  - If $n > 0$, we apply the induction hypothesis to the polynomial truncated at degree $n-1$, i.e., $\sum_{i=0}^{n-1} a_i x^i$. Since $a_n = 0$, this polynomial has the same positive roots as the original one, and the number of sign variations remains unchanged when removing a zero coefficient.

* Case 2: If $a_n \neq 0$:
  - If the set $\{r \mid r > 0 \text{ and } f(r) = 0\}$ is empty:
    - Then by the contrapositive of the theorem on odd variation implying a positive root, the variation must be even. We can take $d$ to be the variation itself.
    
  - If the set is non-empty:
    - Let $r$ be a positive root of $f$.
    - By the property of factoring out a root with its multiplicity, we can write $f(x) = (x - r)^m \cdot g(x)$ where $m$ is the multiplicity of $r$ and $g$ is a polynomial of degree $n-m$ with coefficients $b_0, b_1, \dots, b_{n-m}$ where $b_{n-m} \neq 0$ and $g(r) \neq 0$.
    - Apply the induction hypothesis to $g$, obtaining an even number $d_1$ such that:
      $$\text{variation}(0..n-m)(b) = \sum_{s > 0, g(s) = 0} \text{multiplicity}(g, s) + d_1$$
    - We know that the set of positive roots of $f$ is $\{r\} \cup \{s \mid s > 0 \text{ and } g(s) = 0\}$.
    - We also know from a previous result that $\text{variation}(0..n)(a) = \text{variation}(0..n-m)(b) + m - 2d_2$ for some even number $d_2$.
    - Setting $d = d_1 + d_2$, we have:
      $$\text{variation}(0..n)(a) = \sum_{s > 0, f(s) = 0} \text{multiplicity}(f, s) + d$$
    - Since $d_1$ and $d_2$ are both even, $d$ is also even.

### Mathematical insight
Descartes' Rule of Signs is a fundamental result in polynomial theory that connects the algebraic structure of a polynomial (the sign pattern of its coefficients) with its geometric behavior (the distribution of its positive roots).

The theorem states that the number of positive real roots of a polynomial, counting multiplicity, is at most equal to the number of sign variations in the sequence of its coefficients, and differs from it by an even number. This provides a quick way to estimate the number of positive roots without directly solving the polynomial.

For example, a polynomial with 3 sign variations in its coefficients must have either 3 or 1 positive real roots (counting multiplicity), since the difference must be even.

The result is particularly useful in qualitative analysis of polynomials and has applications in various fields including computer algebra systems, numerical analysis, and control theory.

### Dependencies
#### Theorems:
- `ODD_VARIATION_POSITIVE_ROOT`: States that if a polynomial has an odd number of sign variations, then it must have at least one positive root.
- `VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR`: Relates the sign variations in a polynomial to those of a polynomial after factoring out a root.
- `VARIATION_SUBSET`: Provides properties of sign variations on coefficient subsets.
- `MULTIPLICITY_OTHER_ROOT`: Relates the multiplicity of roots across related polynomials.
- `REAL_POLYFUN_FINITE_ROOTS`: States that a non-zero real polynomial has finitely many roots.

#### Concepts:
- `variation`: Counts the number of sign changes in a sequence of coefficients.
- `multiplicity`: The multiplicity of a root in a polynomial.
- `num_WF`: Well-founded induction principle for natural numbers.

### Porting notes
When porting this theorem:
1. Ensure that the definition of sign variation in coefficient sequences is properly formalized.
2. The proof relies heavily on polynomial factorization and manipulation, so a good library for polynomial operations is essential.
3. The multiplicity concept for roots needs to be defined consistently with how it appears in this theorem.
4. The proof uses well-founded induction on the degree of the polynomial, which might require different tactics in other proof assistants.

---

