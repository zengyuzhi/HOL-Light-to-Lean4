# birthday.ml

## Overview

Number of statements: 9

This file formalizes the classical birthday paradox/problem from probability theory, demonstrating how quickly the probability of a "collision" increases with group size. It provides theorems that establish the exact probability of at least one shared birthday in a group of n people, as well as approximation formulas and bounds. The formalization likely includes definitions for probability calculations, key theorems about collision probabilities, and supporting lemmas for deriving the well-known results such as the surprising fact that with just 23 people, the probability exceeds 50%.

## FUNSPACE_EMPTY

### FUNSPACE_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FUNSPACE_EMPTY = prove
 (`({} --> t) = {(\x. @y. T)}`,
  REWRITE_TAC[EXTENSION; IN_SING; funspace; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUN_EQ_THM]);;
```

### Informal statement
For any set $t$, the function space from the empty set to $t$ is equal to the singleton set containing only the function that maps any input to an arbitrarily chosen value (denoted by $\{(\lambda x. @y. T)\}$).

Formally, $\emptyset \rightarrow t = \{(\lambda x. @y. T)\}$, where:
- $\emptyset \rightarrow t$ represents the set of all functions from the empty set to $t$
- $@y. T$ is an arbitrary value (using Hilbert's epsilon operator to select some arbitrary value)

### Informal proof
The proof proceeds by showing set equality through bi-directional inclusion:

1. Apply the `EXTENSION` theorem to reduce the goal to showing that any function is in $\emptyset \rightarrow t$ if and only if it's in the singleton set $\{(\lambda x. @y. T)\}$.
   
2. Unfold the definitions of `IN_SING` (membership in a singleton set), `funspace` (the definition of the $\rightarrow$ operator), and `IN_ELIM_THM` (membership conditions).
   
3. Use `NOT_IN_EMPTY` to simplify the condition that no elements exist in the empty set.
   
4. Apply `FUN_EQ_THM` to establish function equality: two functions are equal if they agree on all inputs.
   
5. Since the domain is empty, the condition `(!x. x IN s ==> f(x) IN t)` is vacuously true for any function, and the condition `(!x. ~(x IN s) ==> f(x) = @y. T)` forces any function in the space to map all inputs to the arbitrary value `@y. T`.

Therefore, the function space $\emptyset \rightarrow t$ contains exactly one function: the constant function returning the arbitrary value.

### Mathematical insight
This theorem characterizes the function space from an empty domain. The result illustrates an important principle in set theory and type theory: a function from an empty domain is uniquely determined (up to extensional equality) because it has no inputs to specify. 

The theorem uses Hilbert's epsilon operator (`@y. T`) to provide a canonical representation for this unique function. The choice of the specific value doesn't matter; what matters is that there's exactly one function in this space.

This result is part of the foundational theory of function spaces and will be useful for reasoning about special cases in theorems involving function spaces.

### Dependencies
- Theorems:
  - `EXTENSION`: Set equality means membership equivalence
  - `IN_SING`: Membership in a singleton set
  - `IN_ELIM_THM`: Membership in a set defined by a predicate
  - `NOT_IN_EMPTY`: No element belongs to the empty set
  - `FUN_EQ_THM`: Function equality is pointwise equality
- Definitions:
  - `funspace`: Defines the restricted function space operator `-->`

### Porting notes
When porting to other proof systems:
1. The use of Hilbert's epsilon operator (`@y. T`) might need adaptation if the target system has a different approach to arbitrary value selection.
2. Some systems might have built-in function space operators that behave differently for empty domains, requiring careful alignment.
3. The treatment of functions with empty domain might vary between proof assistants, so check each system's conventions.

---

## HAS_SIZE_FUNSPACE

### HAS_SIZE_FUNSPACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HAS_SIZE_FUNSPACE = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)`,
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; FUNSPACE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[EXP; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(x INSERT s) --> t =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\ g IN s --> t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; funspace; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `f:A->B` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) x`; `\u. if u = x then @y. T else (f:A->B) u`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[IN_INSERT];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:B`; `g:A->B`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ d <=> d /\ a /\ b`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; funspace; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `u:A` THEN ASM_CASES_TAC `u:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any sets $s : A \to \text{bool}$ and $t : B \to \text{bool}$ with cardinalities $|s| = m$ and $|t| = n$ respectively, the function space $(s \to t)$ has size $n^m$.

Here, $(s \to t)$ represents the set of all functions $f : A \to B$ such that:
- For all $x \in s$, $f(x) \in t$
- For all $x \not\in s$, $f(x) = @y.T$ (where $@y.T$ is some arbitrary fixed value)

### Informal proof
The proof proceeds by induction on the set $s$.

* Base case: When $s = \emptyset$ (the empty set)
  - By definition, $(\emptyset \to t) = \{(\lambda x. @y.T)\}$, which is a singleton set
  - Therefore, $|(\emptyset \to t)| = 1 = n^0 = n^m$ as required
  
* Inductive step: Assume the theorem holds for a finite set $s$
  - We need to prove it for $(x \cup s)$ where $x \notin s$
  - First, we establish that $(x \cup s) \to t$ can be represented as:
    $\text{IMAGE } (\lambda(y,g).(\lambda u. \text{if } u = x \text{ then } y \text{ else } g(u))) \{(y,g) \mid y \in t \text{ and } g \in (s \to t)\}$
  - This representation captures the fact that a function on $(x \cup s)$ is determined by:
    1. Its value at $x$ (which must be in $t$)
    2. Its behavior on $s$ (which must be a function in $(s \to t)$)
  - We prove this is an injective mapping
  - By the induction hypothesis, $|(s \to t)| = n^m$
  - Since $|t| = n$, the cardinality of the Cartesian product $|t \times (s \to t)| = n \times n^m = n^{m+1} = n^{|x \cup s|}$
  - Therefore $(x \cup s) \to t$ has size $n^{|x \cup s|}$ as required

### Mathematical insight
This theorem establishes the cardinality of the restricted function space $(s \to t)$, showing that it follows the standard combinatorial principle that there are $n^m$ possible functions from a set of size $m$ to a set of size $n$. 

The key insight is that even though functions in $(s \to t)$ are technically defined on the entire domain type $A$, only their behavior on $s$ matters for distinguishing them, as they all must take the same arbitrary value outside of $s$. This matches our intuition that when counting functions from $s$ to $t$, we have $n$ choices for each of the $m$ elements in the domain.

### Dependencies
- **Theorems**:
  - `FUNSPACE_EMPTY`: States that the function space from the empty set is a singleton containing just the arbitrary function
  - `HAS_SIZE`: Definition of a set having a specific size
  - Various other theorem manipulations including `CARD_CLAUSES`, `FINITE_INDUCT_STRONG`, `HAS_SIZE_IMAGE_INJ`, `HAS_SIZE_PRODUCT`

- **Definitions**:
  - `funspace`: Defines the function space notation $(s \to t)$ as the set of functions that map elements in $s$ to elements in $t$ and map elements outside $s$ to some arbitrary fixed value

### Porting notes
When porting this theorem:
1. Consider how to handle the function space notation - some systems might already have a similar concept
2. Pay attention to the handling of "arbitrary fixed values" (represented in HOL Light as `@y. T`)
3. The proof relies on an induction on finite sets, which might require different tactics in other systems
4. The representation of functions as explicitly having a fixed value outside the domain is important for the cardinality result

---

## FACT_DIVIDES

### Name of formal statement
FACT_DIVIDES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIVIDES = prove
 (`!m n. m <= n ==> ?d. FACT(n) = d * FACT(m)`,
  REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:num` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  ASM_MESON_TAC[MULT_AC; MULT_CLAUSES]);;
```

### Informal statement
For any natural numbers $m$ and $n$, if $m \leq n$, then there exists a natural number $d$ such that $n! = d \cdot m!$

Where $FACT(n)$ denotes the factorial of $n$.

### Informal proof
The proof proceeds by rewriting the inequality $m \leq n$ using the `LE_EXISTS` theorem, which states that $m \leq n$ if and only if there exists a $p$ such that $n = m + p$.

1. First, we rewrite the goal using `LE_EXISTS` and `LEFT_IMP_EXISTS_THM` to transform $m \leq n$ into $\exists p.\ n = m + p$.
2. We then fix $m$ and swap the order of the universal quantifiers.
3. Using `LEFT_FORALL_IMP_THM` and `EXISTS_REFL`, we simplify the goal structure.
4. We proceed by induction on $p$ (the difference between $n$ and $m$):
   - Base case ($p = 0$): Here $n = m$, so $n! = m!$, and we can choose $d = 1$.
   - Inductive step: Assume the result holds for $p$, we must prove it for $p + 1$.
     When $n = m + (p + 1)$, we have $n! = (m + p + 1) \cdot (m + p)!$
     By the induction hypothesis, $(m + p)! = d' \cdot m!$ for some $d'$
     Therefore, $n! = (m + p + 1) \cdot d' \cdot m! = d \cdot m!$ where $d = (m + p + 1) \cdot d'$
5. The final step uses `ASM_MESON_TAC` with the associativity and commutativity of multiplication (`MULT_AC`) and basic multiplication properties (`MULT_CLAUSES`) to complete the proof.

### Mathematical insight
This theorem formalizes the well-known number theory result that if $m \leq n$, then $m!$ divides $n!$. This follows from the fact that $n! = n \cdot (n-1) \cdot \ldots \cdot (m+1) \cdot m!$, so $n!/m!$ is a product of consecutive integers.

This result is frequently used in number theory, combinatorics, and probability theory. For instance, it is essential in proving properties of binomial coefficients, where $\binom{n}{m} = \frac{n!}{m!(n-m)!}$.

The theorem also explains why factorials grow so quickly: each factorial is a multiple of all smaller factorials.

### Dependencies
- **Theorems:**
  - `LE_EXISTS`: Relates $m \leq n$ to the existence of $p$ such that $n = m + p$
  - `LEFT_IMP_EXISTS_THM`: Logical manipulation for implications and existentials
  - `SWAP_FORALL_THM`: Reorders universal quantifiers
  - `LEFT_FORALL_IMP_THM`: Manipulation of universal quantifiers in implications
  - `EXISTS_REFL`: Basic property of existential quantification
  - `ADD_CLAUSES`: Basic properties of addition
  - `FACT`: Definition and properties of factorial
  - `MULT_AC`: Associativity and commutativity of multiplication
  - `MULT_CLAUSES`: Basic properties of multiplication

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition of factorial that matches HOL Light's `FACT`.
2. The proof relies on rewriting inequality $m \leq n$ as $\exists p.\ n = m + p$, which might need a separate lemma in systems that don't have this built-in.
3. The automated reasoning step using `ASM_MESON_TAC` might need to be replaced with more explicit steps in systems with different automation capabilities.
4. Consider whether induction on the difference between $n$ and $m$ is the most natural approach in your target system, or if direct induction on $n$ might be clearer.

---

## FACT_DIV_MULT

### Name of formal statement
FACT_DIV_MULT

### Type of formal statement
theorem

### Formal Content
```ocaml
let FACT_DIV_MULT = prove
 (`!m n. m <= n ==> FACT n = (FACT(n) DIV FACT(m)) * FACT(m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP FACT_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT; GSYM LT_NZ; FACT_LT]);;
```

### Informal statement
For any natural numbers $m$ and $n$ such that $m \leq n$, the factorial of $n$ can be expressed as:
$n! = \left\lfloor\frac{n!}{m!}\right\rfloor \cdot m!$

where $\lfloor \cdot \rfloor$ represents the integer division operation.

### Informal proof
The proof proceeds as follows:

1. We start with the theorem `FACT_DIVIDES` which states that for any $m \leq n$, there exists some $d$ such that $n! = d \cdot m!$.

2. Apply `FACT_DIVIDES` to our assumption $m \leq n$ to obtain $d$ such that $n! = d \cdot m!$.

3. Use this equality to rewrite the goal.

4. Apply commutativity of multiplication to rewrite $d \cdot m!$ as $m! \cdot d$.

5. Finally, we use the theorem `DIV_MULT` which states that $(a \cdot b) \div b = a$ when $b > 0$.

6. The condition $b > 0$ (i.e., $m! > 0$) is satisfied by `FACT_LT`, which ensures that the factorial of any number is strictly positive.

7. Therefore, $d = n! \div m!$, and substituting this back gives us the desired result: $n! = (n! \div m!) \cdot m!$.

### Mathematical insight
This theorem formalizes a natural property about factorials and integer division: when $m \leq n$, the factorial $n!$ is divisible by $m!$, and the quotient $n! \div m!$ corresponds to the product of integers from $m+1$ to $n$.

The result is particularly useful in combinatorial mathematics, as $n! \div m!$ represents the number of ways to arrange $(n-m)$ distinct objects among $n$ positions when $m$ positions are already fixed. It's also a key component in computing binomial coefficients.

In formal theorem proving, this result helps simplify expressions involving factorial divisions, providing a clean way to work with such terms.

### Dependencies
- Theorems:
  - `FACT_DIVIDES`: For any $m \leq n$, there exists $d$ such that $n! = d \cdot m!$
  - `DIV_MULT`: $(a \cdot b) \div b = a$ when $b > 0$
  - `FACT_LT`: The factorial of any number is strictly positive
  - `LT_NZ`: $n > 0$ if and only if $n \neq 0$
  - `MULT_SYM`: Commutativity of multiplication

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the target system has the appropriate division operation that truncates toward zero for natural numbers.
- Make sure that factorial is defined for natural numbers and that its basic properties (like being strictly positive) are available.
- The proof relies on the existence theorem `FACT_DIVIDES`, which should be ported first.
- Many proof assistants have built-in simplification rules for divisions that might make the proof even simpler than in HOL Light.

---

## HAS_SIZE_FUNSPACE_INJECTIVE

### HAS_SIZE_FUNSPACE_INJECTIVE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_SIZE_FUNSPACE_INJECTIVE = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}
            HAS_SIZE (if n < m then 0 else (FACT n) DIV (FACT(n - m)))`,
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; FUNSPACE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[FINITE_RULES; CARD_CLAUSES; FACT] THEN
    SIMP_TAC[NOT_IN_EMPTY; LT; SUB_0; DIV_REFL; GSYM LT_NZ; FACT_LT] THEN
    REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{f | f IN (x INSERT s) --> t /\
    (!u v. u IN (x INSERT s) /\ v IN (x INSERT s) /\ f u = f v ==> u = v)} =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\
                     g IN {f | f IN (s --> (t DELETE y)) /\
                               !u v. u IN s /\ v IN s /\ f u = f v ==> u = v}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; funspace; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `f:A->B` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) x`; `\u. if u = x then @y. T else (f:A->B) u`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_INSERT; IN_DELETE; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:B`; `g:A->B`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ d <=> d /\ a /\ b`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; funspace; IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `u:A` THEN ASM_CASES_TAC `u:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `(if n < SUC (CARD s) then 0 else FACT n DIV FACT (n - SUC (CARD s))) =
    n * (if (n - 1) < CARD(s:A->bool) then 0
         else FACT(n - 1) DIV FACT (n - 1 - CARD s))`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> (n - 1 < m <=> n < SUC m)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `n - SUC(m) = n - 1 - m`] THEN
    UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[FACT; SUC_SUB1] THEN DISCH_TAC THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; FACT_LT; GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC FACT_DIV_MULT THEN ARITH_TAC;
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE]]);;
```

### Informal statement
This theorem states that for sets $s$ and $t$ with cardinalities $m$ and $n$ respectively, the set of injective functions from $s$ to $t$ has cardinality $\frac{n!}{(n-m)!}$ if $n \geq m$, and $0$ otherwise.

More formally, for any sets $s \subseteq A$ and $t \subseteq B$ with $|s| = m$ and $|t| = n$, the set
$\{f \mid f \in (s \to t) \land \forall x,y \in s. (f(x) = f(y) \implies x = y)\}$ 
has cardinality equal to:
- $\frac{n!}{(n-m)!}$ if $n \geq m$
- $0$ if $n < m$

Here, $(s \to t)$ denotes the set of functions $f$ from $A$ to $B$ such that $f(x) \in t$ for all $x \in s$, and $f(x) = @y.T$ (an arbitrary value) for all $x \notin s$.

### Informal proof

The proof proceeds by strong induction on the size of set $s$:

* **Base case** (when $s$ is empty): 
  - The function space from empty set $\emptyset \to t$ contains exactly one function (by `FUNSPACE_EMPTY`).
  - This function trivially satisfies the injectivity condition (as there are no elements in the domain).
  - The expected cardinality is $\frac{n!}{n!} = 1$ when $n \geq 0$, which matches our result.

* **Inductive case** (for non-empty set $s = \{x\} \cup s'$ where $s'$ is the remaining set):
  - We show that the set of injective functions from $x \cup s'$ to $t$ can be represented as:
    $\{f \mid f \in ((x \cup s') \to t) \land \forall u,v \in (x \cup s'). (f(u) = f(v) \implies u = v)\} = $
    $\text{IMAGE}(\lambda(y,g).(\lambda u. \text{if } u = x \text{ then } y \text{ else } g(u)))$
    $\{(y,g) \mid y \in t \land g \in \{f \mid f \in (s' \to (t \setminus \{y\})) \land \forall u,v \in s'. (f(u) = f(v) \implies u = v)\}\}$
  
  - This representation means that each injective function $f$ from $x \cup s'$ to $t$ can be uniquely determined by:
    1. Choosing a value $y \in t$ for $f(x)$
    2. Finding an injective function $g$ from $s'$ to $t \setminus \{y\}$

  - We prove this mapping is injective (one-to-one) between these two representations.

  - By the inductive hypothesis, the number of injective functions from $s'$ to $t \setminus \{y\}$ is:
    - $\frac{(n-1)!}{(n-1-(m-1))!} = \frac{(n-1)!}{(n-m)!}$ if $n-1 \geq m-1$
    - $0$ otherwise
  
  - Since there are $n$ possible choices for $y$, the total number of injective functions is:
    $n \cdot \frac{(n-1)!}{(n-m)!} = \frac{n!}{(n-m)!}$ if $n \geq m$
    $0$ otherwise

  - We verify that this matches our expected formula by simplifying the expression.

### Mathematical insight
This theorem quantifies a fundamental combinatorial fact: the number of different ways to inject a finite set with $m$ elements into a finite set with $n$ elements is $\frac{n!}{(n-m)!}$, which is often denoted as $P(n,m)$ or ${}^n P_m$ (the number of permutations of $n$ things taken $m$ at a time).

The result has a natural interpretation: when creating an injection from a set of size $m$ to a set of size $n$ (assuming $n \geq m$), we:
1. Choose the image for the first element (n choices)
2. Choose the image for the second element (n-1 choices)
...
m. Choose the image for the mth element (n-m+1 choices)

Multiplying these together gives $n(n-1)(n-2)...(n-m+1) = \frac{n!}{(n-m)!}$.

If $n < m$, no injection can exist by the pigeonhole principle, hence the cardinality is 0.

### Dependencies
- Definitions:
  - `funspace`: Defines the function space from a set to another set
- Theorems:
  - `FUNSPACE_EMPTY`: The function space from empty set to any set contains only one function
  - `SUC_SUB1`: The successor of a number minus 1 equals the original number
  - `FACT_DIV_MULT`: For $m \leq n$, we have $n! = \frac{n!}{m!} \cdot m!$

### Porting notes
- Care should be taken with the function space definition, which specifies a default value for elements outside the domain.
- The inductive structure on finite sets may vary between proof assistants, requiring adjustment to the induction strategy.
- The handling of the cardinality calculation, particularly the factorial division, might need different tactics in other systems.

---

## HAS_SIZE_DIFF

### HAS_SIZE_DIFF
- HAS_SIZE_DIFF

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_SIZE_DIFF = prove
 (`!s t:A->bool m n.
        s SUBSET t /\ s HAS_SIZE m /\ t HAS_SIZE n
        ==> (t DIFF s) HAS_SIZE (n - m)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `s SUBSET t ==> t = s UNION (t DIFF s)`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_DIFF; ADD_SUB2;
               SET_RULE `s INTER (t DIFF s) = {}`]);;
```

### Informal statement
For all sets $s$ and $t$ of type $A \to \text{bool}$ (representing sets of elements of type $A$) and natural numbers $m$ and $n$, if:
- $s$ is a subset of $t$ ($s \subseteq t$)
- $s$ has size $m$ ($|s| = m$)
- $t$ has size $n$ ($|t| = n$)

Then the set difference $t \setminus s$ has size $n - m$ ($|t \setminus s| = n - m$).

### Informal proof
The proof proceeds as follows:

- First, we simplify the goal using the definition of `HAS_SIZE` and a theorem about the finiteness of set differences (`FINITE_DIFF`).
- We introduce all the universal quantifiers into the context using `REPEAT GEN_TAC`.
- We split the assumption "$s \subseteq t \land s$ has size $m \land t$ has size $n$" into two parts:
  1. "$s \subseteq t$" (which we assume)
  2. "$s$ has size $m \land t$ has size $n$" (which we continue to process)
- We further split the second part recursively to get all individual assumptions into the context.
- We use the symmetric form of the numerical size property for substitution in the goal.
- From the assumption $s \subseteq t$, we derive that $t = s \cup (t \setminus s)$ using a set rule.
- We rewrite the goal using this equality.
- Finally, we apply simplification with:
  - `CARD_UNION`: $|A \cup B| = |A| + |B| - |A \cap B|$ when $A$ and $B$ are finite
  - `FINITE_DIFF`: If $t$ is finite, then $t \setminus s$ is finite
  - `ADD_SUB2`: $a + b - a = b$
  - The set rule that $s \cap (t \setminus s) = \emptyset$

The last step combines these facts to establish that $|t| = |s| + |t \setminus s| - 0 = |s| + |t \setminus s|$, which gives us $|t \setminus s| = |t| - |s| = n - m$.

### Mathematical insight
This theorem establishes a fundamental property of finite sets: if one set is a subset of another, then the size of their difference equals the difference of their sizes. This is an intuitive result that formalizes the natural expectation that removing $m$ elements from a set of size $n$ leaves exactly $n-m$ elements.

The result is particularly useful in combinatorial proofs and counting arguments, where we often need to reason about the cardinality of set differences. It's also a direct application of the principle of inclusion-exclusion for the special case of a subset relationship.

### Dependencies
- `HAS_SIZE`: Definition that relates a set to its cardinality
- `FINITE_DIFF`: Theorem stating that if a set is finite, so is its difference with another set
- `CARD_UNION`: Theorem for the cardinality of the union of two finite sets
- `ADD_SUB2`: Arithmetic theorem that $a + b - a = b$
- `SET_RULE`: Various set-theoretic rules, particularly:
  - `s SUBSET t ==> t = s UNION (t DIFF s)`: A set equals the union of its subset and the difference
  - `s INTER (t DIFF s) = {}`: The intersection of a set with the difference of another set minus itself is empty

### Porting notes
When porting this theorem:
1. Ensure your system's set theory includes proper definitions for set difference, subset relation, and size/cardinality
2. The key arithmetic property needed is simply that $a + b - a = b$
3. Watch for differences in notation for set operations (especially set difference, which might be written as `\` or `−` in other systems)
4. Note that the HOL Light proof relies heavily on theorem-application tactics that might need different approaches in other systems

---

## BIRTHDAY_THM

### BIRTHDAY_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIRTHDAY_THM = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
            HAS_SIZE (if m <= n then (n EXP m) - (FACT n) DIV (FACT(n - m))
                      else n EXP m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{f:A->B | f IN (s --> t) /\
              ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)} =
    (s --> t) DIFF
    {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}`] THEN
  REWRITE_TAC[ARITH_RULE
   `(if a <= b then x - y else x) = x - (if b < a then 0 else y)`] THEN
  MATCH_MP_TAC HAS_SIZE_DIFF THEN
  ASM_SIMP_TAC[HAS_SIZE_FUNSPACE_INJECTIVE; HAS_SIZE_FUNSPACE] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;
```

### Informal statement
For finite sets $s$ and $t$ with cardinalities $|s| = m$ and $|t| = n$ respectively, the set of functions $f : s \to t$ that have at least one collision (i.e., there exist distinct elements $x, y \in s$ such that $f(x) = f(y)$) has cardinality:
- If $m \leq n$, then $n^m - \frac{n!}{(n-m)!}$
- If $m > n$, then $n^m$

In the formal statement:
- `s HAS_SIZE m` means that $s$ is a finite set with cardinality $m$
- `t HAS_SIZE n` means that $t$ is a finite set with cardinality $n$
- `s --> t` represents the set of all functions from $s$ to $t$
- `f IN (s --> t)` means $f$ is a function from $s$ to $t$
- `?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)` means there exist distinct elements $x, y \in s$ such that $f(x) = f(y)$

### Informal proof
The proof proceeds by rewriting the set of functions with collisions as the difference between all functions and injective functions, then applying set cardinality properties:

1. First, we rewrite the set of functions with collisions as the complement of injective functions:
   $$\{f \in (s \to t) \mid \exists x,y \in s : x \neq y \wedge f(x) = f(y)\} = (s \to t) \setminus \{f \in (s \to t) \mid \forall x,y \in s : f(x) = f(y) \implies x = y\}$$

2. We simplify the conditional expression:
   $$(if\ m \leq n\ then\ n^m - \frac{n!}{(n-m)!}\ else\ n^m) = n^m - (if\ n < m\ then\ 0\ else\ \frac{n!}{(n-m)!})$$

3. We apply `HAS_SIZE_DIFF` to compute the cardinality of the difference between the set of all functions and the set of injective functions:
   - The cardinality of all functions from $s$ to $t$ is $n^m$ (by `HAS_SIZE_FUNSPACE`)
   - The cardinality of injective functions is $\frac{n!}{(n-m)!}$ when $n \geq m$ and $0$ when $n < m$ (by `HAS_SIZE_FUNSPACE_INJECTIVE`)

4. The result follows by subtracting the cardinality of injective functions from the cardinality of all functions.

### Mathematical insight
This theorem formalizes the mathematics underlying the famous "Birthday Paradox" (or "Birthday Problem") in probability theory. The result gives the exact count of functions that produce at least one collision.

The formula makes intuitive sense because:
- When $m > n$ (more inputs than outputs), every function must have at least one collision by the pigeonhole principle, so all $n^m$ possible functions exhibit collisions.
- When $m \leq n$, we count all $n^m$ possible functions and subtract the number of injective functions $\frac{n!}{(n-m)!}$, which is the number of ways to select $m$ distinct values from $t$ (order matters).

This theorem is important in cryptography, hashing, and probability theory, as it gives the exact probability of collisions in various scenarios.

### Dependencies
- `HAS_SIZE_FUNSPACE`: Computes the cardinality of the set of all functions between finite sets
- `HAS_SIZE_FUNSPACE_INJECTIVE`: Computes the cardinality of the set of all injective functions between finite sets
- `HAS_SIZE_DIFF`: Computes the cardinality of the difference of finite sets
- `SET_RULE`: Used for set-theoretic rewriting
- `ARITH_RULE`: Used for arithmetic simplification

### Porting notes
When porting this theorem:
1. Ensure that your target system has a good representation of finite sets and their cardinalities
2. You'll need to have already ported the dependent theorems about function spaces and injectivity
3. In systems with dependent types (like Coq or Lean), you might define functions over finite types rather than using set-theoretic constructions, which could simplify the formulation

---

## FACT_DIV_SIMP

### Name of formal statement
FACT_DIV_SIMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIV_SIMP = prove
 (`!m n. m < n
         ==> (FACT n) DIV (FACT m) = n * FACT(n - 1) DIV FACT(m)`,
  GEN_TAC THEN REWRITE_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[ARITH_RULE `(m + SUC d) - 1 - m = d`] THEN
  REWRITE_TAC[ARITH_RULE `(m + SUC d) - 1 = m + d`; ADD_SUB2] THEN
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[FACT_LT; ARITH_RULE `x + 0 = x`] THEN REWRITE_TAC[FACT] THEN
  SIMP_TAC[GSYM MULT_ASSOC; GSYM FACT_DIV_MULT; LE_ADD] THEN
  REWRITE_TAC[ADD_CLAUSES; FACT]);;
```

### Informal statement
For any natural numbers $m$ and $n$ where $m < n$, the factorial ratio $\frac{n!}{m!}$ can be simplified as:

$$\frac{n!}{m!} = \frac{n \cdot (n-1)!}{m!}$$

### Informal proof
The proof proceeds by rewriting the inequality $m < n$ in terms of an existential quantifier.

* First, we use `LT_EXISTS` to rewrite $m < n$ as $\exists d. n = m + \text{SUC}(d)$, i.e., $n = m + (d+1)$.
* We rearrange the quantifiers and simplify the resulting expressions.
* We use arithmetic rules to simplify:
  * $(m + \text{SUC}(d)) - 1 - m = d$
  * $(m + \text{SUC}(d)) - 1 = m + d$
* We apply `DIV_UNIQ` with remainder $0$ to establish the equality of the division operation.
* Using `FACT_LT` and the definition of factorial (`FACT`), we further simplify.
* We apply `FACT_DIV_MULT` (which states that if $m \leq n$ then $n! = \frac{n!}{m!} \cdot m!$) along with associativity of multiplication.
* Final simplifications using the recursive definition of factorial complete the proof.

### Mathematical insight
This theorem provides a simplification for factorial division that's useful in combinatorial calculations. It expresses the ratio of consecutive factorials in terms of smaller factorials, enabling stepwise computation.

The key insight is that $n! = n \cdot (n-1)!$, which allows us to rewrite the division in a form that can be computed more efficiently or used in further algebraic manipulations.

This result is particularly important in combinatorial mathematics where factorial ratios appear in binomial coefficients and other counting problems.

### Dependencies
#### Theorems
- `FACT_DIV_MULT`: For $m \leq n$, $n! = \frac{n!}{m!} \cdot m!$
- `LT_EXISTS`: Expresses $m < n$ as $\exists d. n = m + \text{SUC}(d)$
- `FACT_LT`: The factorial function is strictly positive for all natural numbers
- `DIV_UNIQ`: Uniqueness property of division with remainder

#### Arithmetic Rules
- `ARITH_RULE`: Various arithmetic simplifications

#### Definitions
- `FACT`: The factorial function

### Porting notes
When implementing this in another system:
- Ensure the factorial function is properly defined for natural numbers
- Check how the target system handles division of natural numbers
- Make sure the uniqueness property of division is available
- Note that HOL Light uses a 0-based SUC representation for natural numbers

---

## BIRTHDAY_THM_EXPLICIT

### Name of formal statement
BIRTHDAY_THM_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIRTHDAY_THM_EXPLICIT = prove
 (`!s t. s HAS_SIZE 23 /\ t HAS_SIZE 365
         ==> 2 * CARD {f | f IN (s --> t) /\
                           ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
             >= CARD (s --> t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BIRTHDAY_THM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  REPEAT(CHANGED_TAC
   (SIMP_TAC[FACT_DIV_SIMP; ARITH_LE; ARITH_LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV))) THEN
  SIMP_TAC[DIV_REFL; GSYM LT_NZ; FACT_LT] THEN
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;
```

### Informal statement
For any sets $s$ and $t$ such that $s$ has size $23$ and $t$ has size $365$, the following inequality holds:
$$2 \cdot |\{f \mid f \in (s \to t) \land \exists x,y \in s: x \neq y \land f(x) = f(y)\}| \geq |s \to t|$$

In other words, if $s$ has exactly 23 elements and $t$ has exactly 365 elements, then the number of functions from $s$ to $t$ that are not injective is at least half the total number of functions from $s$ to $t$.

### Informal proof
This theorem is a formalization of the birthday paradox, which shows that in a group of 23 people, the probability that at least two people share a birthday (out of 365 possible days) is greater than 50%.

The proof proceeds as follows:

* Apply the `BIRTHDAY_THM` to the assumption that $|s| = 23$ and $|t| = 365$.
* This theorem tells us that the number of non-injective functions from $s$ to $t$ is $365^{23} - \frac{365!}{(365-23)!}$.
* Apply `HAS_SIZE_FUNSPACE` to determine that the total number of functions is $365^{23}$.
* Simplify the factorial expressions using `FACT_DIV_SIMP` repeatedly.
* After simplification and numerical computation, we find that:
  $$365^{23} - \frac{365!}{(365-23)!} > \frac{365^{23}}{2}$$
* This shows that the number of non-injective functions is greater than half the total number of functions, establishing the theorem.

The final step uses `NUM_REDUCE_CONV` to perform the actual numerical calculation that confirms the inequality.

### Mathematical insight
This theorem formalizes the famous "birthday paradox" which demonstrates that in a group of just 23 people, the probability that at least two share a birthday exceeds 50%. The result is often surprising to people because intuition might suggest that you need closer to 183 people (half of 365) for such a probability.

The key insight is that we're not looking for a specific pair sharing a birthday, but any pair sharing any birthday. The number of possible pairs grows quadratically with group size, which is why the threshold is much lower than intuition would suggest.

The formulation here is in terms of sets and functions rather than probability. It shows that if we consider all possible functions from a 23-element set to a 365-element set, more than half of these functions will map at least two distinct elements to the same value (i.e., be non-injective).

This result has applications in many areas, including cryptography, where it forms the basis for birthday attacks on hash functions.

### Dependencies
- Theorems:
  - `BIRTHDAY_THM`: The general theorem about the cardinality of non-injective functions between finite sets
  - `HAS_SIZE_FUNSPACE`: Establishes the cardinality of function spaces between finite sets
  - `FACT_DIV_SIMP`: Simplification theorem for factorial division

### Porting notes
When porting this theorem:
- Ensure your system has appropriate libraries for numerical computation, as the final step relies on calculating a specific numerical inequality.
- The proof relies on factorial and exponential calculations, so ensure your system can handle these efficiently.
- The formalization uses the concept of function spaces, so ensure your target system has a way to represent the set of all functions between two sets.

---

