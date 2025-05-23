# fta.ml

## Overview

Number of statements: 10

This file formalizes the Fundamental Theorem of Arithmetic, which establishes the unique factorization of natural numbers into prime factors. Building on the prime number theory defined in `prime.ml`, it proves that every natural number greater than 1 can be expressed uniquely as a product of primes, up to reordering. The formalization includes key lemmas about prime factorization, divisibility properties, and the uniqueness of prime decomposition.

## nproduct

### Name of formal statement
nproduct

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let nproduct = new_definition `nproduct = iterate ( * )`;;
```

### Informal statement
$\text{nproduct}$ is defined as the iterated multiplication operation. Specifically, $\text{nproduct} = \text{iterate}(\times)$, where $\text{iterate}$ applies a binary operation repeatedly over a collection of elements.

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
The `nproduct` function is a foundational definition that provides a mechanism for taking the product of a collection of numbers. It's defined using the `iterate` higher-order function, which generalizes the concept of applying a binary operation repeatedly across a collection.

This definition is particularly important in the context of number theory, especially for the fundamental theorem of arithmetic (unique prime factorization) as indicated in the comment. When working with prime factorizations, we need to represent products of prime powers, which is precisely what `nproduct` enables.

The definition abstracts away the mechanics of iteration, allowing for cleaner statements of theorems involving products of numbers.

### Dependencies
- `iterate`: A higher-order function that iteratively applies a binary operation to elements in a collection

### Porting notes
When porting to another system, ensure that:
1. An equivalent `iterate` function exists or is defined first
2. The multiplication operation is correctly passed as an argument to `iterate`
3. The type system of the target proof assistant properly handles the types for binary operations and iteration

In some systems like Lean or Coq, this might be implemented using a fold operation over lists or finite sets, possibly with a more specific type signature that makes the domain and codomain explicit.

---

## NPRODUCT_CLAUSES

### Name of formal statement
NPRODUCT_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_CLAUSES = prove
 (`(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MUL]);;
```

### Informal statement
This theorem establishes the basic properties of the `nproduct` function (numerical product over a set):

1. For any function $f$, the product over the empty set is equal to 1:
   $$\forall f. \prod_{x \in \emptyset} f(x) = 1$$

2. For any function $f$, element $x$, and finite set $s$:
   $$\forall x,f,s. \text{FINITE}(s) \implies \prod_{y \in (x \cup s)} f(y) = \begin{cases}
   \prod_{y \in s} f(y) & \text{if } x \in s \\
   f(x) \cdot \prod_{y \in s} f(y) & \text{if } x \notin s
   \end{cases}$$

### Informal proof
The proof proceeds by reducing the `nproduct` properties to general properties of the `ITERATE` function:

1. First, we rewrite using the definition of `nproduct`, which is defined in terms of `ITERATE` with the neutral element 1 (using `GSYM NEUTRAL_MUL` to express this).

2. We then apply `SWAP_FORALL_THM` to rearrange the quantifiers in a suitable form for the next step.

3. Finally, we apply the general `ITERATE_CLAUSES` theorem using `MATCH_MP_TAC`, showing that multiplication forms a monoidal operation (using `MONOIDAL_MUL`).

The proof essentially shows that `nproduct` inherits the recursive structure of the general `ITERATE` function when applied to the particular monoidal operation of multiplication with identity element 1.

### Mathematical insight
This theorem establishes the fundamental recursive structure of the numerical product operation over finite sets. It provides:

1. A base case: the product over an empty set equals 1 (the multiplicative identity)
2. A recursive case: how to compute the product over a set with an additional element

These properties are essential for inductive reasoning about products over sets. The recursive structure mirrors the familiar pattern of iterative operations over sets, similar to summation, allowing us to build products incrementally by adding elements to the set.

The theorem connects set-based notation (product over a set) to computational approaches (recursive calculation), making it a foundation for both theoretical and algorithmic treatments of products.

### Dependencies
- `nproduct`: Definition of numerical product over sets
- `ITERATE_CLAUSES`: Theorem about the basic properties of the `ITERATE` function
- `MONOIDAL_MUL`: Theorem establishing that multiplication with identity 1 forms a monoidal operation
- `NEUTRAL_MUL`: Theorem about the neutral element for multiplication (1)
- `SWAP_FORALL_THM`: Theorem for rearranging universal quantifiers

### Porting notes
When porting this theorem:
1. Ensure that the target system has a corresponding concept for iterating an operation over a finite set
2. Verify that multiplication is properly defined as a monoidal operation with identity 1
3. The conditional expression (`if x IN s then ... else ...`) might need special handling in systems with different conditional syntax

---

## NPRODUCT_EQ_1_EQ

### Name of formal statement
NPRODUCT_EQ_1_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ_1_EQ = prove
 (`!s f. FINITE s ==> (nproduct s f = 1 <=> !x. x IN s ==> f(x) = 1)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; MULT_EQ_1; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
For any finite set $s$ and function $f$, the product of $f(x)$ over all elements $x \in s$ equals 1 if and only if $f(x) = 1$ for all $x \in s$. 

Formally: 
$$\forall s, f. \text{FINITE}(s) \Rightarrow (\text{nproduct}(s, f) = 1 \Leftrightarrow \forall x. x \in s \Rightarrow f(x) = 1)$$

### Informal proof
This theorem is proven by strong induction over finite sets:

1. First, the theorem is rewritten to prepare for induction using `REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]`.

2. Then apply strong finite induction with `MATCH_MP_TAC FINITE_INDUCT_STRONG`.

3. For the base and inductive cases:
   * Base case (empty set): The product over an empty set is 1 by definition, and the condition $\forall x \in \emptyset. f(x) = 1$ is vacuously true.
   * Inductive case: For a set with a new element inserted, the product equals 1 if and only if both $f$ at the new element equals 1 and the product over the rest of the set equals 1.

4. The inductive step is handled by simplifying with `NPRODUCT_CLAUSES`, `IN_INSERT`, `MULT_EQ_1`, and `NOT_IN_EMPTY`.

5. The remaining subgoals are resolved using the induction hypothesis through `ASM_MESON_TAC[]`.

### Mathematical insight
This theorem characterizes when a product over a finite set equals 1, which is a fundamental property in algebra. The result is intuitive: a product equals 1 if and only if all terms in the product equal 1.

The theorem is particularly useful when working with multiplicative structures like groups or fields, where the identity element is 1. It provides a direct way to relate a global property (the product being 1) to a local property (each factor being 1).

In formal verification, this result helps simplify proofs involving products, particularly in applications such as probability theory, number theory, or algebraic structures.

### Dependencies
- **Theorems**:
  - `FINITE_INDUCT_STRONG` - Strong induction principle for finite sets
  - `NPRODUCT_CLAUSES` - Basic properties of products over sets
  - `MULT_EQ_1` - Characterization of when a product equals 1
  - `IN_INSERT` - Membership property for set insertion
  - `NOT_IN_EMPTY` - No elements belong to the empty set
  - `IMP_CONJ` - Logical transformation for implications and conjunctions
  - `RIGHT_FORALL_IMP_THM` - Logical transformation for quantified implications

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the target system has an equivalent notion of products over sets (`nproduct` in HOL Light).
- The proof relies on a strong induction principle for finite sets that might need to be established first.
- The automated reasoning in `ASM_MESON_TAC[]` might require more explicit steps in systems with different automation capabilities.

---

## NPRODUCT_SPLITOFF

### Name of formal statement
NPRODUCT_SPLITOFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_SPLITOFF = prove
 (`!x:A f s. FINITE s
             ==> nproduct s f =
                 (if x IN s then f(x) else 1) * nproduct (s DELETE x) f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  SUBGOAL_THEN `s = (x:A) INSERT (s DELETE x)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th] THEN
              ASM_SIMP_TAC[NPRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]);;
```

### Informal statement
For any element $x$ of type $A$, function $f$, and finite set $s$, the product $\prod_{t \in s} f(t)$ can be rewritten as:

$$\prod_{t \in s} f(t) = f(x) \cdot \prod_{t \in s \setminus \{x\}} f(t)$$

if $x \in s$, and

$$\prod_{t \in s} f(t) = 1 \cdot \prod_{t \in s \setminus \{x\}} f(t)$$

if $x \notin s$.

This can be written concisely as:

$$\prod_{t \in s} f(t) = (if~x \in s~then~f(x)~else~1) \cdot \prod_{t \in s \setminus \{x\}} f(t)$$

### Informal proof
The proof proceeds by case analysis on whether $x \in s$ or not:

* Case 1: $x \notin s$
  * In this case, $s \setminus \{x\} = s$ (by set theory)
  * Therefore, $1 \cdot \prod_{t \in s \setminus \{x\}} f(t) = 1 \cdot \prod_{t \in s} f(t) = \prod_{t \in s} f(t)$
  * This matches the required equality when $x \notin s$

* Case 2: $x \in s$
  * We establish that $s = \{x\} \cup (s \setminus \{x\})$
  * By the definition of product over sets, $\prod_{t \in s} f(t) = \prod_{t \in \{x\} \cup (s \setminus \{x\})} f(t)$
  * Using the property that the product over a union of disjoint sets equals the product of the products over each set (from `NPRODUCT_CLAUSES`), and given that $x \notin (s \setminus \{x\})$
  * We get $\prod_{t \in s} f(t) = f(x) \cdot \prod_{t \in s \setminus \{x\}} f(t)$
  * This matches the required equality when $x \in s$

### Mathematical insight
This theorem provides a way to split off a single element from a finite product, which is a fundamental tool for inductive reasoning about products. It's analogous to how we can split a sum as $\sum_{t \in s} f(t) = f(x) + \sum_{t \in s \setminus \{x\}} f(t)$ when $x \in s$.

The result is particularly useful for induction proofs where we need to reduce the size of the set we're working with by removing one element at a time. It also enables various algebraic manipulations of finite products by allowing us to extract specific elements from the product.

### Dependencies
- **Theorems**: `NPRODUCT_CLAUSES`
- **Definitions**: `nproduct`
- **Set operations**: `DELETE`, `IN`, `INSERT`
- **Set theorems**: `FINITE_DELETE`, `IN_DELETE`
- **Logical operations**: `MULT_CLAUSES` (basic multiplication properties)

### Porting notes
When porting this theorem:
1. Ensure the target system has a corresponding notion of product over finite sets
2. Pay attention to how set operations like deletion (`s DELETE x`) are defined
3. The proof relies on simplification with set-theoretic reasoning, so use appropriate set manipulation lemmas in the target system

---

## NPRODUCT_SPLITOFF_HACK

### Name of formal statement
NPRODUCT_SPLITOFF_HACK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_SPLITOFF_HACK = prove
 (`!x:A f s. nproduct s f =
             if FINITE s then
               (if x IN s then f(x) else 1) * nproduct (s DELETE x) f
             else nproduct s f`,
  REPEAT STRIP_TAC THEN MESON_TAC[NPRODUCT_SPLITOFF]);;
```

### Informal statement
For any element $x$ of type $A$, any function $f$ from $A$ to a multiplicative structure, and any set $s$ of elements of type $A$, the product $\prod_{i \in s} f(i)$ equals:
- If $s$ is finite:
  - If $x \in s$, then $f(x) \cdot \prod_{i \in s \setminus \{x\}} f(i)$
  - If $x \notin s$, then $1 \cdot \prod_{i \in s \setminus \{x\}} f(i)$ (which is equivalent to $\prod_{i \in s} f(i)$)
- If $s$ is infinite, then the product remains unchanged (as $\prod_{i \in s} f(i)$)

### Informal proof
This theorem is proved by direct application of the existing theorem `NPRODUCT_SPLITOFF`. The proof uses MESON, a first-order theorem prover, to automatically derive the result from `NPRODUCT_SPLITOFF`.

`NPRODUCT_SPLITOFF` already states that for any finite set $s$ and an element $x \in s$, we have $\prod_{i \in s} f(i) = f(x) \cdot \prod_{i \in s \setminus \{x\}} f(i)$. This theorem simply generalizes it by handling the case where $x$ might not be in $s$ and where $s$ might not be finite.

### Mathematical insight
This theorem provides a way to extract a specific term from a product over a finite set. It's particularly useful in inductive proofs about products, where you might need to separate one element and reason about the rest of the product. 

The theorem is called "HACK" likely because it reformulates the existing `NPRODUCT_SPLITOFF` theorem in a conditional form that makes it more convenient in certain proof contexts. The advantage of this formulation is that:

1. It handles the case where $x$ is not in the set $s$
2. It explicitly states what happens when $s$ is infinite
3. It puts the result in an if-then-else form that can be directly used in simplification steps

This makes it more generally applicable in automated reasoning without requiring additional case analysis.

### Dependencies
#### Theorems
- `NPRODUCT_SPLITOFF`: The base theorem that this result generalizes, stating that for finite sets, a product can be split into one element times the product of the remaining elements.

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has a similar notion of product over sets
2. Check how the target system handles empty products (typically defined as 1)
3. The conditional structure may need to be represented differently depending on the system's syntax for if-then-else expressions
4. Consider whether the target system needs separate handling for finite and infinite sets, as some systems might have different product definitions for these cases

---

## NPRODUCT_EQ

### Name of formal statement
NPRODUCT_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ = prove
 (`!f g s. FINITE s /\ (!x. x IN s ==> f x = g x)
           ==> nproduct s f = nproduct s g`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT]);;
```

### Informal statement
For any functions $f$ and $g$, and any set $s$, if $s$ is finite and $f(x) = g(x)$ for all $x \in s$, then 
$$\prod_{x \in s} f(x) = \prod_{x \in s} g(x)$$

### Informal proof
This theorem is proved by induction on the finite set $s$:

* Base case: When $s$ is empty, both products are equal to 1 by definition of `nproduct`.
* Induction step: Assume the theorem holds for a finite set $t$. We need to show it holds for $s = \{a\} \cup t$ where $a \notin t$.

The proof uses:
1. `FINITE_INDUCT_STRONG` to perform induction on the finite set
2. `NPRODUCT_CLAUSES` which states that:
   * $\prod_{x \in \emptyset} f(x) = 1$
   * For $a \notin t$, $\prod_{x \in \{a\} \cup t} f(x) = f(a) \cdot \prod_{x \in t} f(x)$
3. `IN_INSERT` to handle the membership condition for inserted elements

Since $f(x) = g(x)$ for all $x \in s$, we have $f(a) = g(a)$ and $f(x) = g(x)$ for all $x \in t$. By the induction hypothesis, $\prod_{x \in t} f(x) = \prod_{x \in t} g(x)$. Therefore, $\prod_{x \in s} f(x) = f(a) \cdot \prod_{x \in t} f(x) = g(a) \cdot \prod_{x \in t} g(x) = \prod_{x \in s} g(x)$.

### Mathematical insight
This theorem establishes that the product of values over a finite set depends only on the values of the function on that set, and not on how the function is defined elsewhere. It's an extensionality property for numeric products, similar to extensionality properties for other operators like summation.

This is a fundamental result for working with products in formal mathematics, as it allows substitution of equals for equals within the scope of a product, which is essential for many calculations and manipulations involving products.

### Dependencies
- `FINITE_INDUCT_STRONG`: Induction principle for finite sets
- `NPRODUCT_CLAUSES`: Basic properties of `nproduct` for empty sets and set insertion
- `IN_INSERT`: Membership property for inserted elements in a set

### Porting notes
When porting this theorem:
- Ensure that the target system has a notion of product over finite sets
- The proof relies on induction over finite sets, which should be available in most proof assistants
- The structure is straightforward and should translate directly to systems like Lean, Isabelle, or Coq

---

## NPRODUCT_EQ_GEN

### Name of formal statement
NPRODUCT_EQ_GEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ_GEN = prove
 (`!f g s t. FINITE s /\ s = t /\ (!x. x IN s ==> f x = g x)
             ==> nproduct s f = nproduct t g`,
  MESON_TAC[NPRODUCT_EQ]);;
```

### Informal statement
For any functions $f$ and $g$, and sets $s$ and $t$, if $s$ is finite, $s = t$, and for all $x \in s$, $f(x) = g(x)$, then $\prod_{x \in s} f(x) = \prod_{x \in t} g(x)$.

### Informal proof
This theorem is proven directly using the `NPRODUCT_EQ` theorem through the `MESON_TAC` tactic. 

The proof follows from the fact that if $s = t$ and $f(x) = g(x)$ for all $x \in s$, then the numerical products over these sets with their respective functions must be equal. This is a straightforward application of extensionality principles for finite products.

### Mathematical insight
This theorem generalizes equality conditions for numerical products over finite sets. It states that if two sets are equal and the functions agree on all elements of the set, then the products are equal. This is a natural extension of the more basic `NPRODUCT_EQ` theorem, allowing for greater flexibility when working with finite products.

The result is useful in contexts where you want to rewrite a product expression by substituting both the set and the function simultaneously, provided they satisfy the given conditions.

### Dependencies
- `NPRODUCT_EQ`: The theorem that establishes equality of numerical products when the functions agree on all elements of the same finite set.

### Porting notes
This theorem should be straightforward to port to other proof assistants. It's essentially an application of extensionality for finite products. Most proof assistants have similar theorems for their finite product operations, possibly with slightly different names or formulations.

---

## PRIME_DIVIDES_NPRODUCT

### Name of formal statement
PRIME_DIVIDES_NPRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_DIVIDES_NPRODUCT = prove
 (`!p s f. prime p /\ FINITE s /\ p divides (nproduct s f)
           ==> ?x. x IN s /\ p divides (f x)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[PRIME_DIVPROD; DIVIDES_ONE; PRIME_1]);;
```

### Informal statement
If $p$ is a prime number, $s$ is a finite set, and $p$ divides the product $\prod_{x \in s} f(x)$ (denoted as `nproduct s f`), then there exists an element $x \in s$ such that $p$ divides $f(x)$.

Formally:
$$\forall p \, s \, f. \text{prime}(p) \land \text{FINITE}(s) \land p \text{ divides } \prod_{x \in s} f(x) \Rightarrow \exists x. x \in s \land p \text{ divides } f(x)$$

### Informal proof
The proof proceeds by strong induction on the finite set $s$:

* For the base case where $s$ is empty:
  - The product $\prod_{x \in \emptyset} f(x)$ equals $1$ by the definition of `NPRODUCT_CLAUSES`
  - Since $p$ is prime, it does not divide $1$ (by `PRIME_1` and `DIVIDES_ONE`)
  - Therefore, the premise that $p$ divides the product is false, making the implication trivially true

* For the inductive case where $s = \{a\} \cup t$ with $a \notin t$:
  - The product becomes $f(a) \cdot \prod_{x \in t} f(x)$
  - If $p$ divides this product, then by the prime divisibility property (`PRIME_DIVPROD`), either:
    - $p$ divides $f(a)$, in which case $x = a$ satisfies our conclusion, or
    - $p$ divides $\prod_{x \in t} f(x)$, in which case by the induction hypothesis, there exists $x \in t$ such that $p$ divides $f(x)$

The proof combines these cases using `ASM_MESON_TAC` with the theorems `PRIME_DIVPROD`, `DIVIDES_ONE`, and `PRIME_1`.

### Mathematical insight
This theorem formalizes a fundamental property of prime numbers: if a prime divides a product, it must divide at least one of the factors. The theorem generalizes this to products over arbitrary finite sets, which is a key result used in number theory and algebra.

This property is one of the characteristic features of prime numbers and is closely related to the unique factorization theorem. It shows how prime numbers behave as "atomic" elements in the multiplicative structure of integers.

The result is especially useful in proofs about divisibility, factorization, and in more advanced algebraic settings where similar properties are studied for prime ideals in rings.

### Dependencies
- Theorems:
  - `PRIME_1`: States that 1 is not a prime number
  - `PRIME_DIVPROD`: If a prime divides a product of two numbers, then it divides at least one of them
- Definitions (implicitly used):
  - `nproduct`: Product over elements of a finite set
  - `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets
  - `NPRODUCT_CLAUSES`: Definition of product over empty and non-empty sets

### Porting notes
When porting this theorem:
- Ensure your system has a proper definition of `nproduct` for products over finite sets
- Consider how your system handles finite set induction - you may need to adapt the inductive argument based on the available induction principles
- The argument is relatively straightforward in any system with good support for arithmetic and set theory

---

## NPRODUCT_CANCEL_PRIME

### Name of formal statement
NPRODUCT_CANCEL_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_CANCEL_PRIME = prove
 (`!s p m f j.
        p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m
        ==> prime p /\ FINITE s /\ (!x. x IN s ==> prime x)
            ==> ~(j = 0) /\
                p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(j = 0) ==> j = SUC(j - 1)`)) THEN
    REWRITE_TAC[SUC_SUB1; EXP; GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
    MESON_TAC[PRIME_0]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s DELETE (p:num)`; `\p. p EXP (f p)`]
                 PRIME_DIVIDES_NPRODUCT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[divides; FINITE_DELETE]; ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[PRIME_1; prime; PRIME_DIVEXP]);;
```

### Informal statement
For any finite set $s$ of prime numbers, a prime number $p$, natural numbers $m$ and $j$, and a function $f$ mapping numbers to natural numbers, if:

$$p^j \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = p \cdot m$$

and $p$ is a prime number, $s$ is finite, and all elements of $s$ are prime numbers, then:
1. $j \neq 0$, and
2. $p^{j-1} \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = m$

This theorem allows cancelling a prime factor from both sides of an equation involving products of prime powers.

### Informal proof
We must prove that $j \neq 0$ and that $p^{j-1} \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = m$.

The proof proceeds by case analysis on $j$:

* **Case 1:** Suppose $j = 0$.
  - We'll proceed by contradiction, assuming $j = 0$.
  - With $p^0 \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = p \cdot m$
  - This simplifies to $\prod_{q \in s \setminus \{p\}} q^{f(q)} = p \cdot m$
  - Now, we can apply `PRIME_DIVIDES_NPRODUCT` which states that if a prime divides a product, then it divides at least one factor.
  - Since $p$ divides the right-hand side, it must divide $\prod_{q \in s \setminus \{p\}} q^{f(q)}$
  - But this means $p$ divides $q^{f(q)}$ for some $q \in s \setminus \{p\}$, where $q$ is prime and $q \neq p$.
  - By `PRIME_DIVEXP`, if a prime divides a power, it divides the base.
  - So $p$ would divide $q$ for some prime $q \neq p$, which is impossible since both are prime.
  - This contradiction shows that $j \neq 0$.

* **Case 2:** Suppose $j \neq 0$.
  - Then $j = (j-1) + 1$, so we can rewrite $p^j$ as $p \cdot p^{j-1}$
  - Substituting this into our equation:
    $p \cdot p^{j-1} \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = p \cdot m$
  - Cancelling $p$ from both sides (using `EQ_MULT_LCANCEL`):
    $p^{j-1} \cdot \prod_{q \in s \setminus \{p\}} q^{f(q)} = m$
  - Note that we can cancel $p$ because $p \neq 0$ (since $p$ is prime and `PRIME_0` states that 0 is not prime).

Thus, we've proven both needed conclusions.

### Mathematical insight
This theorem provides a way to cancel prime factors in equations involving products of prime powers. It plays a crucial role in number-theoretic manipulations, especially in unique factorization arguments.

The key insight is the fundamental property that if a prime divides a product, it must divide one of the factors. When combined with the unique factorization of integers, this allows us to manipulate expressions involving prime powers with precision.

The theorem is particularly useful when working with the canonical prime factorization form of natural numbers and simplifying equations in this representation.

### Dependencies
- **Theorems about primes:**
  - `PRIME_0`: 0 is not prime
  - `PRIME_1`: 1 is not prime
  - `PRIME_DIVEXP`: If a prime $p$ divides $x^n$, then $p$ divides $x$
  - `PRIME_DIVIDES_NPRODUCT`: If a prime divides a product, it divides at least one factor

### Porting notes
When porting this theorem, pay attention to:
1. The representation of the product over a set minus an element
2. The treatment of exponentiation
3. Assumptions about prime numbers (particularly that they're greater than 1)
4. The use of the contrapositive in the proof
5. The handling of divides relation and prime factorization

---

## FTA

### Name of formal statement
FTA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FTA = prove
 (`!n. ~(n = 0)
       ==> ?!i. FINITE {p | ~(i p = 0)} /\
                (!p. ~(i p = 0) ==> prime p) /\
                n = nproduct {p | ~(i p = 0)} (\p. p EXP (i p))`,
  ONCE_REWRITE_TAC[ARITH_RULE `n = nproduct s f <=> nproduct s f = n`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
    SIMP_TAC[NPRODUCT_EQ_1_EQ; EXP_EQ_1; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [EXISTS_TAC `\n:num. 0` THEN
      REWRITE_TAC[SET_RULE `{p | F} = {}`; FINITE_RULES];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `q:num` THEN ASM_CASES_TAC `q = 1` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PRIME_1]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  REWRITE_TAC[divides; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `m:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_FACTOR_LT]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\q:num. if q = p then i(q) + 1 else i(q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `p INSERT {p:num | ~(i p = 0)}` THEN
      ASM_SIMP_TAC[SUBSET; FINITE_INSERT; IN_INSERT; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ADD_EQ_0; ARITH] THEN
    REWRITE_TAC[MULT_ASSOC] THEN BINOP_TAC THENL
     [ASM_CASES_TAC `(i:num->num) p = 0` THEN
      ASM_REWRITE_TAC[EXP_ADD; EXP_1; EXP; MULT_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN RULE_ASSUM_TAC(SIMP_RULE[]) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; EXTENSION; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[TAUT
   `p /\ q /\ ((if p then x else y) = z) <=> p /\ q /\ x = z`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[EXP] `(if ~(x = 0) then p EXP x else 1) = p EXP x`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num->num`; `k:num->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\i:num. if i = p then j(i) - 1 else j(i)`;
    `\i:num. if i = p then k(i) - 1 else k(i)`]) THEN
  REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP NPRODUCT_CANCEL_PRIME)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `!j k. {q | ~((if q = p then j q else k q) = 0)} DELETE p =
          {q | ~(k q = 0)} DELETE p`] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`~(j(p:num) = 0)`; `~(k(p:num) = 0)`] THEN ARITH_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(j p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(k p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM]]);;
```

### Informal statement
The Fundamental Theorem of Arithmetic states that for any non-zero natural number $n$, there exists a unique function $i : \mathbb{N} \to \mathbb{N}$ such that:
- The set $\{p \mid i(p) \neq 0\}$ is finite
- For every $p$ with $i(p) \neq 0$, $p$ is prime
- $n = \prod_{p \in \{p \mid i(p) \neq 0\}} p^{i(p)}$

This means every non-zero natural number has a unique prime factorization, where $i(p)$ represents the exponent of prime $p$ in the factorization of $n$.

### Informal proof
The proof uses well-founded induction on natural numbers.

- First, rewrite the goal to a form that explicitly states the uniqueness of factorization.
- Use well-founded induction on the natural number $n$. 
- Consider the base case $n = 1$:
  * For $n = 1$, we can take $i$ to be the constant zero function.
  * The set $\{p \mid i(p) \neq 0\}$ is empty and finite.
  * The product $\prod_{p \in \emptyset} p^{i(p)} = 1$ as expected.
  * For uniqueness, if another function has $i(p) \neq 0$ for a prime $p$, this contradicts that $1$ is not prime (by `PRIME_1`).

- For the inductive case where $n > 1$:
  * Apply `PRIME_FACTOR` to obtain a prime factor $p$ such that $n = p \cdot m$ for some $m$.
  * Since $p$ is prime and $m \neq 0$, we know $m < n$ (by `PRIME_FACTOR_LT`).
  * Apply the induction hypothesis to $m$ to get a unique $i$ for $m$.
  * Define a new function $j$ where $j(q) = i(q) + 1$ if $q = p$, and $j(q) = i(q)$ otherwise.
  * Show that $j$ satisfies the required properties for $n$:
    * The set $\{q \mid j(q) \neq 0\}$ is finite since it's a subset of $\{p\} \cup \{p \mid i(p) \neq 0\}$.
    * Any $q$ with $j(q) \neq 0$ is prime, as was already true for $i$.
    * $n = p \cdot m = p \cdot \prod_{q \in \{q \mid i(q) \neq 0\}} q^{i(q)} = \prod_{q \in \{q \mid j(q) \neq 0\}} q^{j(q)}$.

- For uniqueness, suppose $j$ and $k$ are two factorizations of $n$.
  * Define $j'(q) = j(q) - 1$ if $q = p$ and $j'(q) = j(q)$ otherwise.
  * Similarly define $k'(q) = k(q) - 1$ if $q = p$ and $k'(q) = k(q)$ otherwise.
  * Show that $j'$ and $k'$ provide factorizations for $m$.
  * By the induction hypothesis, $j'$ and $k'$ must be equal.
  * This implies that $j$ and $k$ are also equal, completing the proof of uniqueness.

### Mathematical insight
The Fundamental Theorem of Arithmetic is one of the most important results in number theory. It states that every natural number greater than 1 can be expressed uniquely as a product of prime numbers, up to the order of the factors. 

In this formalization, rather than using multisets or lists of prime factors, the theorem is expressed using a function $i$ that maps each prime $p$ to its exponent in the factorization. This approach elegantly handles the uniqueness condition and avoids having to deal with the ordering of prime factors.

The theorem forms the basis for many results in number theory and explains why prime numbers are considered the "building blocks" of the natural numbers.

### Dependencies
- `PRIME_1`: States that 1 is not a prime number.
- `PRIME_FACTOR`: Every natural number greater than 1 has a prime factor.
- `PRIME_FACTOR_LT`: If prime $p$ divides non-zero $n$ with $n = p \cdot m$, then $m < n$.

### Porting notes
When porting this theorem to other systems:
- Consider how to represent the prime factorization. While HOL Light uses a function mapping primes to exponents, other systems might prefer a multiset or list representation.
- The uniqueness part of the proof relies on careful manipulation of the factorization functions, which may need different techniques in systems with different function handling.
- The well-founded induction on natural numbers is a standard technique that should be available in most proof assistants, but may have different syntax.

---

