# gcd.ml

## Overview

Number of statements: 3

This file implements the Euclidean algorithm for computing greatest common divisors (GCD) in HOL Light, building upon the prime number theory from the library. It defines the GCD function and proves its fundamental properties including existence, uniqueness, commutativity, and association with divisibility relations. The file also establishes connections between GCD and other number-theoretic concepts like coprimality and the Bézout identity.

## EGCD_INVARIANT

### Name of formal statement
EGCD_INVARIANT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EGCD_INVARIANT = prove
 (`!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `m + n` THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[egcd] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  COND_CASES_TAC THEN
  (W(fun (asl,w) -> FIRST_X_ASSUM(fun th ->
    MP_TAC(PART_MATCH (lhs o snd o dest_forall o rand) th (lhand w)))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[DIVIDES_SUB; DIVIDES_ADD; SUB_ADD; LE_CASES]);;
```

### Informal statement
For all natural numbers $m$, $n$, and $d$:
$$d \text{ divides } \gcd(m,n) \iff d \text{ divides } m \land d \text{ divides } n$$

Where $\gcd(m,n)$ is the greatest common divisor of $m$ and $n$ computed using the Euclidean algorithm as defined by the recursive function `egcd`.

### Informal proof
This proof establishes that the `egcd` function correctly computes the greatest common divisor by showing that it preserves the fundamental property of GCD: a number divides the GCD if and only if it divides both input numbers.

* The proof uses well-founded induction on the sum $m + n$.
* After expanding the definition of `egcd`, we consider several cases:
  * If $m = 0$, then $\gcd(0,n) = n$, and the property holds because $d$ divides $0$ (by `DIVIDES_0`) and $d$ divides $n$ iff $d$ divides $n$.
  * If $n = 0$, then $\gcd(m,0) = m$, and similarly the property holds.
  * For the recursive cases (when $m \leq n$ or $m > n$), we apply the inductive hypothesis, since the sum of arguments decreases in each recursive call.
  * The proof uses the properties that:
    * If $d$ divides $a$ and $d$ divides $b$, then $d$ divides $a - b$ (by `DIVIDES_SUB`)
    * If $d$ divides $a$ and $d$ divides $b$, then $d$ divides $a + b$ (by `DIVIDES_ADD`)
    * For any $a$ and $b$, either $a \leq b$ or $b \leq a$ (by `LE_CASES`)
  * These properties allow us to show that the set of divisors remains invariant through the recursive calls of `egcd`.

### Mathematical insight
This theorem establishes a fundamental invariant of the Euclidean algorithm: the divisibility property is preserved throughout the computation. This invariant is crucial for proving that the `egcd` function correctly computes the greatest common divisor.

The Euclidean algorithm is one of the oldest and most efficient methods for computing the GCD. It works by repeatedly applying the property that $\gcd(m,n) = \gcd(m, n-m)$ when $m \leq n$, and symmetrically when $m > n$.

This theorem is essential for developing number theory in formal systems, as GCD is a fundamental concept that underlies many results about divisibility, prime numbers, and modular arithmetic.

### Dependencies
- **Theorems:**
  - `DIVIDES_0`: For all $x$, $x$ divides $0$
  - `DIVIDES_SUB`: If $d$ divides $a$ and $d$ divides $b$, then $d$ divides $a - b$
  - `DIVIDES_ADD`: If $d$ divides $a$ and $d$ divides $b$, then $d$ divides $a + b$
  - `SUB_ADD`: Subtraction and addition are inverse operations
  - `LE_CASES`: For any $a$ and $b$, either $a \leq b$ or $b \leq a$
- **Definitions:**
  - `egcd`: The recursive Euclidean algorithm for computing GCD

### Porting notes
When porting this theorem:
1. Ensure the target system has a similar recursive definition of the Euclidean algorithm
2. The well-founded induction on `m + n` is crucial - make sure your system can handle this induction principle
3. The definition of divisibility (`divides`) should be consistent: typically $a$ divides $b$ means there exists $k$ such that $b = a \cdot k$
4. You may need to establish the basic divisibility properties (`DIVIDES_0`, `DIVIDES_ADD`, `DIVIDES_SUB`) in your target system first

---

## EGCD_GCD

### EGCD_GCD
- `EGCD_GCD`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EGCD_GCD = prove
 (`!m n. egcd(m,n) = gcd(m,n)`,
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  MESON_TAC[EGCD_INVARIANT; DIVIDES_REFL]);;
```

### Informal statement
For all integers $m$ and $n$, the extended greatest common divisor $\text{egcd}(m,n)$ equals the greatest common divisor $\text{gcd}(m,n)$.

Formally: $\forall m, n. \text{egcd}(m,n) = \text{gcd}(m,n)$

### Informal proof
The proof establishes that the extended GCD function `egcd` and the standard GCD function `gcd` compute the same value by showing they satisfy the same defining property.

- The proof first uses `GCD_UNIQUE`, which characterizes the GCD as the unique integer $d$ that:
  1. Divides both $m$ and $n$
  2. Is divisible by any common divisor of $m$ and $n$

- By applying `EGCD_INVARIANT`, which ensures that `egcd` satisfies these same conditions, the proof establishes that `egcd(m,n)` satisfies the defining property of `gcd(m,n)`.

- The `DIVIDES_REFL` theorem (which states that any number divides itself) is used to complete the reasoning about divisibility.

### Mathematical insight
The extended GCD function `egcd` calculates not just the greatest common divisor of two numbers, but also typically provides the coefficients for Bézout's identity. This theorem confirms that the first component of the extended computation correctly yields the standard GCD.

This result ensures that the extended Euclidean algorithm correctly computes the GCD while providing additional information (the Bézout coefficients) that is useful for solving linear Diophantine equations and computing modular inverses.

### Dependencies
- Theorems:
  - `GCD_UNIQUE`: Characterizes the GCD of two numbers as the unique integer that divides both numbers and is divisible by all their common divisors.
  - `DIVIDES_REFL`: States that any number divides itself.
  - `EGCD_INVARIANT`: Establishes that the extended GCD satisfies the defining properties of the GCD.

### Porting notes
When implementing this in other proof assistants:
- Make sure to define both `gcd` and `egcd` functions first
- Ensure your `egcd` implementation satisfies the expected invariant properties
- The approach should be straightforward if your system has good support for divisibility reasoning

---

## EGCD

### Name of formal statement
EGCD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EGCD = prove
 (`!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))`,
  REWRITE_TAC[EGCD_GCD; GCD]);;
```

### Informal statement
For all integers $a$ and $b$, the extended greatest common divisor function $\operatorname{egcd}(a,b)$ satisfies:
1. $\operatorname{egcd}(a,b)$ divides $a$ and $\operatorname{egcd}(a,b)$ divides $b$
2. For any integer $e$, if $e$ divides $a$ and $e$ divides $b$, then $e$ divides $\operatorname{egcd}(a,b)$

This states that $\operatorname{egcd}(a,b)$ is a greatest common divisor of $a$ and $b$.

### Informal proof
The proof is straightforward by rewriting the goal using two theorems:
1. First, use `EGCD_GCD` which relates $\operatorname{egcd}(a,b)$ to $\gcd(a,b)$
2. Then use the fundamental properties of the `GCD` function

This effectively shows that $\operatorname{egcd}(a,b)$ satisfies the defining properties of a greatest common divisor.

### Mathematical insight
This theorem establishes that the extended GCD function (`egcd`) satisfies the same defining properties as the standard greatest common divisor (`gcd`). The extended GCD function typically returns not just the GCD but also the coefficients for the Bézout's identity. This theorem confirms that the first component of the extended GCD function output is indeed a greatest common divisor.

While the standard `gcd` function only returns the greatest common divisor, the extended GCD function (`egcd`) is important in number theory and cryptography because it provides the Bézout coefficients $s$ and $t$ such that $as + bt = \gcd(a,b)$, which are essential for calculating modular inverses and solving linear Diophantine equations.

### Dependencies
- `EGCD_GCD`: Likely relates the extended GCD function to the standard GCD function
- `GCD`: Likely defines the properties of the greatest common divisor

### Porting notes
When porting to another system, note that different systems may have different representations of the extended GCD function. Some systems might return a tuple of values (the GCD and the Bézout coefficients) while others might use a record type or a different structure. The port should ensure that the same fundamental properties hold for whatever representation is chosen.

---

