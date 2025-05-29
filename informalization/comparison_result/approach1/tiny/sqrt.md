# sqrt.ml

## Overview

Number of statements: 3

This file proves several key irrationality results in number theory, with the irrationality of √2 as a focal case. It builds on prime number theory and floor function definitions to establish a general framework for proving irrationality of square roots and other algebraic numbers. The file includes formal proofs of irrationality for √n where n is not a perfect square, as well as more general irrationality results about roots of certain polynomials.

## IRRATIONAL_SQRT_NONSQUARE

### IRRATIONAL_SQRT_NONSQUARE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IRRATIONAL_SQRT_NONSQUARE = prove
 (`!n. rational(sqrt(&n)) ==> ?m. n = m EXP 2`,
  REWRITE_TAC[rational] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [integer])) THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV] THEN DISCH_THEN(MP_TAC o MATCH_MP(REAL_FIELD
   `p = (n / m) pow 2 ==> ~(m = &0) ==> m pow 2 * p = n pow 2`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
  ASM_MESON_TAC[EXP_MULT_EXISTS; REAL_ABS_ZERO; REAL_OF_NUM_EQ]);;
```

### Informal statement
The theorem states that if the square root of a natural number $n$ is rational, then $n$ must be a perfect square. Formally:

For all natural numbers $n$, if $\sqrt{n}$ is rational, then there exists a natural number $m$ such that $n = m^2$.

### Informal proof
The proof proceeds as follows:

- We start by applying the definition of being rational, which means $\sqrt{n} = \frac{p}{q}$ for some integers $p$ and $q$ with $q \neq 0$.
- Square both sides of this equality to get $n = \frac{p^2}{q^2}$.
- Use the fact that $\sqrt{n}^2 = n$ for $n \geq 0$.
- Rewrite in terms of absolute values to ensure we're working with positive quantities.
- From $n = \frac{p^2}{q^2}$, we can multiply both sides by $q^2$ to get $q^2 \cdot n = p^2$.
- Using number theory, specifically the theorem `EXP_MULT_EXISTS`, we can deduce that if $m^k \cdot n = p^k$ (where $m \neq 0$), then $n = q^k$ for some $q$. 
- Applying this with $k = 2$, $m = q$, and $p$ as above, we conclude that $n = m^2$ for some natural number $m$.

### Mathematical insight
This theorem generalizes the classic result that $\sqrt{2}$ is irrational. It provides a complete characterization of which natural numbers have rational square roots - precisely those that are perfect squares. This is a fundamental result in number theory.

The contrapositive statement is often more useful: if $n$ is not a perfect square, then $\sqrt{n}$ is irrational. So for example, $\sqrt{2}$, $\sqrt{3}$, $\sqrt{5}$, etc. are all irrational numbers.

The proof technique uses the fundamental theorem of arithmetic (unique prime factorization) implicitly through the `EXP_MULT_EXISTS` theorem. The key insight is that the exponents of prime factors must be even in a perfect square.

### Dependencies
- Theorems:
  - `EXP_MULT_EXISTS`: If $m \neq 0$ and $m^k \cdot n = p^k$, then there exists $q$ such that $n = q^k$.
- Used implicitly:
  - `rational`: Definition of rational numbers
  - `integer`: Definition of integers
  - `SQRT_POW_2`: Property that $\sqrt{x}^2 = x$ for $x \geq 0$
  - `REAL_POS`: Property that certain expressions are positive
  - `REAL_POW2_ABS`: Property relating squares and absolute values

### Porting notes
When porting this theorem:
1. Ensure that the number theory libraries with prime factorization properties are available
2. Be careful with the distinction between natural numbers, integers, and reals in your target system
3. The theorem uses real square roots, so make sure your target system has a compatible definition of square roots for real numbers

---

## IRRATIONAL_SQRT_PRIME

### Name of formal statement
IRRATIONAL_SQRT_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IRRATIONAL_SQRT_PRIME = prove
 (`!p. prime p ==> ~rational(sqrt(&p))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP IRRATIONAL_SQRT_NONSQUARE) THEN
  REWRITE_TAC[PRIME_EXP; ARITH_EQ]);;
```

### Informal statement
For all prime numbers $p$, the square root of $p$ is irrational. In symbols:

$$\forall p. \text{prime}(p) \Rightarrow \neg\text{rational}(\sqrt{p})$$

### Informal proof
The proof uses a contrapositive approach to show that if $\sqrt{p}$ is rational, then $p$ cannot be prime.

* We start by applying contraposition: assume $\sqrt{p}$ is rational and show that $p$ is not prime.
* By the theorem `IRRATIONAL_SQRT_NONSQUARE`, if $\sqrt{n}$ is rational, then $n$ must be a perfect square, i.e., $n = m^2$ for some integer $m$.
* Therefore, $p = m^2$ for some integer $m$.
* Using `PRIME_EXP`, we know that $p^n$ is prime if and only if $p$ is prime and $n = 1$.
* In our case, $p = m^2 = m^1 \cdot m^1$, which means $p$ is not of the form $q^1$ where $q$ is prime.
* Therefore, $p$ cannot be prime.

### Mathematical insight
This theorem establishes the irrationality of square roots of prime numbers, which is a classical result in number theory. The key insight is that rational numbers, when written in lowest form, have a square root that is rational only when the original number is a perfect square. Since prime numbers are not perfect squares, their square roots must be irrational.

This result is part of a broader investigation into which real numbers are rational or irrational, which has been fundamental to number theory since ancient Greek mathematics (particularly Pythagoras' discovery of irrational numbers).

### Dependencies
- `CONTRAPOS_THM`: Contraposition theorem
- `IRRATIONAL_SQRT_NONSQUARE`: If $\sqrt{n}$ is rational, then $n$ is a perfect square
- `PRIME_EXP`: A power $p^n$ is prime if and only if $p$ is prime and $n = 1$

### Porting notes
When porting this theorem:
1. Ensure that the target system has a definition of rationality for real numbers
2. Verify that the system has a definition of prime numbers
3. Check that the square root function is properly defined for natural numbers
4. The proof relies on the contrapositive approach, which should be available in most proof assistants

---

## IRRATIONAL_SQRT_2

### IRRATIONAL_SQRT_2
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IRRATIONAL_SQRT_2 = prove
 (`~rational(sqrt(&2))`,
  SIMP_TAC[IRRATIONAL_SQRT_PRIME; PRIME_2]);;
```

### Informal statement
The square root of 2 is irrational.

Formally: $\sqrt{2} \notin \mathbb{Q}$.

### Informal proof
This theorem follows immediately from two more general results:

1. The square root of any prime number is irrational (theorem IRRATIONAL_SQRT_PRIME)
2. The number 2 is a prime number (theorem PRIME_2)

Since 2 is prime, we can apply the first theorem to conclude that $\sqrt{2}$ is irrational.

### Mathematical insight
This is one of the most famous proofs in mathematics, dating back to ancient Greek mathematics. The irrationality of $\sqrt{2}$ was reportedly discovered by the Pythagoreans and caused a major crisis in their mathematical philosophy, which had assumed that all lengths could be expressed as ratios of integers.

The result is foundational in number theory as it demonstrates the existence of irrational numbers. This particular proof in HOL Light uses a more general theorem about the irrationality of square roots of prime numbers, showing how the famous result is a special case of a broader pattern.

### Dependencies
- Theorems:
  - `IRRATIONAL_SQRT_PRIME`: The square root of any prime number is irrational
  - `PRIME_2`: 2 is a prime number

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it relies only on:
1. The definition of irrationality
2. The primality of 2
3. The general theorem about irrationality of square roots of primes

Most proof assistants will have these concepts already formalized or they can be easily defined.

---

