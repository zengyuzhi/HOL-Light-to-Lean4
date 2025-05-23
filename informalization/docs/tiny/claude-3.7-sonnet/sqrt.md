# sqrt.ml

## Overview

Number of statements: 3

This file contains formal proofs of irrationality results, most notably the irrationality of the square root of 2, along with more general theorems about the irrationality of various roots of integers. It builds on prime number theory and floor function definitions from the imported libraries to construct these proofs. The formalization includes both specific irrationality results and general theorems characterizing when expressions of certain forms are irrational.

## IRRATIONAL_SQRT_NONSQUARE

### IRRATIONAL_SQRT_NONSQUARE
- `IRRATIONAL_SQRT_NONSQUARE`

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
The theorem states that for any natural number $n$, if $\sqrt{n}$ is rational, then there exists a natural number $m$ such that $n = m^2$.

In other words, if the square root of a natural number is rational, then that natural number must be a perfect square.

### Informal proof
The proof proceeds as follows:

- Start with the assumption that $\sqrt{n}$ is rational, which means by definition that $\sqrt{n} = \frac{p}{q}$ for integers $p$ and $q$ with $q \neq 0$.
- Square both sides of this equation to get $(\sqrt{n})^2 = (\frac{p}{q})^2$.
- The left side simplifies to $n$ since $(\sqrt{n})^2 = n$ for $n \geq 0$.
- For the right side, use the property that $|\frac{p}{q}|^2 = \frac{|p|^2}{|q|^2}$.
- This gives $n = \frac{|p|^2}{|q|^2}$, which implies $|q|^2 \cdot n = |p|^2$.
- Converting to natural numbers (using `REAL_OF_NUM_POW`, `REAL_OF_NUM_MUL`, and `REAL_OF_NUM_EQ`), we get $|q|^2 \cdot n = |p|^2$.
- Apply the theorem `EXP_MULT_EXISTS`, which states that if $m^k \cdot n = p^k$ and $m \neq 0$, then there exists a $q$ such that $n = q^k$.
- With $k = 2$, this gives us that $n = m^2$ for some natural number $m$, completing the proof.

### Mathematical insight
This theorem establishes a fundamental result in number theory: the square root of a natural number is either irrational or an integer. It's a generalization of the famous result that $\sqrt{2}$ is irrational.

The key insight is that rationality of square roots is deeply connected to the number-theoretic property of being a perfect square. This connection highlights how properties of real numbers (rationality) can be characterized by properties of natural numbers (being a perfect square).

This result is important because it provides a complete characterization of when square roots of natural numbers are rational, which is useful in various areas of mathematics including number theory and algebra.

### Dependencies
- Theorems:
  - `EXP_MULT_EXISTS`: If $m^k \cdot n = p^k$ and $m \neq 0$, then there exists a $q$ such that $n = q^k$.

### Porting notes
- This proof relies on basic properties of real numbers, square roots, and rational numbers.
- The definition of rationality (`rational`) and integer (`integer`) in HOL Light should be mapped to corresponding concepts in the target system.
- The theorem `EXP_MULT_EXISTS` is a key dependency that may need to be ported first.
- The proof uses several arithmetic simplifications that may require different tactics in other systems.

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
For any prime number $p$, the square root of $p$ is irrational, i.e., $\sqrt{p} \notin \mathbb{Q}$.

### Informal proof
We prove this by contraposition. Suppose $\sqrt{p}$ is rational.

By the theorem `IRRATIONAL_SQRT_NONSQUARE`, if $\sqrt{n}$ is rational, then $n$ must be a perfect square, i.e., $n = m^2$ for some integer $m$. 

So, our assumption that $\sqrt{p}$ is rational implies that $p = m^2$ for some integer $m$. But then $p = m^2 = m^1 \cdot m^1 = m^2$, which means $p$ is a perfect square.

Now we apply the theorem `PRIME_EXP`, which states that $p^n$ is prime if and only if $p$ is prime and $n = 1$. In our case, since $p = m^2$, we can write $p$ as $m^2 = m^1 \cdot m^1 = m^2$. By `PRIME_EXP`, this is prime if and only if $m$ is prime and $2 = 1$, which is false. Therefore, $p$ cannot be prime, contradicting our assumption.

Thus, if $p$ is prime, then $\sqrt{p}$ must be irrational.

### Mathematical insight
This theorem establishes that the square root of any prime number is irrational. This is a classic result and a special case of the more general fact that if $n$ is not a perfect square, then $\sqrt{n}$ is irrational. For prime numbers, it's particularly easy to see they can't be perfect squares (except for the case of $p=2^1$, which is included).

The proof uses contraposition and leverages the fact that prime numbers have very specific factorization properties - specifically, they cannot be expressed as perfect squares because a perfect square always has an even number of prime factors (counting multiplicities).

This result is important in number theory and is often one of the first examples of irrational numbers that students encounter after $\sqrt{2}$.

### Dependencies
- Theorems:
  - `PRIME_EXP`: A number raised to a power ($p^n$) is prime if and only if $p$ is prime and $n = 1$.
  - `IRRATIONAL_SQRT_NONSQUARE`: If $\sqrt{n}$ is rational, then $n$ must be a perfect square.
  - `CONTRAPOS_THM`: The principle of contraposition: $(P \implies Q) \iff (\neg Q \implies \neg P)$.

### Porting notes
When porting this theorem, ensure that the dependency theorems are available in your target system. The proof strategy using contraposition is straightforward and should work in most proof assistants. The key is ensuring proper handling of the rational numbers and square roots, which might have different representations in different systems.

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
The theorem states that the square root of 2 is irrational:

$$\sqrt{2} \text{ is not a rational number}$$

### Informal proof
The proof is straightforward and follows directly from two theorems:

1. `IRRATIONAL_SQRT_PRIME`: This theorem states that if $p$ is a prime number, then $\sqrt{p}$ is irrational.
2. `PRIME_2`: This theorem establishes that 2 is a prime number.

By applying `IRRATIONAL_SQRT_PRIME` with the fact that 2 is prime (from `PRIME_2`), we directly conclude that $\sqrt{2}$ is irrational.

The proof uses `SIMP_TAC` to simplify the goal using these two theorems, which is sufficient for the complete proof.

### Mathematical insight
This is a classic result in mathematics, often cited as the first proof of the existence of irrational numbers. The irrationality of $\sqrt{2}$ has historical significance dating back to ancient Greek mathematics, where it caused a crisis in the Pythagorean school which had assumed that all numbers could be expressed as ratios of integers.

While the HOL Light proof relies on more general results about irrationality of square roots of primes, the traditional proof is a proof by contradiction that shows if $\sqrt{2} = \frac{p}{q}$ where $p$ and $q$ are relatively prime integers, then both $p$ and $q$ must be even, which is a contradiction.

This theorem is fundamental in number theory and serves as a gateway to understanding irrational numbers more broadly.

### Dependencies
- **Theorems**:
  - `IRRATIONAL_SQRT_PRIME`: States that the square root of any prime number is irrational
  - `PRIME_2`: States that 2 is a prime number

### Porting notes
This theorem should be straightforward to port to other proof assistants. The main requirement is having corresponding theorems about irrationality of square roots of prime numbers and the primality of 2. Most proof assistants will have these theorems in their standard libraries, though the names and exact formulations may differ.

---

