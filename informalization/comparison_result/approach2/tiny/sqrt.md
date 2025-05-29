MODEL_A="deepseek/deepseek-chat-v3-0324"
MODEL_B="anthropic/claude-3.7-sonnet"
MODEL_C="openai/gpt-4.1-mini"

# sqrt.ml

## Overview

Number of statements: 3

The file `sqrt.ml` formalizes the irrationality of \(\sqrt{2}\) and extends this result to more general cases involving square roots of natural numbers. It relies on imported results from `prime.ml` and `floor.ml` to establish properties of primes, divisibility, and floor functions. Key content includes proofs of irrationality for \(\sqrt{n}\) when \(n\) is not a perfect square, leveraging number-theoretic reasoning. The file serves as a foundational component for results on irrational numbers in the HOL Light library.

## IRRATIONAL_SQRT_NONSQUARE

### Name of formal statement
IRRATIONAL_SQRT_NONSQUARE

### Type of the formal statement
theorem

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
For any natural number \( n \), if \( \sqrt{n} \) is rational, then there exists a natural number \( m \) such that \( n = m^2 \).

In other words, the square root of a natural number is rational if and only if that number is a perfect square.

### Informal proof
1. **Assume rationality**: Suppose \( \sqrt{n} \) is rational. By definition, this means 
   \[
   \sqrt{n} = \frac{p}{q}
   \]
   for integers \( p \), \( q \) with \( q \neq 0 \).

2. **Square both sides**: Squaring yields
   \[
   n = \frac{p^2}{q^2}.
   \]

3. **Clear denominators**: Multiplying both sides by \( q^2 \) gives
   \[
   n q^2 = p^2.
   \]

4. **Apply number-theoretic lemma**: The equality \( n q^2 = p^2 \) implies that \( p^2 \) factors as \( n \) times a perfect square (\( q^2 \)). Using the lemma `EXP_MULT_EXISTS`—which states that if \( m^k \cdot n = p^k \) with \( m \neq 0 \), then \( n \) is itself a perfect \( k \)-th power—one concludes that \( n \) must be a perfect square. 

5. **Conclusion**: Therefore, there exists some natural number \( m \) such that
   \[
   n = m^2.
   \]

### Mathematical insight
This theorem generalizes a classical number-theoretic fact: a natural number has a rational square root if and only if it is a perfect square. The contrapositive tells us that the square root of any non-square natural number is irrational, a key early example being the irrationality of \(\sqrt{2}\).

The proof method exemplifies a common approach in proving irrationality results: assuming rationality, expressing the quantity in lowest terms, and deriving integral divisibility constraints, which then yield structural restrictions on the original number.

Notably, this theorem highlights the interplay between algebraic manipulation of rational expressions and number-theoretic reasoning about perfect powers.

### Dependencies
- **Theorems**:
  - `EXP_MULT_EXISTS`: Given \( m^k \cdot n = p^k \) with \( m \neq 0 \), there exists \( q \) such that \( n = q^k \). This is critical for concluding \( n \) is a perfect square.
- **Definitions**:
  - Rationality of real numbers as expressible by integer quotients with nonzero denominator.

### Porting notes
- **Rationality definition**: Ensure the target system defines rational numbers equivalently to HOL Light—typically as real numbers that equal the quotient of two integers with non-zero denominator.
- **Number theory support**: The receiving system must support or be extended with lemmas characterizing perfect powers like `EXP_MULT_EXISTS`.
- **Real number operations**: The proof uses real arithmetic, notably the properties of the square root function and squaring, so analogous concepts must be present.

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
For every prime number \( p \), the square root of \( p \) is irrational: 
\[
\forall p.\ \text{prime}(p) \implies \neg \text{rational}(\sqrt{p}).
\]

- \(\text{prime}(p)\): \( p \) is a prime number.
- \(\text{rational}(x)\): \( x \) is a rational number (expressible as a fraction of two integers).
- \(\sqrt{p}\): The real square root of \( p \).

### Informal proof
The proof proceeds by contraposition:

1. **Contrapositive formulation**: Instead of proving 
\[
\text{prime}(p) \implies \neg \text{rational}(\sqrt{p}),
\]
we prove the contrapositive:
\[
\text{rational}(\sqrt{p}) \implies \neg \text{prime}(p).
\]

2. **Rational square roots imply perfect squares**:  
By the theorem `IRRATIONAL_SQRT_NONSQUARE`, if \(\sqrt{p}\) is rational, then \( p \) is a perfect square. That is, there exists a natural number \( m \) such that:
\[
p = m^2.
\]

3. **Prime powers characterization**:  
The theorem `PRIME_EXP` states that for any prime \( p \) and integer exponent \( n \), \( p^n \) is prime if and only if \( p \) is prime and \( n = 1 \).

4. **Contradiction for \( p = m^2 \)**:  
Since \( p = m^2 = m^2 \), this is a square power with exponent \( 2 \neq 1 \). According to `PRIME_EXP`, \( p \) cannot be prime if it is a perfect square other than to the power 1.

Therefore, if \(\sqrt{p}\) is rational, then \( p \) is not prime, completing the proof by contraposition.

### Mathematical insight
This theorem confirms a classical number-theoretic fact: the square roots of prime numbers are irrational. The key idea is that primes cannot be perfect squares, since their prime-power decomposition must have exponent 1 for primality.

More broadly, the theorem fits into the general principle that the square root of a natural number is rational if and only if the number is a perfect square.

### Dependencies
- **Theorems**:
  - `IRRATIONAL_SQRT_NONSQUARE`: A rational square root implies the number is a perfect square.
  - `PRIME_EXP`: Characterizes primality of prime powers — only when the exponent is 1.

### Porting notes
- The proof relies on contraposition and fundamental properties of primes and perfect squares, which are standard concepts in most formal systems.
- When porting, ensure consistent definitions of `prime`, `rational`, and the square root function.
- The proof uses only elementary reasoning, making it straightforward to reconstruct in target assistants like Lean4.

---

## IRRATIONAL_SQRT_2

### Name of formal statement
IRRATIONAL_SQRT_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IRRATIONAL_SQRT_2 = prove
 (`~rational(sqrt(&2))`,
  SIMP_TAC[IRRATIONAL_SQRT_PRIME; PRIME_2]);;
```

### Informal statement
The square root of 2 is irrational. Formally,  
\[
\neg \text{rational}(\sqrt{2})
\]

where \(\text{rational}(x)\) means \(x\) is a rational number, and \(\sqrt{2}\) is the unique positive real number whose square is 2.

### Informal proof
The proof follows directly from a general theorem stating that the square root of any prime number is irrational. Specifically:

1. The theorem `IRRATIONAL_SQRT_PRIME` establishes that for any prime \(p\), \(\sqrt{p}\) is irrational.

2. Since 2 is prime (as stated by the theorem `PRIME_2`), it follows that \(\sqrt{2}\) is irrational.

Therefore, by instantiating `IRRATIONAL_SQRT_PRIME` with \(p = 2\), we conclude \(\sqrt{2}\) is irrational.

### Mathematical insight
- This classical result from number theory shows that not all real numbers can be expressed as fractions.
- The irrationality of \(\sqrt{2}\) was historically significant, revealing the existence of numbers outside the rationals and motivating the development of real analysis.
- The usual proof involves contradiction assuming \(\sqrt{2} = \frac{a}{b}\) with coprime integers \(a,b\), leading to a prime factorization contradiction.
- HOL Light's formalization leverages a general result about primes, avoiding explicit number-theoretic arguments.

### Dependencies
- Theorems:  
  - `PRIME_2`: Establishes that 2 is a prime number.  
  - `IRRATIONAL_SQRT_PRIME`: States that for every prime \(p\), \(\sqrt{p}\) is irrational.

### Porting notes
- The theorem is straightforward to port to other proof assistants with number theory libraries.
- Definitions of rational numbers and square roots should align with those in the source theorem.
- The proof automation may vary; in HOL Light, simplification tactics directly derive the theorem from its dependencies.
- Confirm that analogous general theorems (or their equivalents) exist in the target system or implement the classical prime-square-root irrationality proof.

---

