# sqrt.ml

## Overview

Number of statements: 3

The file `sqrt.ml` proves the irrationality of $\sqrt{2}$ and related results. It builds upon the theories of prime numbers and floor function from `prime.ml` and `floor.ml`. The file formalizes theorems about square roots and their irrationality properties.


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
For all `n`, if the square root of `n` is rational, then there exists an `m` such that `n` equals `m` squared.

### Informal sketch
The proof proceeds as follows:
- Assume that `sqrt(n)` is rational, meaning it can be expressed as `p / q` where `p` and `q` are integers.
- Square both sides of the equation `sqrt(n) = p / q` to obtain `n = (p / q) pow 2`.
- Manipulate the equation `n = (p / q) pow 2`, where `p` and `q` are integers, to derive a contradiction if `n` is not a perfect square. Specifically, rewrite `n = (p/q)^2` as `n*q^2 = p^2`.
- From `rational(sqrt(&n))`, one deduces `?m. n = m EXP 2`.

### Mathematical insight
This theorem formalizes the condition under which the square root of a number is rational: namely, if and only if the number is a perfect square. This generalizes the classic irrationality of `sqrt(2)` to all real positive `n`. It asserts that if `sqrt(n)` is rational, then `n` is a perfect square.

### Dependencies
- Definitions: `rational`
- Theorems: `SQRT_POW_2`, `REAL_POS`, `REAL_POW2_ABS`, `integer`, `REAL_ABS_DIV`, `REAL_FIELD p = (n / m) pow 2 ==> ~(m = &0) ==> m pow 2 * p = n pow 2`, `REAL_ABS_ZERO`, `REAL_OF_NUM_POW`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_EQ`, `EXP_MULT_EXISTS`.


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
For all `p`, if `p` is prime, then the square root of `p` is not rational.

### Informal sketch
The proof proceeds as follows:
- First, the contrapositive of the statement `!p. prime p ==> ~rational(sqrt(&p))` is considered.
- Then, assume that `rational(sqrt(&p))` holds for some `p` and derive that `~ prime p`.
- The assumption `rational(sqrt(&p))` is instantiated to obtain the existence of `m` and `n` such that `sqrt(&p) = m / n`, where `m` and `n` are coprime. This uses the theorem `IRRATIONAL_SQRT_NONSQUARE`.
- Substitute `sqrt(&p)` in `rational(sqrt(&p))` with `m/n`.
- Rewrite using `PRIME_EXP` (definition of prime numbers in terms of exponential valuations) and `ARITH_EQ` (`a = a <=> T`).

### Mathematical insight
This theorem states that the square root of any prime number is irrational. This is a fundamental result in number theory. It highlights the relationship between primality and rationality, and the relative density of rational and irrational numbers.

### Dependencies
- `prime`
- `rational`
- `sqrt`
- `CONTRAPOS_THM`
- `IRRATIONAL_SQRT_NONSQUARE`
- `PRIME_EXP`
- `ARITH_EQ`


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
It is not the case that the square root of 2 is a rational number.

### Informal sketch
To prove `~rational(sqrt(&2))`:
- The proof uses `SIMP_TAC` which applies simplification rules.
- The simplification rules are derived from `IRRATIONAL_SQRT_PRIME` and `PRIME_2`.
- `IRRATIONAL_SQRT_PRIME` generalizes the irrationality of square roots to prime numbers, stating that for any prime number *p*, the square root of *p* is not rational.
- `PRIME_2` proves that 2 is a prime number.
- Therefore, by instantiating `IRRATIONAL_SQRT_PRIME` with `PRIME_2`, we conclude that the square root of 2 is not rational.

### Mathematical insight
This theorem establishes a fundamental property of the square root of 2, namely its irrationality. This result is a classic and important result in number theory, often used as an example of proof by contradiction. It demonstrates that not all numbers can be expressed as a ratio of two integers.

### Dependencies
- Theorems: `IRRATIONAL_SQRT_PRIME`, `PRIME_2`


---

