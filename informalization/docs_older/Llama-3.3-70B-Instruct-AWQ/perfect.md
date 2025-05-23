# perfect.ml

## Overview

Number of statements: 18

The `perfect.ml` file contains formalizations of perfect number theorems. It builds upon the `prime.ml` library, suggesting a connection to primality and number theory. The file's purpose is to define and prove properties related to perfect numbers, contributing to the larger library's coverage of number theoretic concepts. Its content is focused on establishing a formal foundation for perfect numbers within the HOL Light system.

## sigma

### Name of formal statement
sigma

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let sigma = new_definition
 `sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)`;;
```

### Informal statement
The function `sigma(n)` is defined as follows: if `n` equals 0, then `sigma(n)` equals 0; otherwise, `sigma(n)` is the sum of all divisors `d` of `n`, where each divisor `d` contributes its value to the sum.

### Informal sketch
* The definition of `sigma(n)` involves a conditional statement to handle the base case when `n` is 0.
* For non-zero `n`, the definition uses a summation `nsum` over the set of divisors `d` of `n`.
* Each divisor `d` in this set contributes its own value `i` to the sum, effectively computing the sum of all divisors of `n`.

### Mathematical insight
The `sigma` function computes the sum of divisors of a given number `n`, which is a fundamental concept in number theory. This function is crucial in the study of perfect numbers, as a perfect number is equal to the sum of its proper divisors (excluding the number itself).

### Dependencies
* `nsum`
* `divides`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles conditional statements, summations, and divisor functions. Specifically, ensure that the `nsum` function and the `divides` relation are properly defined and imported in the target system. Additionally, consider the handling of binders and lambda expressions, as the `\i. i` term may require special treatment.

---

## perfect

### Name of formal statement
perfect

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let perfect = new_definition
 `perfect n <=> ~(n = 0) /\ sigma(n) = 2 * n`;;
```

### Informal statement
The `perfect` predicate is defined for a number `n` such that `n` is not equal to 0 and the sum of divisors of `n` (denoted by `sigma(n)`) is equal to twice `n`.

### Informal sketch
* The definition of `perfect` relies on two main conditions: 
  - `n` must be non-zero, expressed as `~(n = 0)`.
  - The sum of divisors of `n`, `sigma(n)`, must be exactly twice the value of `n`, or `sigma(n) = 2 * n`.
* This definition does not explicitly outline a proof structure but rather sets a criterion for what constitutes a perfect number.
* The key concept here involves the `sigma` function, which represents the sum of divisors of a number, including 1 and the number itself.

### Mathematical insight
The concept of a perfect number is a classic mathematical idea where a number is equal to the sum of its proper divisors (excluding the number itself). This definition captures that essence by equating the sum of all divisors (`sigma(n)`) to twice the number (`2 * n`), effectively making the number equal to the sum of its proper divisors when the number itself is subtracted from `sigma(n)`.

### Dependencies
- `sigma` (the sum of divisors function)

### Porting notes
When translating this definition into another proof assistant, ensure that the `sigma` function is properly defined or imported, as it is crucial for the definition of `perfect`. Note that different systems may handle the definition of such predicates slightly differently, especially regarding the use of negation (`~`) and the representation of the `sigma` function. Additionally, consider how the target system handles arithmetic operations and comparisons, as these are integral to the definition.

---

## ODD_POW2_MINUS1

### Name of formal statement
ODD_POW2_MINUS1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODD_POW2_MINUS1 = prove
 (`!k. ~(k = 0) ==> ODD(2 EXP k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EVEN(2 EXP k) <=> EVEN((2 EXP k - 1) + 1)` MP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `k = k - 1 + 1 <=> ~(k = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH];
    ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD; EVEN_EXP; ARITH]]);;
```

### Informal statement
For all non-zero natural numbers `k`, the number `2` raised to the power of `k` minus `1` is odd.

### Informal sketch
* The proof starts by assuming `k` is not equal to `0`.
* It then uses the `SUBGOAL_THEN` tactic to establish the equivalence `EVEN(2 EXP k) <=> EVEN((2 EXP k - 1) + 1)`.
* The proof proceeds by considering two cases:
  + The first case applies `AP_TERM_TAC` and then simplifies using `ARITH_RULE` and `REWRITE_TAC` to handle the arithmetic properties.
  + The second case uses `ASM_REWRITE_TAC` to apply properties of even numbers, including `GSYM NOT_EVEN`, `EVEN_ADD`, `EVEN_EXP`, and `ARITH`.
* The overall strategy involves using properties of even and odd numbers, as well as arithmetic manipulations, to establish the oddness of `2 EXP k - 1` for non-zero `k`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of powers of `2` minus `1`, which are related to Mersenne numbers. The oddness of these numbers has implications in number theory, particularly in the study of prime numbers and perfect numbers. The proof showcases how basic properties of arithmetic and parity can be used to derive significant results.

### Dependencies
* `ODD`
* `EVEN`
* `EXP`
* `ARITH_RULE`
* `NOT_EVEN`
* `EVEN_ADD`
* `EVEN_EXP`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles arithmetic and parity properties. Specifically, ensure that the target system has equivalent definitions for `ODD`, `EVEN`, and arithmetic operations, as well as similar tactics for manipulating these properties. Additionally, be mindful of how the `SUBGOAL_THEN` and `ASM_REWRITE_TAC` tactics are handled, as their direct equivalents may not exist in other systems.

---

## EVEN_ODD_DECOMP

### Name of formal statement
EVEN_ODD_DECOMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EVEN_ODD_DECOMP = prove
 (`!n. ~(n = 0) ==> ?r s. ODD s /\ n = 2 EXP r * s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  MP_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THENL
   [DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[MULT_EQ_0; ARITH; ARITH_RULE `m < 2 * m <=> ~(m = 0)`] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `s:num` THEN DISCH_THEN(X_CHOOSE_TAC `r:num`) THEN
    EXISTS_TAC `SUC r` THEN ASM_REWRITE_TAC[EXP; GSYM MULT_ASSOC];
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[EXP; MULT_CLAUSES] THEN MESON_TAC[]])
```

### Informal statement
For all non-zero natural numbers `n`, there exist natural numbers `r` and `s` such that `s` is odd and `n` is equal to `2` raised to the power of `r`, multiplied by `s`.

### Informal sketch
* The proof starts by considering an arbitrary non-zero natural number `n`.
* It then applies the `EVEN_OR_ODD` theorem to `n`, which states that any non-zero natural number is either even or odd.
* The proof proceeds by cases:
  + If `n` is even, it is shown that `n` can be expressed as `2` raised to some power `r`, multiplied by an odd number `s`.
  + If `n` is odd, it is shown that `n` can be expressed as `2` raised to the power of `0`, multiplied by `n` itself (since `n` is odd).
* The `MATCH_MP_TAC` and `MP_TAC` tactics are used to apply the `num_WF` and `EVEN_OR_ODD` theorems, respectively.
* The `DISCH_THEN` and `X_CHOOSE_THEN` tactics are used to handle the existential quantifiers and choose witnesses for `r` and `s`.
* The `ASM_CASES_TAC` and `ASM_REWRITE_TAC` tactics are used to handle the case analysis and simplify the expressions.

### Mathematical insight
This theorem provides a decomposition of non-zero natural numbers into a product of a power of `2` and an odd number. This decomposition is useful in number theory and can be used to prove other results about natural numbers.

### Dependencies
* Theorems:
  + `EVEN_OR_ODD`
  + `num_WF`
  + `MULT_EQ_0`
  + `ARITH`
  + `ARITH_RULE`
  + `MONO_EXISTS`
  + `SWAP_EXISTS_THM`
* Definitions:
  + `EVEN_EXISTS`
  + `ODD_EXISTS`
  + `EXP`
  + `MULT_ASSOC`
  + `GSYM`
  + `MULT_CLAUSES`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `MATCH_MP_TAC` and `MP_TAC` tactics are replaced with the corresponding tactics in the target system. Additionally, the `DISCH_THEN` and `X_CHOOSE_THEN` tactics may need to be replaced with equivalent tactics that handle existential quantifiers and witness selection. The `ASM_CASES_TAC` and `ASM_REWRITE_TAC` tactics may also need to be replaced with equivalent tactics that handle case analysis and expression simplification.

---

## FINITE_DIVISORS

### Name of formal statement
FINITE_DIVISORS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE])
```

### Informal statement
For all non-zero natural numbers $n$, the set of divisors of $n$ is finite.

### Informal sketch
* The proof starts by assuming a non-zero natural number $n$.
* It then constructs a set containing all divisors $d$ of $n$.
* The key insight is to show that this set of divisors is a subset of the set of numbers less than or equal to $n$, which is known to be finite.
* The `FINITE_SUBSET` theorem is used to establish that the set of divisors is finite because it is a subset of a finite set.
* The `DIVIDES_LE` property is crucial in establishing the subset relationship, as it implies that any divisor $d$ of $n$ must be less than or equal to $n$.

### Mathematical insight
This theorem is important because it establishes a fundamental property of divisibility in number theory, namely that the number of divisors of any non-zero natural number is finite. This property has far-reaching implications in many areas of mathematics, including number theory, algebra, and combinatorics.

### Dependencies
* Theorems:
  + `FINITE_SUBSET`
  + `FINITE_NUMSEG_LE`
  + `DIVIDES_LE`
* Definitions:
  + `divides`
  + `FINITE`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how each system handles finite sets and subset relationships. The `FINITE_SUBSET` theorem may need to be restated or re-proved in the target system. Additionally, the `DIVIDES_LE` property may require a custom proof or be part of a standard library. Be mindful of the binder syntax and automation capabilities of the target system, as these may differ from HOL Light.

---

## MULT_EQ_COPRIME

### Name of formal statement
MULT_EQ_COPRIME

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let MULT_EQ_COPRIME = prove
 (`!a b x y. a * b = x * y /\ coprime(a,x)
             ==> ?d. y = a * d /\ b = x * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `x:num`; `y:num`] COPRIME_DIVPROD) THEN
  MP_TAC(SPECL [`x:num`; `a:num`; `b:num`] COPRIME_DIVPROD) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; COPRIME_SYM];
    REWRITE_TAC[divides] THEN STRIP_TAC]) THEN
  UNDISCH_TAC `a * b = x * y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
    `(a * x * u = x * a * v) <=> (a * x) * u = (a * x) * v`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0] THEN ASM_MESON_TAC[])
```

### Informal statement
For all natural numbers `a`, `b`, `x`, and `y`, if `a * b` equals `x * y` and `a` is coprime with `x`, then there exists a natural number `d` such that `y` equals `a * d` and `b` equals `x * d`.

### Informal sketch
* Start by assuming `a * b = x * y` and `coprime(a, x)`.
* Utilize the `COPRIME_DIVPROD` theorem to derive relationships between `a`, `x`, `y`, and `b` based on their coprime nature and the equality of the products.
* Apply logical deductions and properties of arithmetic operations (e.g., `DIVIDES_REFL`, `DIVIDES_RMUL`, `COPRIME_SYM`) to establish the existence of `d`.
* Leverage `ARITH_RULE` to simplify and rearrange equations involving `a`, `x`, `y`, and `d`, ultimately showing that `y = a * d` and `b = x * d`.
* The proof involves strategic use of `REPEAT STRIP_TAC`, `MP_TAC`, and `ASM_MESON_TAC` to manage assumptions and derive conclusions.

### Mathematical insight
This theorem provides insight into the relationship between coprime numbers and their products, specifically how the equality of two products can be related to the existence of a common factor. It highlights the importance of coprimality in number theory and its implications for factorization and divisibility.

### Dependencies
#### Theorems
* `COPRIME_DIVPROD`
* `DIVIDES_REFL`
* `DIVIDES_RMUL`
* `COPRIME_SYM`
* `ARITH_RULE`
* `EQ_MULT_LCANCEL`
* `MULT_EQ_0`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how coprimality and divisibility are defined and handled, as these concepts may be represented differently. Additionally, the strategic use of tactics like `REPEAT STRIP_TAC` and `MP_TAC` may need to be adapted to the target system's proof scripting language.

---

## COPRIME_ODD_POW2

### Name of formal statement
COPRIME_ODD_POW2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COPRIME_ODD_POW2 = prove
 (`!k n. ODD(n) ==> coprime(2 EXP k,n)`,
  SIMP_TAC[coprime; PRIME_2; DIVIDES_PRIMEPOW] THEN REWRITE_TAC[divides] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ODD_MULT; ODD_EXP; ARITH])
```

### Informal statement
For all integers `k` and `n`, if `n` is odd, then `2` raised to the power of `k` is coprime with `n`.

### Informal sketch
* Start with the assumption that `n` is odd.
* Use the definition of `coprime` and the fact that `2` is a prime number (`PRIME_2`) to establish the relationship between `2` raised to the power of `k` and `n`.
* Apply the `DIVIDES_PRIMEPOW` theorem to analyze the divisibility of `n` by `2` raised to the power of `k`.
* Rewrite the `divides` relation and repeatedly strip away unnecessary assumptions.
* Utilize the fact that `n` is odd (`ODD n`) to simplify the expression.
* Apply the `ODD_MULT`, `ODD_EXP`, and `ARITH` theorems to further simplify and establish the coprimality.

### Mathematical insight
This theorem establishes that any power of `2` is coprime with any odd number. This result is fundamental in number theory, as it highlights the relationship between powers of `2` and odd numbers in terms of their greatest common divisor.

### Dependencies
* Theorems:
	+ `coprime`
	+ `PRIME_2`
	+ `DIVIDES_PRIMEPOW`
	+ `ODD_MULT`
	+ `ODD_EXP`
	+ `ARITH`
* Definitions:
	+ `ODD`
	+ `coprime`
	+ `divides`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of the `ODD` predicate and the `coprime` relation. Additionally, the `DIVIDES_PRIMEPOW` theorem may need to be reestablished or imported from a relevant library. The `SIMP_TAC` and `REWRITE_TAC` tactics may have equivalents in other systems, but their exact usage may vary.

---

## MULT_NSUM

### Name of formal statement
MULT_NSUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let MULT_NSUM = prove
 (`!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))`,
  SIMP_TAC[GSYM NSUM_NSUM_PRODUCT; NSUM_LMUL; NSUM_RMUL])
```

### Informal statement
For all sets `s` and `t`, if `s` is finite and `t` is finite, then the product of the natural sum of `f` over `s` and the natural sum of `g` over `t` is equal to the natural sum of the product of `f(x)` and `g(y)` over the set of all pairs `(x, y)` such that `x` is in `s` and `y` is in `t`.

### Informal sketch
* The proof starts by assuming `s` and `t` are finite sets.
* It then applies the `SIMP_TAC` tactic with a list of theorems (`GSYM NSUM_NSUM_PRODUCT`, `NSUM_LMUL`, `NSUM_RMUL`) to simplify the expression and establish the equality between the product of the sums and the sum of the products.
* The key idea is to use the properties of natural sums and the distributivity of multiplication over addition to transform the left-hand side into the right-hand side.

### Mathematical insight
This theorem provides a way to distribute the product of two sums over finite sets into a single sum over the Cartesian product of the sets. This is a fundamental property of summation and has numerous applications in mathematics, particularly in algebra and analysis. The theorem is important because it allows for the simplification of complex expressions involving sums and products.

### Dependencies
* `FINITE`
* `NSUM`
* `GSYM NSUM_NSUM_PRODUCT`
* `NSUM_LMUL`
* `NSUM_RMUL`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of finite sets, natural sums, and the `SIMP_TAC` tactic. The equivalent of `SIMP_TAC` may need to be used with a similar set of theorems to establish the desired equality. Additionally, the representation of finite sets and natural sums may differ between systems, requiring adjustments to the theorem statement and proof.

---

## SIGMA_0

### Name of formal statement
SIGMA_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_0 = prove
 (`sigma 0 = 0`,
  REWRITE_TAC[sigma]);;
```

### Informal statement
The theorem `SIGMA_0` states that the `sigma` function applied to `0` equals `0`.

### Informal sketch
* The proof of `SIGMA_0` involves using the `REWRITE_TAC` tactic with the `sigma` definition to establish the equality `sigma 0 = 0`.
* This step relies on the definition of the `sigma` function, which is used to rewrite the expression `sigma 0` to its equivalent value `0`.

### Mathematical insight
The `SIGMA_0` theorem provides a basic property of the `sigma` function, which is likely used as a foundation for further results involving this function. Understanding the behavior of `sigma` at `0` is essential for establishing more complex properties and theorems.

### Dependencies
* `sigma` definition

### Porting notes
When translating `SIGMA_0` into other proof assistants, ensure that the `sigma` function is defined and its properties are established accordingly. The `REWRITE_TAC` tactic may have an equivalent in other systems, such as `rewrite` in Coq or `simp` in Isabelle, which can be used to achieve the same rewriting step.

---

## SIGMA_1

### Name of formal statement
SIGMA_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_1 = prove
 (`sigma(1) = 1`,
  REWRITE_TAC[sigma; DIVIDES_ONE; SET_RULE `{d | d = 1} = {1}`] THEN
  REWRITE_TAC[ARITH; NSUM_SING])
```

### Informal statement
The theorem states that the sum of divisors of 1, denoted as `sigma(1)`, is equal to 1.

### Informal sketch
* The proof begins with the statement `sigma(1) = 1`, which is the claim to be proven.
* The `REWRITE_TAC` tactic is applied with the `sigma`, `DIVIDES_ONE`, and `SET_RULE `{d | d = 1} = {1}` theorems to rewrite the statement.
* Then, another `REWRITE_TAC` is applied with the `ARITH` and `NSUM_SING` theorems to further simplify the statement, ultimately proving the claim.
* The key idea is to use the definitions and properties of the `sigma` function, as well as basic arithmetic and set theory, to establish the equality.

### Mathematical insight
The theorem `SIGMA_1` provides a basic property of the `sigma` function, which is likely used as a building block for more complex results. The `sigma` function represents the sum of divisors of a number, and this theorem establishes a trivial but essential case.

### Dependencies
* Theorems:
  + `sigma`
  + `DIVIDES_ONE`
  + `SET_RULE `{d | d = 1} = {1}`
  + `ARITH`
  + `NSUM_SING`

### Porting notes
When porting this theorem to another proof assistant, ensure that the `sigma` function and the relevant theorems (`DIVIDES_ONE`, `SET_RULE`, `ARITH`, and `NSUM_SING`) are defined and available. The `REWRITE_TAC` tactic may need to be replaced with equivalent tactics or rewriting mechanisms in the target system. Additionally, the handling of arithmetic and set theory may differ between systems, requiring adjustments to the proof script.

---

## SIGMA_LBOUND

### Name of formal statement
SIGMA_LBOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_LBOUND = prove
 (`!n. 1 < n ==> n + 1 <= sigma(n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,n} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL]])
```

### Informal statement
For all natural numbers `n`, if `1` is less than `n`, then `n + 1` is less than or equal to the sum of divisors of `n`, denoted as `sigma(n)`.

### Informal sketch
* The proof starts by assuming `1 < n`, which implies `n` is not equal to `0`.
* It then rewrites `sigma(n)` using its definition and applies the transitive property of less than or equal to (`LE_TRANS`).
* The proof proceeds by showing two main points:
  + The sum of the first `n` natural numbers (`nsum {1,n} (\i. i)`) is equal to `n * (n + 1) / 2`, which is greater than or equal to `n + 1` for `n > 1`.
  + This sum is less than or equal to `sigma(n)` because it represents the sum of a subset of divisors of `n` (specifically, the set of all numbers from `1` to `n`), leveraging `NSUM_SUBSET_SIMPLE` and properties of divisors.

### Mathematical insight
This theorem provides a lower bound on the sum of divisors function `sigma(n)` for any `n > 1`, relating it to a simple arithmetic expression `n + 1`. This is useful in number theory for establishing properties of the divisor function and its behavior.

### Dependencies
* `ARITH_RULE`
* `sigma`
* `NSUM_CLAUSES`
* `FINITE_RULES`
* `IN_SING`
* `NOT_IN_EMPTY`
* `NSUM_SUBSET_SIMPLE`
* `FINITE_DIVISORS`
* `SUBSET`
* `IN_ELIM_THM`
* `DIVIDES_1`
* `DIVIDES_REFL`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how `nsum` (a summation over a finite set) and `sigma` (the sum of divisors) are defined and handled, as these may differ significantly between systems. Additionally, the use of `REPEAT STRIP_TAC` and other tacticals may need to be adapted, as the proof strategies and automation levels can vary between proof assistants.

---

## SIGMA_MULT

### Name of formal statement
SIGMA_MULT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_MULT = prove
 (`!a b. 1 < a /\ 1 < b ==> 1 + b + a * b <= sigma(a * b)`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,b,a*b} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x = a * b <=> a * b = 1 * x`] THEN
    ASM_REWRITE_TAC[EQ_MULT_RCANCEL] THEN
    REWRITE_TAC[MULT_CLAUSES; MULT_EQ_1] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; MULT_EQ_0] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL; DIVIDES_LMUL]])
```

### Informal statement
For all natural numbers $a$ and $b$ such that $1 < a$ and $1 < b$, it holds that $1 + b + a \cdot b \leq \sigma(a \cdot b)$, where $\sigma(n)$ denotes the sum of divisors of $n$.

### Informal sketch
* The proof starts by assuming $1 < a$ and $1 < b$, which implies $a \neq 0$ and $b \neq 0$.
* It then rewrites $\sigma(a \cdot b)$ using its definition and applies `LE_TRANS` to establish the inequality $1 + b + a \cdot b \leq \sigma(a \cdot b)$ by finding an intermediate value.
* The intermediate value is the sum of the elements in the set $\{1, b, a \cdot b\}$, which is shown to be less than or equal to $\sigma(a \cdot b)$ by `NSUM_SUBSET_SIMPLE`.
* Key steps involve simplifying expressions with `SIMP_TAC`, rewriting with `ASM_REWRITE_TAC`, and applying arithmetic properties with `ASM_ARITH_TAC`.
* The proof also uses `MATCH_MP_TAC` to apply relevant theorems, such as `ARITH_RULE` and `NSUM_SUBSET_SIMPLE`, to establish the required inequalities.

### Mathematical insight
This theorem provides a relationship between the sum of divisors function $\sigma(n)$ and the product of two numbers $a$ and $b$, both greater than 1. It shows that the sum of $1$, $b$, and the product $a \cdot b$ is less than or equal to the sum of divisors of $a \cdot b$. This kind of inequality can be useful in number theory, particularly in studying properties of the sum of divisors function and its relation to multiplication and divisibility.

### Dependencies
* Theorems:
  + `ARITH_RULE`
  + `NSUM_SUBSET_SIMPLE`
  + `LE_TRANS`
* Definitions:
  + `sigma`
  + `nsum`
* Other:
  + `FINITE_DIVISORS`
  + `DIVIDES_1`
  + `DIVIDES_REFL`
  + `DIVIDES_LMUL`
  + `MULT_EQ_0`
  + `MULT_EQ_1`
  + `EQ_MULT_RCANCEL`
  + `IN_INSERT`
  + `NOT_IN_EMPTY`
  + `SUBSET`
  + `IN_ELIM_THM`

---

## SIGMA_PRIME

### Name of formal statement
SIGMA_PRIME

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_PRIME = prove
 (`!p. prime(p) ==> sigma(p) = p + 1`,
  GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1; SIGMA_1; ARITH] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum {1,p} (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[prime; DIVIDES_1; DIVIDES_REFL];
    ASM_SIMP_TAC[NSUM_CLAUSES; IN_SING; FINITE_RULES; NOT_IN_EMPTY] THEN
    ARITH_TAC])
```

### Informal statement
For all `p`, if `p` is prime, then the sum of divisors of `p`, denoted as `sigma(p)`, is equal to `p + 1`.

### Informal sketch
* The proof starts by considering cases for `p = 0` and `p = 1`, using `PRIME_0`, `SIGMA_0`, `PRIME_1`, and `SIGMA_1` to handle these base cases.
* For prime `p`, it uses the definition of `sigma` and applies `EQ_TRANS` to establish the equality `sigma(p) = p + 1`.
* The proof involves showing that the sum of divisors of `p` (excluding `p` itself) is `1`, leveraging the fact that `p` is prime and thus only has `1` and itself as divisors.
* Key steps include using `MATCH_MP_TAC` with `EQ_TRANS`, and `EXISTS_TAC` to introduce the sum of divisors, followed by `CONJ_TAC` to split the proof into two parts: one for the sum of divisors being `1` and another for simplifying the expression using `NSUM_CLAUSES` and `ARITH_TAC`.

### Mathematical insight
This theorem provides insight into the property of the sum of divisors function, `sigma`, for prime numbers. It shows that for any prime `p`, the only divisors are `1` and `p` itself, leading to `sigma(p) = p + 1`. This is a fundamental property in number theory, highlighting the unique characteristic of primes in relation to their divisors.

### Dependencies
* Theorems:
  - `PRIME_0`
  - `PRIME_1`
  - `SIGMA_0`
  - `SIGMA_1`
  - `EXTENSION`
  - `IN_ELIM_THM`
  - `IN_INSERT`
  - `NOT_IN_EMPTY`
  - `NSUM_CLAUSES`
  - `IN_SING`
  - `FINITE_RULES`
* Definitions:
  - `prime`
  - `sigma`
  - `nsum`
  - `DIVIDES_1`
  - `DIVIDES_REFL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles quantifiers, case distinctions, and the application of theorems like `EQ_TRANS`. Additionally, the representation of the `sigma` function and the handling of arithmetic properties may differ, requiring careful consideration of the target system's libraries and tactics for arithmetic and number theory.

---

## SIGMA_PRIME_EQ

### Name of formal statement
SIGMA_PRIME_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_PRIME_EQ = prove
 (`!p. prime(p) <=> sigma(p) = p + 1`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[SIGMA_PRIME] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[prime; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[SIGMA_1; ARITH] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; divides; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`a:num`; `b:num`] SIGMA_MULT) THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[MULT_EQ_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a = a * b <=> a * b = a * 1`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ARITH_TAC)
```

### Informal statement
For all natural numbers `p`, `p` is prime if and only if the sum of divisors of `p`, denoted as `sigma(p)`, equals `p + 1`.

### Informal sketch
* The proof starts by assuming `p` is a natural number and aims to prove the equivalence `prime(p) <=> sigma(p) = p + 1`.
* It first considers the case when `p = 1`, handling it separately due to its unique properties regarding primality and divisors.
* For `p != 1`, it applies various logical transformations and properties of prime numbers, divisors, and the `sigma` function to establish the equivalence.
* Key steps involve using the definition of `prime`, properties of `sigma` (notably `SIGMA_PRIME`), and handling cases for when potential divisors `a` and `b` are zero or non-zero.
* The proof leverages the `SIGMA_MULT` property to reason about the sum of divisors for composite numbers and applies arithmetic reasoning to conclude the proof.

### Mathematical insight
This theorem provides a fundamental characterization of prime numbers in terms of the sum of their divisors, offering a unique perspective on the nature of primality. It is crucial in number theory, connecting basic properties of numbers (like being prime) with more complex functions (like the sum of divisors), and is likely used in various proofs involving prime numbers and their properties.

### Dependencies
#### Theorems and Definitions
- `SIGMA_PRIME`
- `prime`
- `SIGMA_MULT`
- `DE_MORGAN_THM`
- `CONTRAPOS_THM`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `divides`
- `MULT_CLAUSES`
- `SIGMA_0`
- `SIGMA_1`
- `MULT_EQ_1`
- `EQ_MULT_LCANCEL`
- `ARITH_RULE` 

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles quantifiers, especially when applying tactics like `GEN_TAC` or `EXISTS_TAC`. Additionally, ensure that the definitions of `prime`, `sigma`, and related theorems like `SIGMA_PRIME` and `SIGMA_MULT` are correctly ported, as their precise formulations are crucial for the validity of the proof. Differences in arithmetic handling and the application of `ARITH_TAC` or similar tactics should also be carefully considered.

---

## SIGMA_POW2

### Name of formal statement
SIGMA_POW2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_POW2 = prove
 (`!k. sigma(2 EXP k) = 2 EXP (k + 1) - 1`,
  GEN_TAC THEN REWRITE_TAC[sigma; EXP_EQ_0; ARITH] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {2 EXP i | i <= k} (\i. i)` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2; EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `x + 1 = y ==> x = y - 1`) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [REWRITE_TAC[SET_RULE `{2 EXP i | i = 0} = {2 EXP 0}`] THEN
    REWRITE_TAC[ARITH; NSUM_SING];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i = SUC k \/ i <= k} =
    (2 EXP (SUC k)) INSERT {2 EXP i | i <= k}`] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i <= k} = IMAGE (\i. 2 EXP i) {i | i <= k}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[IN_IMAGE; GSYM LE_ANTISYM; LE_EXP; ARITH] THEN
  REWRITE_TAC[LE_ANTISYM; IN_ELIM_THM; UNWIND_THM1] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[EXP; EXP_ADD; ARITH] THEN ARITH_TAC)
```

### Informal statement
For all natural numbers `k`, the sum of all divisors of `2` raised to the power of `k` is equal to `2` raised to the power of `k + 1` minus `1`.

### Informal sketch
* The proof starts with a generalization over `k` using `GEN_TAC`.
* It then applies `REWRITE_TAC` with `sigma`, `EXP_EQ_0`, and `ARITH` to transform the `sigma` function.
* The proof uses `MATCH_MP_TAC` with `EQ_TRANS` to establish an equality.
* It introduces a summation over the set `{2 EXP i | i <= k}` using `EXISTS_TAC` and `nsum`.
* The proof proceeds by induction on `k` using `INDUCT_TAC`.
* In the base case, it simplifies the summation using `NSUM_SING`.
* In the inductive step, it uses `REWRITE_TAC` with `SET_RULE` to transform the set `{2 EXP i | i = SUC k \/ i <= k}`.
* The proof then applies `SIMP_TAC` with various theorems to simplify the expression.
* Finally, it uses `ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem provides a formula for the sum of divisors of powers of `2`, which is a fundamental result in number theory. The proof involves a combination of algebraic manipulations, induction, and properties of summations.

### Dependencies
#### Theorems
* `sigma`
* `EXP_EQ_0`
* `ARITH`
* `EQ_TRANS`
* `DIVIDES_PRIMEPOW`
* `PRIME_2`
* `EXTENSION`
* `IN_ELIM_THM`
* `NSUM_CLAUSES`
* `FINITE_IMAGE`
* `FINITE_NUMSEG_LE`
* `LE_ANTISYM`
* `UNWIND_THM1`
* `EXP_ADD`
#### Definitions
* `nsum`
* `sigma`
* `EXP` 
#### Axioms
* `ARITH_RULE`

---

## SIGMA_MULTIPLICATIVE

### Name of formal statement
SIGMA_MULTIPLICATIVE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIGMA_MULTIPLICATIVE = prove
 (`!a b. coprime(a,b) ==> sigma(a * b) = sigma(a) * sigma(b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma; MULT_EQ_0] THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; MULT_NSUM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `nsum (IMAGE (\(x,y). x * y)
         {x,y | x divides a /\ y divides b}) (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> c /\ a /\ b`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    X_GEN_TAC `n:num` THEN EQ_TAC THEN REWRITE_TAC[DIVISION_DECOMP] THEN
    REWRITE_TAC[divides] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MULT_AC];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) NSUM_IMAGE (lhand w))) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:num`; `x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (is_var o rand o concl))) THEN
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_MESON_TAC[COPRIME_DIVISORS; COPRIME_SYM; COPRIME_DIVPROD;
                DIVIDES_RMUL; DIVIDES_REFL; MULT_SYM])
```

### Informal statement
For all natural numbers `a` and `b`, if `a` and `b` are coprime, then the `sigma` function of their product `a * b` is equal to the product of the `sigma` function applied to `a` and the `sigma` function applied to `b`, i.e., `sigma(a * b) = sigma(a) * sigma(b)`.

### Informal sketch
* The proof starts by considering cases where either `a` or `b` is `0`, using `ASM_CASES_TAC` to handle these base cases and applying `SIGMA_0` and `MULT_CLAUSES` to simplify.
* It then proceeds to use `DISCH_TAC` and `ASM_REWRITE_TAC` to apply definitions and properties of `sigma` and `coprime` numbers.
* The proof involves using `MATCH_MP_TAC EQ_TRANS` to establish an equality through a series of steps, including applying `NSUM_IMAGE` and manipulating terms to show the desired relationship between `sigma(a * b)` and `sigma(a) * sigma(b)`.
* Key steps involve using `CONJ_TAC` to break down the proof into manageable parts, applying `AP_THM_TAC` and `AP_TERM_TAC` to handle function applications, and `MESON_TAC` to derive conclusions from given premises, leveraging properties like `MULT_AC` and `COPRIME_DIVISORS`.

### Mathematical insight
The `SIGMA_MULTIPLICATIVE` theorem is crucial because it establishes a fundamental property of the `sigma` function, which counts the number of divisors of a number. This multiplicativity property, applicable when the arguments are coprime, is essential in number theory for various applications, including the study of arithmetic functions and their behavior under multiplication. It reflects the intuitive idea that when combining two numbers with no common factors, the number of divisors of their product can be determined by multiplying the number of divisors of each.

### Dependencies
* Theorems:
  + `SIGMA_0`
  + `MULT_CLAUSES`
  + `FINITE_DIVISORS`
  + `MULT_NSUM`
  + `IN_ELIM_THM`
  + `EQ_TRANS`
  + `NSUM_IMAGE`
  + `COPRIME_DIVISORS`
  + `COPRIME_SYM`
  + `COPRIME_DIVPROD`
  + `DIVIDES_RMUL`
  + `DIVIDES_REFL`
  + `MULT_SYM`
* Definitions:
  + `sigma`
  + `coprime`
  + `divides`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles arithmetic functions, coprimality, and the `sigma` function. Note that the `sigma` function and its properties might need to be defined or imported from a library. Additionally, the tactic scripts may vary significantly between systems, so understanding the mathematical structure of the proof will be crucial for successful translation. Be prepared to adapt the use of `MATCH_MP_TAC`, `CONJ_TAC`, and other tactics to the target system's tactic language and proof assistant's strengths.

---

## PERFECT_EUCLID

### Name of formal statement
PERFECT_EUCLID

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERFECT_EUCLID = prove
 (`!k. prime(2 EXP k - 1) ==> perfect(2 EXP (k - 1) * (2 EXP k - 1))`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH; PRIME_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `coprime(2 EXP (k - 1),2 EXP k - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC COPRIME_ODD_POW2 THEN ASM_SIMP_TAC[ODD_POW2_MINUS1];
    ALL_TAC] THEN
  ASM_SIMP_TAC[perfect; SIGMA_MULTIPLICATIVE; SIGMA_PRIME; SIGMA_POW2] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 + 1 = k`; EXP_EQ_0;
               MULT_EQ_0; ARITH] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[MULT_ASSOC] THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC)
```

### Informal statement
For all natural numbers `k`, if `2` raised to the power of `k` minus `1` is prime, then `2` raised to the power of `k-1` times `2` raised to the power of `k` minus `1` is a perfect number.

### Informal sketch
* The proof starts by considering the case when `k` equals `0` and then proceeds to handle the case when `k` is not equal to `0`.
* It assumes `coprime(2 EXP (k - 1), 2 EXP k - 1)` and uses `COPRIME_ODD_POW2` to simplify.
* The proof then applies various simplification tactics, including `ASM_SIMP_TAC` with `perfect`, `SIGMA_MULTIPLICATIVE`, `SIGMA_PRIME`, and `SIGMA_POW2`, to establish the relationship between the terms.
* Key steps involve using `CONJ_TAC` to split the goal into two parts and `REWRITE_TAC` with `MULT_ASSOC` and `MULT_SYM` to rearrange terms.
* The proof also uses `AP_TERM_TAC` and `UNDISCH_TAC` to manage assumptions and `ARITH_TAC` for arithmetic reasoning.

### Mathematical insight
This theorem relates to the properties of perfect numbers, which are equal to the sum of their proper divisors. The condition involving `2` raised to the power of `k` minus `1` being prime is significant because it connects to the definition of Mersenne primes and their role in constructing perfect numbers.

### Dependencies
* `prime`
* `perfect`
* `coprime`
* `COPRIME_ODD_POW2`
* `SIGMA_MULTIPLICATIVE`
* `SIGMA_PRIME`
* `SIGMA_POW2`
* `PRIME_0`
* `ARITH`
* `EXP_EQ_0`
* `MULT_EQ_0`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of arithmetic and the properties of prime and perfect numbers. The use of `GEN_TAC`, `ASM_CASES_TAC`, and `SUBGOAL_THEN` may require equivalent tactics in the target system. Additionally, the `COPRIME_ODD_POW2` and other `SIGMA` properties might need to be defined or imported from relevant libraries in the target proof assistant.

---

## PERFECT_EULER

### Name of formal statement
PERFECT_EULER

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERFECT_EULER = prove
 (`!n. EVEN(n) /\ perfect(n)
       ==> ?k. prime(2 EXP k - 1) /\ n = 2 EXP (k - 1) * (2 EXP k - 1)`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` EVEN_ODD_DECOMP) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[perfect]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; GSYM NOT_EVEN] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[EVEN_EXP; EVEN_MULT; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[perfect] THEN
  ASM_SIMP_TAC[SIGMA_MULTIPLICATIVE; SIGMA_POW2;
               COPRIME_ODD_POW2; GSYM NOT_EVEN] THEN
  DISCH_TAC THEN EXISTS_TAC `r + 1` THEN
  REWRITE_TAC[ADD_SUB; EQ_MULT_LCANCEL] THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_eq o concl)) THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); ADD1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] MULT_EQ_COPRIME)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_ODD_POW2 THEN
    SIMP_TAC[ODD_POW2_MINUS1; ADD_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THENL
   [ASM_MESON_TAC[EVEN]; ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_PRIME_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    MATCH_MP_TAC(GSYM SUB_ADD) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`2 EXP (r + 1) - 1`; `d:num`] SIGMA_MULT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ ~b ==> (a ==> b) ==> c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 EXP 1 < a ==> 1 < a - 1`) THEN
    REWRITE_TAC[LT_EXP; ARITH] THEN
    UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`~(d = 0)`; `~(d = 1)`] THEN ARITH_TAC;
    REWRITE_TAC[NOT_LE] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE `1 * d < x * d ==> x * d < 1 + d + x * d - d`) THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
    MATCH_MP_TAC(ARITH_RULE `2 EXP 0 < a ==> 1 < a`) THEN
    REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC])
```

### Informal statement
For all natural numbers `n`, if `n` is even and perfect, then there exists a natural number `k` such that `2` raised to the power of `k` minus `1` is prime and `n` equals `2` raised to the power of `k-1` times `2` raised to the power of `k` minus `1`.

### Informal sketch
* The proof starts by assuming `n` is even and perfect, then applies `EVEN_ODD_DECOMP` to decompose `n` into `2` raised to some power `r` times an odd number `s`.
* It then considers the case where `n` equals `0` and uses `perfect` to derive a contradiction.
* The main body of the proof involves showing that `s` must be equal to `2` raised to the power of `k` minus `1` for some `k`, and that this `k` satisfies the required conditions.
* Key steps involve using `SIGMA_MULTIPLICATIVE`, `COPRIME_ODD_POW2`, and `MULT_EQ_COPRIME` to establish the necessary relationships between `r`, `s`, and `k`.
* The proof also involves case analysis on the possible values of `d`, where `d` is a divisor of `s`, to establish the primality of `2` raised to the power of `k` minus `1`.

### Mathematical insight
This theorem provides a characterization of even perfect numbers in terms of Mersenne primes. It shows that every even perfect number can be expressed as `2` raised to the power of `k-1` times a Mersenne prime `2` raised to the power of `k` minus `1`. This provides a deep connection between the properties of perfect numbers and the distribution of prime numbers.

### Dependencies
* Theorems:
 + `EVEN_ODD_DECOMP`
 + `perfect`
 + `SIGMA_MULTIPLICATIVE`
 + `COPRIME_ODD_POW2`
 + `MULT_EQ_COPRIME`
 + `SIGMA_MULT`
* Definitions:
 + `EVEN`
 + `perfect`
 + `prime`
 + `EXP` 
* Axioms and rules:
 + Basic arithmetic properties and rules, including `ARITH_RULE` and `TAUT`

---

