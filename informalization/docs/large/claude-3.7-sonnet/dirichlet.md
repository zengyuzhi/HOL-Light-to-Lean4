# dirichlet.ml

## Overview

Number of statements: 73

This file contains the formalization of Dirichlet's theorem on primes in arithmetic progressions, which states that for any coprime integers a and k, there are infinitely many primes congruent to a modulo k. The implementation likely builds on number theory concepts from the imported files, including multiplicative functions, the von Mangoldt function, and transcendental methods. It represents a significant achievement in formal verification, as Dirichlet's theorem is a cornerstone result in analytic number theory that connects prime numbers with modular arithmetic.

## VSUM_VSUM_DIVISORS

### VSUM_VSUM_DIVISORS
- VSUM_VSUM_DIVISORS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VSUM_VSUM_DIVISORS = prove
 (`!f x. vsum (1..x) (\n. vsum {d | d divides n} (f n)) =
         vsum (1..x) (\n. vsum (1..(x DIV n)) (\k. f (k * n) n))`,
  SIMP_TAC[VSUM; FINITE_DIVISORS; LE_1] THEN
  SIMP_TAC[VSUM; FINITE_NUMSEG; ITERATE_ITERATE_DIVISORS;
           MONOIDAL_VECTOR_ADD]);;
```

### Informal statement
For any function $f$ and natural number $x$, the double sum
$$\sum_{n=1}^{x} \sum_{d|n} f(n)$$
equals
$$\sum_{n=1}^{x} \sum_{k=1}^{\lfloor x/n \rfloor} f(kn, n)$$

where $d|n$ means $d$ divides $n$, and $\lfloor x/n \rfloor$ represents integer division.

### Informal proof
The proof applies the theorem `ITERATE_ITERATE_DIVISORS` to vector addition. 

First, we simplify using:
- `VSUM` definition for both sides of the equation
- The finiteness of divisor sets (`FINITE_DIVISORS`)
- The finiteness of numeric segments (`FINITE_NUMSEG`)
- The lower bound constraint (`LE_1`)

Then we apply `ITERATE_ITERATE_DIVISORS` with the knowledge that vector addition is monoidal (`MONOIDAL_VECTOR_ADD`).

This rearranges the double sum by changing the iteration order. The outer theorem `ITERATE_ITERATE_DIVISORS` handles the core mathematical transformation that allows exchanging the summation order.

### Mathematical insight
This theorem provides a way to rearrange a double sum where the inner sum is over divisors. This type of sum rearrangement appears frequently in analytic number theory, particularly when working with arithmetic functions.

The transformation changes from summing over all divisors of each number to summing over multiples of each number. This is a common technique for manipulating Dirichlet convolutions and similar constructions.

The importance of this result lies in its ability to simplify certain number-theoretic calculations by providing alternative ways to compute or bound sums involving divisor functions.

### Dependencies
- **Theorems**:
  - `ITERATE_ITERATE_DIVISORS`: Rearranges a double iteration where the inner iteration is over divisors
  - `MONOIDAL_VECTOR_ADD`: States that vector addition is monoidal
  - `VSUM`: Definition of vector sum
  - `FINITE_DIVISORS`: States that the set of divisors of a number is finite
  - `FINITE_NUMSEG`: States that numeric segments are finite
  - `LE_1`: Constraint that 1 is a lower bound

### Porting notes
When porting this theorem, be aware that different systems may have different ways of handling:
1. Sets and their finiteness properties
2. Divisibility notation
3. Vector operations and their monoidal properties
4. The rearrangement of double sums

The core mathematical idea is standard, but the specifics of how divisors and summation are formalized might vary between proof assistants.

---

## REAL_EXP_1_LE_4

### REAL_EXP_1_LE_4
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_EXP_1_LE_4 = prove
 (`exp(&1) <= &4`,
  ONCE_REWRITE_TAC[ARITH_RULE `&1 = &1 / &2 + &1 / &2`; REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&4 = &2 * &2`; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(SPEC `&1 / &2` REAL_EXP_BOUND_LEMMA) THEN REAL_ARITH_TAC);;
```

### Informal statement
This theorem states that $\exp(1) \leq 4$.

### Informal proof
The proof proceeds as follows:

- First, rewrite $1 = \frac{1}{2} + \frac{1}{2}$ and apply the exponential addition formula, so $\exp(1) = \exp(\frac{1}{2} + \frac{1}{2}) = \exp(\frac{1}{2}) \cdot \exp(\frac{1}{2})$.
- Also rewrite $4 = 2 \cdot 2$.
- To prove $\exp(\frac{1}{2}) \cdot \exp(\frac{1}{2}) \leq 2 \cdot 2$, it suffices to show that $\exp(\frac{1}{2}) \leq 2$, which we can apply twice using the `REAL_LE_MUL2` theorem.
- We know $\exp(x) \geq 0$ for all $x$ from `REAL_EXP_POS_LE`.
- Finally, apply `REAL_EXP_BOUND_LEMMA` which states that $\exp(x) \leq 1 + 2x$ for $0 \leq x \leq \frac{1}{2}$.
- Since $\frac{1}{2}$ satisfies these conditions, we get $\exp(\frac{1}{2}) \leq 1 + 2 \cdot \frac{1}{2} = 2$, completing the proof.

### Mathematical insight
This theorem provides a simple upper bound for $e = \exp(1)$. While the actual value of $e$ is approximately 2.718, this theorem establishes a convenient bound of $e \leq 4$ which is useful in many approximation scenarios. This is derived using elementary properties of the exponential function rather than calculating the value directly.

The proof technique illustrates how to obtain bounds on exponential values by splitting the exponent and using known bounds on smaller values.

### Dependencies
- Definitions:
  - `exp`: The real exponential function defined as $\exp(x) = \text{Re}(\text{cexp}(\text{Cx } x))$

- Theorems:
  - `REAL_EXP_ADD`: $\exp(x + y) = \exp(x) \cdot \exp(y)$
  - `REAL_EXP_POS_LE`: $0 \leq \exp(x)$ for all $x$
  - `REAL_EXP_BOUND_LEMMA`: If $0 \leq x \leq \frac{1}{2}$, then $\exp(x) \leq 1 + 2x$

---

## DECREASING_LOG_OVER_N

### DECREASING_LOG_OVER_N
- `DECREASING_LOG_OVER_N`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DECREASING_LOG_OVER_N = prove
 (`!n. 4 <= n ==> log(&n + &1) / (&n + &1) <= log(&n) / &n`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog z / z`; `\z. (Cx(&1) - clog(z)) / z pow 2`;
                 `Cx(&n)`; `Cx(&n + &1)`] COMPLEX_MVT_LINE) THEN
  REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
  REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    SUBGOAL_THEN `&0 < Re w` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w = Cx(&0)` THEN ASM_SIMP_TAC[RE_CX; REAL_LT_REFL] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `&0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_DIV; RE_CX; GSYM CX_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> a - b = x ==> a <= b`) THEN
    REWRITE_TAC[RE_MUL_CX; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `?u. z = Cx(u)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[REAL; real]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IM_CX; RE_CX]) THEN
    UNDISCH_THEN `T` (K ALL_TAC) THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; RE_CX;
      real_div; GSYM REAL_MUL_LNEG; REAL_NEG_SUB; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For any natural number $n \geq 4$, we have:
$$\frac{\ln(n + 1)}{n + 1} \leq \frac{\ln(n)}{n}$$

This theorem states that the function $f(x) = \frac{\ln(x)}{x}$ is decreasing for $x \geq 4$.

### Informal proof
We apply the Mean Value Theorem for complex functions on the line segment from $n$ to $n+1$, considering the function $f(z) = \frac{\ln(z)}{z}$ with derivative $f'(z) = \frac{1 - \ln(z)}{z^2}$.

The proof proceeds as follows:

* First, we convert the inequality into its real-number form and assume $n \geq 4$.
* We apply the Complex Mean Value Theorem (COMPLEX_MVT_LINE) to the function $f(z) = \frac{\ln(z)}{z}$ with derivative $f'(z) = \frac{1-\ln(z)}{z^2}$ on the line segment from $n$ to $n+1$.
* We verify that $f'$ is well-defined on this segment, noting that the real part of any point on this segment is positive.
* The Mean Value Theorem gives us that for some point $z$ on the segment:
  $$f(n+1) - f(n) = f'(z)(n+1 - n) = f'(z)$$
* Since $z$ is a real number between $n$ and $n+1$, we have $z > 0$.
* We need to show that $f'(z) \leq 0$, which is equivalent to showing that $\ln(z) \geq 1$ for $z \geq 4$.
* To prove this, we use that $\ln(z) \geq \ln(4)$ for $z \geq 4$ (by monotonicity of logarithm) and $\ln(4) \geq 1$ (using that $e \leq 4$).
* Therefore $f'(z) \leq 0$, which implies $f(n+1) \leq f(n)$, completing the proof.

### Mathematical insight
This theorem establishes that the function $f(x) = \frac{\ln(x)}{x}$ is decreasing for $x \geq 4$. This is a standard result in calculus, but formalizing it requires careful application of the Mean Value Theorem.

The function $\frac{\ln(x)}{x}$ appears in various contexts, including the study of the harmonic series and the analysis of algorithms. The fact that it's decreasing for sufficiently large values is often used in asymptotic analyses.

The proof uses the complex version of the Mean Value Theorem, which is more general than necessary for this real-valued statement, but demonstrates the power and flexibility of complex analysis in proving real analysis results.

### Dependencies
- **Theorems:**
  - `REAL_EXP_POS_LT`: $\forall x. 0 < \exp(x)$
  - `LOG_EXP`: $\forall x. \log(\exp(x)) = x$
  - `LOG_MONO_LE_IMP`: $\forall x y. 0 < x \land x \leq y \Rightarrow \log(x) \leq \log(y)$
  - `CX_LOG`: $\forall z. 0 < z \Rightarrow \text{Cx}(\log(z)) = \text{clog}(\text{Cx}(z))$
  - `REAL_EXP_1_LE_4`: $\exp(1) \leq 4$
  - `COMPLEX_MVT_LINE` (not explicitly listed in dependencies but used)

- **Definitions:**
  - `clog`: $\text{clog}(z) = \text{the unique } w \text{ such that } \exp(w) = z \land -\pi < \text{Im}(w) \leq \pi$

### Porting notes
When porting this theorem:

1. The proof relies on the complex version of the Mean Value Theorem. Make sure your target system has this theorem available or be prepared to port it.

2. The complex logarithm (`clog`) requires careful handling, especially regarding its branch cuts. Ensure that your target system's definition of complex logarithm matches HOL Light's.

3. The proof strategy using complex analysis to prove a real-valued result might be more complicated than necessary. A direct proof using real calculus (finding the derivative and showing it's negative for x ≥ 4) could be simpler in some systems.

4. The inequality $e \leq 4$ is used in the proof. Some systems might have this result available already, possibly with a tighter bound.

---

## EXISTS_COMPLEX_ROOT_NONTRIVIAL

### EXISTS_COMPLEX_ROOT_NONTRIVIAL
- `EXISTS_COMPLEX_ROOT_NONTRIVIAL`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EXISTS_COMPLEX_ROOT_NONTRIVIAL = prove
 (`!a n. 2 <= n ==> ?z. z pow n = a /\ ~(z = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `2 <= n ==> ~(n = 0)`)) THEN
  ASM_CASES_TAC  `a = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_POW_ZERO] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = Cx(&1)` THENL
   [EXISTS_TAC `cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &n))` THEN
    ASM_SIMP_TAC[COMPLEX_ROOT_UNITY_EQ_1; DIVIDES_ONE;
                 ARITH_RULE `2 <= n ==> ~(n = 1)`; COMPLEX_ROOT_UNITY];
    MATCH_MP_TAC(MESON[]
     `(!x. ~Q x ==> ~P x) /\ (?x. P x) ==> (?x. P x /\ Q x)`) THEN
    ASM_SIMP_TAC[COMPLEX_POW_ONE] THEN EXISTS_TAC `cexp(clog a / Cx(&n))` THEN
    ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CEXP_CLOG]]);;
```

### Informal statement
For all complex numbers $a$ and natural numbers $n \geq 2$, there exists a complex number $z$ such that $z^n = a$ and $z \neq 1$.

### Informal proof
The proof proceeds by case analysis:

- First, we note that if $n \geq 2$ then $n \neq 0$.

- **Case 1**: If $a = 0$
  * We can choose $z = 0$, since $0^n = 0$ and $0 \neq 1$.

- **Case 2**: If $a = 1$
  * We choose $z = \exp(2\pi i \cdot \frac{1}{n})$, which is a non-trivial $n$-th root of unity.
  * Since $n \geq 2$, we know $n \neq 1$, so $n$ does not divide $1$.
  * By `COMPLEX_ROOT_UNITY_EQ_1`, we know $\exp(2\pi i \cdot \frac{1}{n}) = 1$ if and only if $n$ divides $1$.
  * Since $n$ does not divide $1$, we have $z \neq 1$.
  * By `COMPLEX_ROOT_UNITY`, we know $z^n = 1$.

- **Case 3**: If $a \neq 0$ and $a \neq 1$
  * We use the fact that if $z^n = a$ and $z \neq 1$ holds, then our goal is proved.
  * We choose $z = \exp(\frac{\log(a)}{n})$.
  * We have $z^n = \exp(n \cdot \frac{\log(a)}{n}) = \exp(\log(a)) = a$
  * Since $a \neq 1$, we also have $z \neq 1$ (because $a = 1$ would imply $z = 1$).

### Mathematical insight
This theorem demonstrates the existence of non-trivial $n$-th roots for any complex number when $n \geq 2$. It's notable that:

1. When $a = 1$, the theorem points to the existence of non-trivial $n$-th roots of unity, specifically using the complex exponential function.
   
2. For other values of $a$, it shows how the complex logarithm can be used to construct $n$-th roots.

The result is fundamental in complex analysis and algebra, showing the completeness of the complex number field regarding root extraction. It confirms that every complex number has exactly $n$ distinct $n$-th roots when $n \geq 1$, with this theorem specifically stating that at least one of these roots differs from 1 when $n \geq 2$.

### Dependencies
- **Theorems**:
  - `COMPLEX_ROOT_UNITY`: States that $\exp(2\pi i \cdot \frac{j}{n})^n = 1$ for non-zero $n$.
  - `COMPLEX_ROOT_UNITY_EQ_1`: States that $\exp(2\pi i \cdot \frac{j}{n}) = 1$ if and only if $n$ divides $j$.
  - `CEXP_N`: States that $\exp(n \cdot x) = \exp(x)^n$.
  - `CEXP_CLOG`: States that $\exp(\log(z)) = z$ for non-zero $z$.

- **Definitions**:
  - `pi`: Definition of $\pi$.
  - `cexp`: The complex exponential function.
  - `clog`: The complex logarithm function.

### Porting notes
When porting this theorem:
1. Ensure your target system has definitions for complex exponential and logarithm functions.
2. Verify that the properties of complex roots of unity are available or can be proven.
3. The proof uses case analysis and existence proofs - make sure your system supports these proof techniques.
4. Pay attention to the handling of the complex number type and its operations, especially exponentiation.

---

## dirichlet_character

### dirichlet_character
- dirichlet_character

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let dirichlet_character = new_definition
 `dirichlet_character d (c:num->complex) <=>
        (!n. c(n + d) = c(n)) /\
        (!n. c(n) = Cx(&0) <=> ~coprime(n,d)) /\
        (!m n. c(m * n) = c(m) * c(n))`;;
```

### Informal statement
A function $c: \mathbb{N} \to \mathbb{C}$ is a Dirichlet character modulo $d$ if and only if it satisfies the following three conditions:
1. $c$ is periodic with period $d$: $\forall n. c(n + d) = c(n)$
2. $c(n) = 0$ if and only if $n$ and $d$ are not coprime: $\forall n. c(n) = 0 \Leftrightarrow \text{gcd}(n,d) \neq 1$
3. $c$ is multiplicative: $\forall m,n. c(m \cdot n) = c(m) \cdot c(n)$

Here, $\mathbb{N}$ represents the natural numbers and $\mathbb{C}$ represents the complex numbers.

### Informal proof
This is a definition, so it does not contain a proof.

### Mathematical insight
Dirichlet characters are fundamental objects in number theory that generalize the Legendre symbol and play a crucial role in the study of L-functions and the distribution of primes in arithmetic progressions.

A Dirichlet character modulo $d$ can be viewed as a homomorphism from the multiplicative group of integers modulo $d$ that are coprime to $d$ (denoted as $(\mathbb{Z}/d\mathbb{Z})^*$) to the non-zero complex numbers. The first condition ensures that the character depends only on the congruence class modulo $d$. The second condition specifies that the character vanishes precisely when the input is not coprime to the modulus. The third condition captures the multiplicative property of the character.

Dirichlet characters are essential in the formulation and proof of Dirichlet's theorem on primes in arithmetic progressions, which states that for any positive integers $a$ and $d$ with $\gcd(a,d) = 1$, there are infinitely many primes of the form $a + nd$ where $n \in \mathbb{N}$.

### Dependencies
- `Cx`: Complex embedding of real numbers
- `coprime`: Function that checks if two numbers are coprime

### Porting notes
When porting this definition:
- Ensure that the target system has a proper representation of complex numbers
- Check how the target system represents the coprimality relation
- The periodicity condition might be alternatively expressed using congruence modulo $d$ in some systems
- Consider whether the target system uses indexing from 0 or 1 for natural numbers, which might affect how the definition is stated

---

## DIRICHLET_CHARACTER_PERIODIC

### DIRICHLET_CHARACTER_PERIODIC

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_PERIODIC = prove
 (`!d c n. dirichlet_character d c ==> c(n + d) = c(n)`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For any positive integer $d$, any Dirichlet character $c: \mathbb{N} \rightarrow \mathbb{C}$ associated with modulus $d$, and any natural number $n$, we have $c(n + d) = c(n)$.

In other words, a Dirichlet character is periodic with period $d$.

### Informal proof
The proof is straightforward by directly applying the definition of a Dirichlet character.

By definition, a Dirichlet character $c$ with modulus $d$ satisfies the property that for all $n$, $c(n + d) = c(n)$. This is precisely the first condition in the definition of `dirichlet_character`, making this theorem an immediate consequence of unfolding the definition.

### Mathematical insight
This theorem explicitly highlights the periodicity property of Dirichlet characters, which is one of their fundamental attributes. The periodicity with period $d$ means that Dirichlet characters are completely determined by their values on the set $\{0, 1, 2, \ldots, d-1\}$, making them finite objects despite being defined on all natural numbers.

This periodicity property is essential for the theory of Dirichlet characters and their applications in number theory, particularly in the study of L-functions and the distribution of primes in arithmetic progressions.

### Dependencies
- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character as a function $c: \mathbb{N} \rightarrow \mathbb{C}$ satisfying three conditions: (1) periodicity with modulus $d$: $c(n+d) = c(n)$ for all $n$, (2) $c(n) = 0$ if and only if $n$ and $d$ are not coprime, and (3) multiplicativity: $c(mn) = c(m)c(n)$ for all $m,n$.

### Porting notes
This theorem should be straightforward to port to other systems as it's a direct consequence of the definition of a Dirichlet character. The main consideration is ensuring that the definition of `dirichlet_character` is ported correctly first, with the appropriate type for the function (mapping natural numbers to complex numbers).

---

## DIRICHLET_CHARACTER_EQ_0

### Name of formal statement
DIRICHLET_CHARACTER_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_0 = prove
 (`!d c n. dirichlet_character d c ==> (c(n) = Cx(&0) <=> ~coprime(n,d))`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For any positive integer $d$, any Dirichlet character $c$ modulo $d$, and any integer $n$, we have:
$$c(n) = 0 \iff \text{$n$ and $d$ are not coprime}$$

Where a Dirichlet character modulo $d$ is a function $c : \mathbb{N} \to \mathbb{C}$ that satisfies the following properties:
1. $c$ is periodic with period $d$: $c(n + d) = c(n)$ for all $n$
2. $c(n) = 0$ if and only if $n$ and $d$ are not coprime
3. $c$ is multiplicative: $c(mn) = c(m)c(n)$ for all $m, n$

### Informal proof
This theorem follows directly from the definition of a Dirichlet character. 

By the definition of `dirichlet_character`, one of the conditions that must be satisfied is precisely that $c(n) = 0$ if and only if $n$ and $d$ are not coprime. The proof simply applies the `dirichlet_character` definition to extract this property.

### Mathematical insight
This theorem explicitly states a fundamental property of Dirichlet characters: a Dirichlet character modulo $d$ evaluates to zero precisely at those integers that share a common factor with $d$ (i.e., are not coprime to $d$).

This property is crucial in number theory, particularly in the study of Dirichlet's theorem on primes in arithmetic progressions and L-functions. It ensures that the character detects exactly the integers that have a common factor with the modulus, which is important for its arithmetic applications.

The result could be considered a trivial extraction from the definition of a Dirichlet character, but it's stated as a separate theorem to make it conveniently available for use in further proofs.

### Dependencies
#### Definitions
- `dirichlet_character`: Defines what it means for a function to be a Dirichlet character modulo $d$

### Porting notes
When porting this theorem, note that it's essentially just an extraction of one of the conjuncts from the definition of a Dirichlet character. The proof is simply simplification by unfolding the definition. Any proof assistant should handle this straightforwardly once the definition is in place.

---

## DIRICHLET_CHARACTER_MUL

### Name of formal statement
DIRICHLET_CHARACTER_MUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_MUL = prove
 (`!d c m n. dirichlet_character d c ==> c(m * n) = c(m) * c(n)`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$, and for any natural numbers $m$ and $n$, we have
$$c(m \cdot n) = c(m) \cdot c(n)$$

This theorem states that Dirichlet characters are completely multiplicative functions.

### Informal proof
The proof is straightforward. By the definition of `dirichlet_character`, one of the properties that defines a Dirichlet character $c$ modulo $d$ is that for all $m$ and $n$, $c(m \cdot n) = c(m) \cdot c(n)$. 

The proof simply uses simplification with the definition of `dirichlet_character`, which directly contains the multiplicative property we're proving.

### Mathematical insight
This theorem isolates and explicitly states the multiplicative property of Dirichlet characters, which is one of their fundamental characteristics. 

A Dirichlet character modulo $d$ is a function $c: \mathbb{N} \rightarrow \mathbb{C}$ that has three key properties:
1. It is periodic with period $d$: $c(n+d) = c(n)$ for all $n$
2. It is zero precisely on numbers not coprime to $d$: $c(n) = 0 \iff \gcd(n,d) \neq 1$
3. It is completely multiplicative: $c(mn) = c(m)c(n)$ for all $m,n$

This theorem extracts the third property, making it available as a standalone result that can be referenced in other proofs involving Dirichlet characters.

### Dependencies
#### Definitions
- `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a complex-valued function satisfying periodicity, zero characterization, and multiplicativity properties.

### Porting notes
When porting this theorem, note that it's simply extracting a property already contained in the definition. The implementation is straightforward in any proof assistant that supports simplification or rewriting with definitions.

---

## DIRICHLET_CHARACTER_EQ_1

### DIRICHLET_CHARACTER_EQ_1
- `DIRICHLET_CHARACTER_EQ_1`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_1 = prove
 (`!d c. dirichlet_character d c ==> c(1) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_MUL) THEN
  DISCH_THEN(MP_TAC o repeat (SPEC `1`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_FIELD `a = a * a <=> a = Cx(&0) \/ a = Cx(&1)`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_EQ_0] THEN
  MESON_TAC[COPRIME_1; COPRIME_SYM]);;
```

### Informal statement
For any positive integer $d$ and function $c: \mathbb{N} \to \mathbb{C}$, if $c$ is a Dirichlet character modulo $d$, then $c(1) = 1$.

### Informal proof
Let $d$ be a positive integer and $c$ be a Dirichlet character modulo $d$.

By the multiplicative property of Dirichlet characters, we have $c(m \cdot n) = c(m) \cdot c(n)$ for all natural numbers $m$ and $n$.

Setting $m = n = 1$, we get:
$c(1 \cdot 1) = c(1) \cdot c(1)$

Since $1 \cdot 1 = 1$, this simplifies to:
$c(1) = c(1) \cdot c(1)$

By the field properties of complex numbers, this equation $a = a \cdot a$ implies either $a = 0$ or $a = 1$.

However, by the definition of a Dirichlet character, $c(n) = 0$ if and only if $n$ and $d$ are not coprime.

Since $1$ is coprime to every positive integer (including $d$), we have that $c(1) \neq 0$.

Therefore, we must have $c(1) = 1$.

### Mathematical insight
This theorem establishes a fundamental property of Dirichlet characters: they always map the value 1 to 1. This is analogous to how a group homomorphism maps the identity element to the identity element.

This property is essential for the theory of Dirichlet characters and their applications in number theory, particularly in the study of L-functions and the distribution of primes in arithmetic progressions. It ensures that Dirichlet characters preserve the multiplicative identity, which is a key property for their use in analytic number theory.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_MUL`: If $c$ is a Dirichlet character modulo $d$, then $c(m \cdot n) = c(m) \cdot c(n)$ for all natural numbers $m$ and $n$.
  - `DIRICHLET_CHARACTER_EQ_0`: For a Dirichlet character $c$ modulo $d$, $c(n) = 0$ if and only if $n$ and $d$ are not coprime.
  - `COPRIME_1` and `COPRIME_SYM`: Number theory theorems about coprime numbers.

- Definitions:
  - `dirichlet_character`: A function $c: \mathbb{N} \to \mathbb{C}$ is a Dirichlet character modulo $d$ if it satisfies:
    - Periodicity: $c(n + d) = c(n)$ for all $n$
    - Zero mapping: $c(n) = 0$ if and only if $n$ and $d$ are not coprime
    - Multiplicativity: $c(m \cdot n) = c(m) \cdot c(n)$ for all $m, n$

### Porting notes
When porting this theorem, ensure that your definition of Dirichlet character includes all three key properties: periodicity, the zero mapping condition, and multiplicativity. Different proof assistants may have varying ways of representing complex numbers and number theory concepts like coprimality, so these underlying definitions should be checked for compatibility.

---

## DIRICHLET_CHARACTER_POW

### Name of formal statement
DIRICHLET_CHARACTER_POW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_POW = prove
 (`!d c m n. dirichlet_character d c ==> c(m EXP n) = c(m) pow n`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[EXP; complex_pow] THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
For any positive integers $d$ and $m$, any Dirichlet character $c$ modulo $d$, and any natural number $n$, we have:

$$c(m^n) = c(m)^n$$

where $c(m^n)$ denotes the character evaluated at $m$ raised to the $n$th power, and $c(m)^n$ denotes the complex number $c(m)$ raised to the $n$th power.

### Informal proof
We prove that for a Dirichlet character $c$ modulo $d$, the character value of $m^n$ equals the $n$th power of the character value of $m$.

* Base case ($n = 0$): We need to show $c(m^0) = c(m)^0$, which simplifies to $c(1) = 1$.
  - From the definition of exponentiation, $m^0 = 1$
  - By the `DIRICHLET_CHARACTER_EQ_1` theorem, we know $c(1) = 1$ for any Dirichlet character
  - Therefore, $c(m^0) = c(1) = 1 = c(m)^0$

* Inductive case: Assume that $c(m^k) = c(m)^k$ for some $k ≥ 0$.
  - We need to show $c(m^{k+1}) = c(m)^{k+1}$
  - By definition of exponentiation, $m^{k+1} = m^k \cdot m$
  - By the multiplicative property of Dirichlet characters (`DIRICHLET_CHARACTER_MUL`), we have:
    $c(m^{k+1}) = c(m^k \cdot m) = c(m^k) \cdot c(m)$
  - Using the induction hypothesis, we get:
    $c(m^k) \cdot c(m) = c(m)^k \cdot c(m) = c(m)^{k+1}$
  - Therefore, $c(m^{k+1}) = c(m)^{k+1}$

Thus, by mathematical induction, we've proven that $c(m^n) = c(m)^n$ for all natural numbers $n$.

### Mathematical insight
This theorem establishes a fundamental property of Dirichlet characters: they respect exponentiation. This is a natural extension of their multiplicative property. Dirichlet characters are completely multiplicative functions, meaning they preserve multiplication: $c(mn) = c(m)c(n)$. This theorem shows that this multiplicative property extends to exponentiation as well.

This result is essential for various number theory applications, particularly in the theory of Dirichlet L-functions and character sums. It allows us to simplify expressions involving powers when working with Dirichlet characters, which is particularly useful in analytic number theory.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_MUL`: States that for a Dirichlet character $c$ modulo $d$, and any integers $m$ and $n$, we have $c(mn) = c(m)c(n)$
  - `DIRICHLET_CHARACTER_EQ_1`: States that for a Dirichlet character $c$ modulo $d$, we have $c(1) = 1$

- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character $c$ modulo $d$ as a function satisfying three properties:
    1. Periodicity: $c(n + d) = c(n)$ for all $n$
    2. Zero exactly at non-coprime values: $c(n) = 0$ if and only if $\gcd(n,d) > 1$
    3. Multiplicativity: $c(mn) = c(m)c(n)$ for all $m,n$

### Porting notes
When porting this theorem:
- Ensure the definition of complex power (`pow`) in the target system matches HOL Light's behavior
- Make sure the definition of exponentiation for natural numbers is compatible
- Verify that the base case handling (for $n = 0$) correctly deals with the fact that $m^0 = 1$ and $c(m)^0 = 1$

---

## DIRICHLET_CHARACTER_PERIODIC_GEN

### Name of formal statement
DIRICHLET_CHARACTER_PERIODIC_GEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_PERIODIC_GEN = prove
 (`!d c m n. dirichlet_character d c ==> c(m * d + n) = c(n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(mk + d) + n:num = (mk + n) + d`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC]);;
```

### Informal statement
If $c$ is a Dirichlet character modulo $d$, then for all natural numbers $m$ and $n$, we have:
$$c(m \cdot d + n) = c(n)$$

This theorem generalizes the periodicity property of Dirichlet characters.

### Informal proof
We prove that if $c$ is a Dirichlet character modulo $d$, then $c(m \cdot d + n) = c(n)$ for all natural numbers $m$ and $n$.

* First, convert the theorem to an implication form and set up the variables.
* Proceed by induction on $m$:
  * Base case ($m = 0$): Since $0 \cdot d + n = n$, we have $c(0 \cdot d + n) = c(n)$, which is trivially true.
  * Inductive step: Assume the result holds for some natural number $m$, i.e., $c(m \cdot d + n) = c(n)$ for all $n$.
  * We need to show that $c((m+1) \cdot d + n) = c(n)$.
* Simplify $(m+1) \cdot d + n$ to $m \cdot d + d + n$.
* Apply the inductive hypothesis to rewrite the right-hand side.
* Rearrange the terms: $(m \cdot d + d) + n = (m \cdot d + n) + d$.
* Apply the `DIRICHLET_CHARACTER_PERIODIC` theorem, which states that $c(n + d) = c(n)$ for any Dirichlet character $c$ modulo $d$.
* This completes the proof that $c(m \cdot d + n) = c(n)$.

### Mathematical insight
This theorem generalizes the basic periodicity property of Dirichlet characters. While the definition of a Dirichlet character already includes the condition that $c(n+d) = c(n)$, this theorem extends it to show that $c$ is constant on each congruence class modulo $d$.

The result is important for number-theoretic applications, particularly in analytic number theory when studying Dirichlet $L$-functions, as it confirms that a Dirichlet character's values depend only on the residue class of its argument modulo $d$. This means we only need to know the values of $c$ on the numbers $1, 2, \ldots, d$ to determine it completely.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_PERIODIC`: If $c$ is a Dirichlet character modulo $d$, then $c(n + d) = c(n)$ for all $n$.

- **Definitions**:
  - `dirichlet_character`: A function $c : \mathbb{N} \rightarrow \mathbb{C}$ is a Dirichlet character modulo $d$ if:
    - It is periodic with period $d$: $c(n + d) = c(n)$ for all $n$.
    - $c(n) = 0$ if and only if $n$ and $d$ are not coprime.
    - It is completely multiplicative: $c(m \cdot n) = c(m) \cdot c(n)$ for all $m, n$.

### Porting notes
When porting this theorem:
1. Ensure the definition of Dirichlet character includes all three key properties (periodicity, values on non-coprime inputs, and multiplicativity).
2. The induction approach should be straightforward to translate to other systems.
3. The arithmetic rewriting may need system-specific tactics but the general structure of rearranging $(m \cdot d + d) + n$ to $(m \cdot d + n) + d$ should be similar.

---

## DIRICHLET_CHARACTER_CONG

### DIRICHLET_CHARACTER_CONG
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CONG = prove
 (`!d c m n.
        dirichlet_character d c /\ (m == n) (mod d) ==> c(m) = c(n)`,
  REWRITE_TAC[CONG_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN]);;
```

### Informal statement
For any positive integer $d$, complex-valued function $c$, and natural numbers $m$ and $n$, if $c$ is a Dirichlet character modulo $d$ and $m \equiv n \pmod{d}$, then $c(m) = c(n)$.

### Informal proof
The proof uses the characterization of congruence from `CONG_CASES` which states that $m \equiv n \pmod{d}$ if and only if either there exists a $q$ such that $m = qd + n$ or there exists a $q$ such that $n = qd + m$.

In either case, we apply `DIRICHLET_CHARACTER_PERIODIC_GEN` which states that for any Dirichlet character $c$ modulo $d$, we have $c(md + n) = c(n)$ for all natural numbers $m$ and $n$. 

This immediately gives us $c(m) = c(n)$ when $m \equiv n \pmod{d}$.

### Mathematical insight
This theorem formalizes a fundamental property of Dirichlet characters: they are well-defined on congruence classes modulo $d$. This means that a Dirichlet character only depends on the remainder when dividing by $d$, not on the specific number itself.

This is a crucial property because it allows us to view Dirichlet characters as functions on $\mathbb{Z}/d\mathbb{Z}$ (the ring of integers modulo $d$), which is essential for their application in number theory, particularly in the study of primes in arithmetic progressions and L-functions.

### Dependencies
- Theorems:
  - `CONG_CASES`: Characterizes when two numbers are congruent modulo $n$
  - `DIRICHLET_CHARACTER_PERIODIC_GEN`: Shows that Dirichlet characters are periodic with period $d$
  
- Definitions:
  - `dirichlet_character`: Defines what it means for a function to be a Dirichlet character

### Porting notes
When porting this theorem, note that the proof relies on the specific formulation of congruence and the periodicity property of Dirichlet characters. Different systems might have different conventions for representing congruences or Dirichlet characters, so the corresponding properties should be established first.

---

## DIRICHLET_CHARACTER_ROOT

### Name of formal statement
DIRICHLET_CHARACTER_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ROOT = prove
 (`!d c n. dirichlet_character d c /\ coprime(d,n)
           ==> c(n) pow phi(d) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o GSYM o MATCH_MP DIRICHLET_CHARACTER_EQ_1) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_POW th)]) THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FERMAT_LITTLE THEN ASM_MESON_TAC[COPRIME_SYM]);;
```

### Informal statement
For any modulus $d$, any Dirichlet character $c$ modulo $d$, and any integer $n$ coprime to $d$, the value of the character raised to the power of Euler's totient function $\phi(d)$ equals 1:

$$\forall d,c,n.\; \text{dirichlet\_character}(d,c) \land \text{coprime}(d,n) \Rightarrow c(n)^{\phi(d)} = 1$$

### Informal proof
The proof demonstrates that a Dirichlet character evaluated at a value coprime to its modulus, when raised to the power of $\phi(d)$, equals 1.

* We start with a Dirichlet character $c$ modulo $d$ and a number $n$ coprime to $d$.

* By `DIRICHLET_CHARACTER_EQ_1`, we know that $c(1) = 1$.

* Using `DIRICHLET_CHARACTER_POW`, we can rewrite the goal to show that $c(n^{\phi(d)}) = 1$, since for a Dirichlet character $c(n^k) = c(n)^k$.

* By Fermat's Little Theorem (adapted for modular arithmetic with modulus $d$ and Euler's totient function), we know that $n^{\phi(d)} \equiv 1 \pmod{d}$ when $\text{coprime}(n,d)$.

* Since $n^{\phi(d)} \equiv 1 \pmod{d}$, and using `DIRICHLET_CHARACTER_CONG` which states that characters have the same value for numbers congruent modulo $d$, we get $c(n^{\phi(d)}) = c(1)$.

* Since $c(1) = 1$, we conclude that $c(n)^{\phi(d)} = c(n^{\phi(d)}) = c(1) = 1$.

### Mathematical insight
This theorem establishes an important property of Dirichlet characters: their values at numbers coprime to the modulus are roots of unity with order dividing $\phi(d)$. This is a generalization of Fermat's Little Theorem to the context of Dirichlet characters and is fundamental in number theory, particularly in the study of Dirichlet L-functions.

The result encapsulates the periodic and multiplicative nature of Dirichlet characters, showing that they behave like homomorphisms from the multiplicative group of integers modulo $d$ to the complex roots of unity.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_EQ_1`: A Dirichlet character always evaluates to 1 at the number 1
  - `DIRICHLET_CHARACTER_POW`: A Dirichlet character evaluated at a power equals the character value raised to that power
  - `DIRICHLET_CHARACTER_CONG`: A Dirichlet character has the same value for numbers congruent modulo the character's modulus
  - `FERMAT_LITTLE` (implicit): If $\gcd(a,n) = 1$, then $a^{\phi(n)} \equiv 1 \pmod{n}$

- Definitions:
  - `dirichlet_character`: A function $c$ from natural numbers to complex numbers satisfying periodicity, vanishing precisely on numbers not coprime to $d$, and multiplicativity

### Porting notes
When porting this theorem:
1. Ensure your system has a definition of Dirichlet characters with the same properties
2. Verify that Euler's totient function and the Fermat's Little Theorem have been properly formalized
3. The proof relies heavily on the congruence properties of characters, so ensure these are established first
4. Be careful with the representation of complex numbers, especially the constant 1 as a complex number

---

## DIRICHLET_CHARACTER_NORM

### DIRICHLET_CHARACTER_NORM
- dirichlet_character_norm

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NORM = prove
 (`!d c n. dirichlet_character d c
           ==> norm(c n) = if coprime(d,n) then &1 else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[COMPLEX_NORM_ZERO] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COPRIME_SYM]] THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  COPRIME_0; COPRIME_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
    DIRICHLET_CHARACTER_ROOT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`norm((c:num->complex) n)`; `phi d`] REAL_POW_EQ_1_IMP) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM] THEN
  ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]);;
```

### Informal statement
For any natural numbers $d$ and $n$, and a Dirichlet character $c : \mathbb{N} \to \mathbb{C}$, if $c$ satisfies the properties of a Dirichlet character modulo $d$, then:

$$\|c(n)\| = \begin{cases}
1 & \text{if } \gcd(d,n) = 1 \\
0 & \text{otherwise}
\end{cases}$$

where $\|\cdot\|$ denotes the complex norm.

### Informal proof
We need to prove that the complex norm of a Dirichlet character $c(n)$ is either 0 or 1, depending on whether $n$ is coprime to the modulus $d$.

The proof proceeds by considering two cases:

* **Case 1**: When $\gcd(d,n) = 1$ (the numbers are coprime):
  - If $d = 0$: Since $\gcd(0,n) = n$, this means $n = 1$. By `DIRICHLET_CHARACTER_EQ_1`, we know $c(1) = 1$, so $\|c(1)\| = 1$.
  
  - If $d \neq 0$: Using `DIRICHLET_CHARACTER_ROOT`, we know that $c(n)^{\phi(d)} = 1$ where $\phi$ is Euler's totient function. 
  
    Taking the complex norm of both sides: $\|c(n)\|^{\phi(d)} = 1$.
    
    Since $\phi(d) \geq 1$ for any $d > 0$, by the properties of the complex norm (specifically `REAL_POW_EQ_1_IMP`), we must have $\|c(n)\| = 1$.

* **Case 2**: When $\gcd(d,n) \neq 1$ (the numbers are not coprime):
  - By `DIRICHLET_CHARACTER_EQ_0`, we know that $c(n) = 0$ if and only if $n$ is not coprime to $d$.
  - Therefore, $\|c(n)\| = \|0\| = 0$.

### Mathematical insight
This theorem establishes a fundamental property of Dirichlet characters: they are always of absolute value 1 when evaluated at arguments coprime to their modulus, and 0 otherwise. This property makes Dirichlet characters particularly useful in number theory, especially in the study of Dirichlet L-functions and the distribution of primes in arithmetic progressions.

The norm constraint ensures that Dirichlet characters are "unitary" when they don't vanish, which is a key property for analytic applications. This character-theoretic structure mirrors the behavior of group characters in representation theory, where unitary representations play a central role.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_EQ_0`: States that for a Dirichlet character $c$ modulo $d$, $c(n) = 0$ if and only if $n$ is not coprime to $d$.
  - `DIRICHLET_CHARACTER_EQ_1`: States that for a Dirichlet character $c$ modulo $d$, $c(1) = 1$.
  - `DIRICHLET_CHARACTER_ROOT`: States that for a Dirichlet character $c$ modulo $d$ and $n$ coprime to $d$, $c(n)^{\phi(d)} = 1$.

- **Definitions**:
  - `dirichlet_character`: Defines the properties of a Dirichlet character modulo $d$: periodic with period $d$, multiplicative, and vanishing exactly when its argument is not coprime to $d$.

### Porting notes
When porting this theorem, it's important to ensure that the definition of Dirichlet characters matches exactly. In particular:
1. The periodicity condition: $c(n+d) = c(n)$
2. The vanishing condition: $c(n) = 0$ if and only if $\gcd(n,d) \neq 1$
3. The multiplicativity condition: $c(mn) = c(m)c(n)$

Additionally, when implementing the proof, ensure that the library has appropriate theorems about Euler's totient function, especially lower bounds for $\phi(d)$, and properties of complex norms.

---

## chi_0

### chi_0
- chi_0

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let chi_0 = new_definition
 `chi_0 d n = if coprime(n,d) then Cx(&1) else Cx(&0)`;;
```

### Informal statement
The principal Dirichlet character $\chi_0$ modulo $d$ is defined as:
$$\chi_0(d, n) = \begin{cases}
1 & \text{if } \gcd(n, d) = 1 \\
0 & \text{otherwise}
\end{cases}$$

where $1$ and $0$ are interpreted as complex numbers.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The principal Dirichlet character $\chi_0$ modulo $d$ is a fundamental concept in number theory. It is the simplest of all Dirichlet characters and serves as the identity element in the group of Dirichlet characters modulo $d$. 

This function returns the complex number $1$ when $n$ is coprime to $d$, and $0$ otherwise. The principal character is important in the theory of Dirichlet L-functions and plays a crucial role in the proof of Dirichlet's theorem on primes in arithmetic progressions.

In this formalization, the function is defined to return complex values (`Cx(&1)` and `Cx(&0)`) rather than integers, which is common in analytical number theory where Dirichlet characters are viewed as complex-valued functions.

### Dependencies
- Definition: `chi_0`

### Porting notes
When porting this definition to other proof assistants:
- Be mindful of how complex numbers are represented in the target system
- Ensure the `coprime` function exists or define it appropriately
- Note that in HOL Light, `Cx` converts a real number to a complex number, and `&` converts an integer to a real number

---

## DIRICHLET_CHARACTER_CHI_0

### DIRICHLET_CHARACTER_CHI_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CHI_0 = prove
 (`dirichlet_character d (chi_0 d)`,
  REWRITE_TAC[dirichlet_character; chi_0] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(n + d,d) <=> coprime(n,d)`;
          NUMBER_RULE `coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)`] THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
The theorem states that $\chi_0(d)$ is a Dirichlet character modulo $d$. Formally:

$\text{dirichlet\_character}\ d\ (\chi_0\ d)$

where $\chi_0$ is the principal Dirichlet character modulo $d$, defined as:
$\chi_0(d)(n) = \begin{cases} 1 & \text{if}\ \gcd(n,d) = 1 \\ 0 & \text{otherwise} \end{cases}$

### Informal proof
The proof shows that $\chi_0(d)$ satisfies the three properties required for a Dirichlet character:

1. First, we expand the definitions of `dirichlet_character` and `chi_0` to work directly with their defining properties.

2. Next, we apply two number-theoretic identities:
   - $\gcd(n + d, d) = \gcd(n, d)$ 
   - $\gcd(m \cdot n, d) = 1$ if and only if $\gcd(m, d) = 1$ and $\gcd(n, d) = 1$

3. These identities help establish:
   - The periodicity property: $\chi_0(d)(n+d) = \chi_0(d)(n)$
   - The multiplicative property: $\chi_0(d)(m \cdot n) = \chi_0(d)(m) \cdot \chi_0(d)(n)$
   - The "zeros" property: $\chi_0(d)(n) = 0$ if and only if $\gcd(n,d) \neq 1$

4. Finally, `COMPLEX_RING` handles the algebraic simplifications needed to complete the proof, particularly showing that $1 \cdot 1 = 1$ for the multiplicative property when both $m$ and $n$ are coprime to $d$.

### Mathematical insight
The principal character $\chi_0$ is the simplest and most fundamental Dirichlet character. It serves as the identity element in the group of Dirichlet characters modulo $d$. This theorem establishes that $\chi_0$ satisfies all the required properties of a Dirichlet character:

1. Periodicity: $\chi_0(n+d) = \chi_0(n)$
2. Values are zero precisely when numbers aren't coprime to the modulus
3. Multiplicativity: $\chi_0(mn) = \chi_0(m)\chi_0(n)$

Understanding $\chi_0$ is essential for the theory of Dirichlet characters and L-functions, as it corresponds to the Riemann zeta function shifted by values.

### Dependencies
#### Definitions
- `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function satisfying periodicity, zero values at non-coprime inputs, and multiplicativity
- `chi_0`: Defines the principal Dirichlet character

#### Number theory rules
- `coprime(n + d,d) <=> coprime(n,d)`
- `coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)`

### Porting notes
When porting this theorem:
- Ensure the definition of Dirichlet character includes all three required properties
- The proof relies on basic properties of coprime numbers modulo $d$, which may be available in most libraries
- The complex arithmetic is trivial (multiplication of 0s and 1s), so automation in other systems should handle it easily

---

## DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Name of formal statement
DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_PRINCIPAL = prove
 (`!d c. dirichlet_character d c
         ==> (c = chi_0 d <=> !n. coprime(n,d) ==> c(n) = Cx(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]);;
```

### Informal statement
For any positive integer $d$ and function $c: \mathbb{N} \to \mathbb{C}$, if $c$ is a Dirichlet character modulo $d$, then $c$ equals the principal character modulo $d$ (denoted as $\chi_0$) if and only if $c(n) = 1$ for all $n$ coprime to $d$.

### Informal proof
Let $d$ be a positive integer and $c$ be a Dirichlet character modulo $d$. We need to prove that $c = \chi_0(d)$ if and only if $c(n) = 1$ for all integers $n$ that are coprime to $d$.

First, recall that the principal character $\chi_0(d)$ is defined as:
$$\chi_0(d)(n) = \begin{cases}
1 & \text{if } \gcd(n,d) = 1 \\
0 & \text{if } \gcd(n,d) > 1
\end{cases}$$

The proof follows directly from the definition of Dirichlet character and the DIRICHLET_CHARACTER_EQ_0 theorem:

- By the definition of equality between functions, $c = \chi_0(d)$ if and only if $c(n) = \chi_0(d)(n)$ for all $n$.
- For any $n$ not coprime to $d$, we have $c(n) = 0$ (by the DIRICHLET_CHARACTER_EQ_0 theorem) and $\chi_0(d)(n) = 0$ (by definition).
- For any $n$ coprime to $d$, we have $\chi_0(d)(n) = 1$ (by definition).

Therefore, $c = \chi_0(d)$ if and only if $c(n) = 1$ for all $n$ coprime to $d$.

### Mathematical insight
This theorem provides a simple characterization of when a Dirichlet character equals the principal character. The principal character ($\chi_0$) is the simplest and most fundamental Dirichlet character, taking the value 1 for integers coprime to the modulus and 0 otherwise.

The result is important because:
1. It gives a clean condition for recognizing the principal character among all Dirichlet characters.
2. It shows that a Dirichlet character is completely determined by its values on integers coprime to the modulus.
3. It serves as a building block for the theory of Dirichlet characters, which is central to analytic number theory.

The theorem essentially states that a Dirichlet character is the principal character if and only if it assigns the value 1 to all integers coprime to the modulus, which matches our intuitive understanding of the principal character.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_EQ_0`: Proves that for any Dirichlet character $c$ modulo $d$, $c(n) = 0$ if and only if $n$ is not coprime to $d$.

- **Definitions**:
  - `dirichlet_character`: Defines what it means for a function to be a Dirichlet character.
  - `chi_0`: Defines the principal Dirichlet character.

### Porting notes
When porting this theorem:
1. Ensure that the definition of Dirichlet character has been properly formalized with its three key properties (periodicity, multiplicativity, and zero values precisely at non-coprime inputs).
2. The principal character should be defined as taking value 1 for inputs coprime to the modulus and 0 otherwise.
3. Make sure the function equality is handled properly in the target system, as this theorem relies on extensional equality of functions.

---

## DIRICHLET_CHARACTER_NONPRINCIPAL

### DIRICHLET_CHARACTER_NONPRINCIPAL
- Name of formal statement: `DIRICHLET_CHARACTER_NONPRINCIPAL`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?n. coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`,
  MESON_TAC[DIRICHLET_CHARACTER_EQ_PRINCIPAL; DIRICHLET_CHARACTER_EQ_0]);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$, if $c$ is not the principal character $\chi_0$ modulo $d$, then there exists a number $n$ such that $\gcd(n,d) = 1$ and $c(n) \neq 0$ and $c(n) \neq 1$.

### Informal proof
The proof uses the characterization of the principal character from the theorem `DIRICHLET_CHARACTER_EQ_PRINCIPAL`, which states that a Dirichlet character $c$ modulo $d$ is the principal character $\chi_0$ if and only if $c(n) = 1$ for all $n$ coprime to $d$.

Since $c$ is not the principal character, by the contrapositive of `DIRICHLET_CHARACTER_EQ_PRINCIPAL`, there must exist some $n$ coprime to $d$ such that $c(n) \neq 1$.

Additionally, from the definition of a Dirichlet character (as referenced in `DIRICHLET_CHARACTER_EQ_0`), we know that $c(n) = 0$ if and only if $n$ is not coprime to $d$. Since we have $\gcd(n,d) = 1$, we must have $c(n) \neq 0$.

Therefore, there exists an $n$ with $\gcd(n,d) = 1$ such that $c(n) \neq 0$ and $c(n) \neq 1$.

### Mathematical insight
This theorem provides a key characterization of non-principal Dirichlet characters: they must take values other than 0 and 1. This is important in number theory, especially in the study of L-functions and the distribution of prime numbers.

The principal character $\chi_0$ only takes values 0 and 1, mapping all numbers coprime to the modulus to 1 and all others to 0. This theorem shows that any other character must have a more complex range of values.

This result is fundamental for distinguishing between principal and non-principal characters, which behave differently in many analytic contexts, particularly when studying Dirichlet L-functions.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_EQ_PRINCIPAL`: Characterizes when a Dirichlet character equals the principal character
  - `DIRICHLET_CHARACTER_EQ_0`: States that a Dirichlet character evaluates to 0 if and only if its input is not coprime to the modulus
- Definitions:
  - `dirichlet_character`: Defines the properties of a Dirichlet character modulo d
  - `chi_0`: Defines the principal character modulo d

### Porting notes
When implementing this in other proof assistants, note that:
1. The complex number representations might differ between systems
2. The theorem uses `Cx(&0)` and `Cx(&1)` which are HOL Light's way of embedding real numbers 0 and 1 into the complex plane
3. Some proof assistants might require explicit typing for the character function
4. The definition of "coprime" might need to be imported from appropriate number theory libraries

---

## DIRICHLET_CHARACTER_0

### Name of formal statement
DIRICHLET_CHARACTER_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_0 = prove
 (`!c. dirichlet_character 0 c <=> c = chi_0 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM; COPRIME_0] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_EQ_0;
                COPRIME_0]);;
```

### Informal statement
For any complex-valued function $c$ on natural numbers, $c$ is a Dirichlet character modulo $0$ if and only if $c = \chi_0(0)$, where $\chi_0(0)$ is the principal character modulo $0$.

In other words: $\forall c. \text{dirichlet\_character}(0, c) \Leftrightarrow c = \chi_0(0)$

### Informal proof
We prove both directions of the equivalence:

- ($\Leftarrow$): If $c = \chi_0(0)$, then $c$ is a Dirichlet character modulo $0$. This follows directly from the theorem `DIRICHLET_CHARACTER_CHI_0` which states that $\chi_0(d)$ is a Dirichlet character modulo $d$ for any $d$.

- ($\Rightarrow$): Assume $c$ is a Dirichlet character modulo $0$. We need to show that $c = \chi_0(0)$.
  * By definition, $\chi_0(0)(n) = \begin{cases} 1 & \text{if } \gcd(n,0) = 1 \\ 0 & \text{otherwise} \end{cases}$
  * For any natural number $n$, we consider two cases based on whether $n$ is coprime to $0$:
    - Case 1: If $\gcd(n,0) = 1$ (i.e., $n = 1$), then by `DIRICHLET_CHARACTER_EQ_1`, we have $c(1) = 1 = \chi_0(0)(1)$.
    - Case 2: If $\gcd(n,0) \neq 1$ (i.e., $n \neq 1$), then by `DIRICHLET_CHARACTER_EQ_0`, we have $c(n) = 0 = \chi_0(0)(n)$.
  * Therefore, $c(n) = \chi_0(0)(n)$ for all $n$, which means $c = \chi_0(0)$.

### Mathematical insight
This theorem characterizes Dirichlet characters modulo 0, showing that there is essentially only one such character - the principal character $\chi_0(0)$.

In number theory, Dirichlet characters are important for studying distributions of primes and for defining L-functions. This result establishes that the modulo 0 case is degenerate, with only one possible character.

The principal character $\chi_0(0)$ is particularly simple: it equals 1 when $n=1$ and 0 for all other values of $n$, since a number is coprime to 0 if and only if it equals 1.

### Dependencies
- Definitions:
  - `dirichlet_character`: Defines what it means for a function to be a Dirichlet character
  - `chi_0`: Defines the principal character

- Theorems:
  - `DIRICHLET_CHARACTER_CHI_0`: Shows that the principal character $\chi_0(d)$ is a Dirichlet character modulo $d$
  - `DIRICHLET_CHARACTER_EQ_0`: Characterizes when a Dirichlet character equals 0
  - `DIRICHLET_CHARACTER_EQ_1`: Shows that a Dirichlet character always equals 1 at input 1
  - `COPRIME_0`: Characterizes when a number is coprime to 0

### Porting notes
When porting this result to another system:
- Ensure that the definition of "coprime to 0" is consistent (usually $\gcd(n,0)=1$ iff $n=1$)
- The proof relies on function extensionality (`FUN_EQ_THM`), so ensure the target system supports this or find an appropriate workaround
- The computational/automation parts of the proof (like `COND_CASES_TAC`) might need to be replaced with more explicit reasoning in systems with different automation capabilities

---

## DIRICHLET_CHARACTER_1

### DIRICHLET_CHARACTER_1
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_1 = prove
 (`!c. dirichlet_character 1 c <=> !n. c n = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[dirichlet_character; COPRIME_1] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_REWRITE_TAC[ARITH; COMPLEX_RING
     `x = x * x <=> x = Cx(&0) \/ x = Cx(&1)`] THEN
    DISCH_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN ASM_REWRITE_TAC[ARITH] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;
```

### Informal statement
For all complex-valued functions $c$ on the natural numbers, the function $c$ is a Dirichlet character with modulus 1 if and only if $c(n) = 1$ for all natural numbers $n$.

In other words:
$$\forall c.\ \text{dirichlet\_character}(1, c) \iff \forall n.\ c(n) = 1$$

### Informal proof
We prove the equivalence by expanding the definition of `dirichlet_character` and showing both directions of the implication.

First, recall that a Dirichlet character with modulus $d$ satisfies:
- Periodicity: $\forall n.\ c(n+d) = c(n)$
- Zero values: $\forall n.\ c(n) = 0 \iff \text{not}\ \text{coprime}(n,d)$
- Multiplicativity: $\forall m,n.\ c(m \cdot n) = c(m) \cdot c(n)$

For the forward direction ($\Rightarrow$):
- Assume $c$ is a Dirichlet character with modulus 1.
- From the definition, we know that $c(1 \cdot 1) = c(1) \cdot c(1)$, which means $c(1) = c(1) \cdot c(1)$.
- This implies $c(1) = 0$ or $c(1) = 1$.
- But since 1 is coprime to 1, the definition ensures $c(1) \neq 0$.
- Therefore, $c(1) = 1$.
- We prove for all $n$ by induction:
  - Base case: We've shown $c(1) = 1$.
  - Induction step: Suppose $c(n) = 1$.
  - We need to show $c(n+1) = 1$.
  - Since the modulus is 1, we have $c(n+1) = c(n+1-1) = c(n)$ by periodicity.
  - Therefore, $c(n+1) = c(n) = 1$.

For the reverse direction ($\Leftarrow$):
- Assume $c(n) = 1$ for all $n$.
- The three conditions for a Dirichlet character with modulus 1 are trivially satisfied:
  - Periodicity: $c(n+1) = 1 = c(n)$ for all $n$.
  - Zero values: $c(n) = 1 \neq 0$ for all $n$, and all numbers are coprime to 1.
  - Multiplicativity: $c(m \cdot n) = 1 = c(m) \cdot c(n)$ for all $m, n$.

### Mathematical insight
This theorem characterizes Dirichlet characters of modulus 1, showing that there is only one such character - the trivial character that maps every number to 1.

Dirichlet characters are important in number theory, particularly in the study of Dirichlet L-functions and in the proof of Dirichlet's theorem on primes in arithmetic progressions. This result identifies the simplest case of a Dirichlet character, which serves as a baseline case in many proofs and constructions.

The fact that the only Dirichlet character with modulus 1 is the trivial character aligns with number-theoretic intuition: the modulus 1 case is degenerate since every number is coprime to 1, so the character must be non-zero everywhere, and multiplicativity forces it to be constantly 1.

### Dependencies
- Definitions:
  - `dirichlet_character`: Definition of a Dirichlet character with modulus d as a function satisfying periodicity, specific zero values, and multiplicativity.
- Theorems:
  - `COPRIME_1`: Every number is coprime to 1.

### Porting notes
When porting to other proof assistants:
- Ensure the definition of Dirichlet character is properly translated with all three conditions.
- The proof relies on simple properties of complex numbers, particularly that if $x = x \cdot x$ then $x = 0$ or $x = 1$, which might need explicit lemmas in other systems.
- The induction step uses periodicity in a way that might not be immediately obvious to automation in other systems.

---

## DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Name of formal statement
DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(d = 0) /\ ~(d = 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_0; TAUT `~(p /\ ~p)`] THEN
  ASM_CASES_TAC `d = 1` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_1; chi_0; FUN_EQ_THM; COPRIME_1] THEN
  CONV_TAC TAUT);;
```

### Informal statement
For any modulus $d$ and character $c$, if $c$ is a Dirichlet character modulo $d$ and $c$ is not the principal character $\chi_0$ modulo $d$, then $d$ is neither $0$ nor $1$.

In other words, if $c$ is a non-principal Dirichlet character modulo $d$, then $d > 1$.

### Informal proof
The proof proceeds by case analysis on $d$:

1. First, we consider the case where $d = 0$.
   - By the theorem `DIRICHLET_CHARACTER_0`, we know that $c$ is a Dirichlet character modulo $0$ if and only if $c = \chi_0(0)$.
   - This directly contradicts our assumption that $c \neq \chi_0(d)$.

2. Next, we consider the case where $d = 1$.
   - By the theorem `DIRICHLET_CHARACTER_1`, all Dirichlet characters modulo 1 satisfy $c(n) = 1$ for all $n$.
   - The principal character $\chi_0(1)$ is defined as $\chi_0(1)(n) = 1$ if $\gcd(n,1) = 1$ (which is true for all $n$), and $0$ otherwise.
   - Therefore, $\chi_0(1)(n) = 1$ for all $n$, which means any Dirichlet character modulo $1$ must equal $\chi_0(1)$.
   - This contradicts our assumption that $c \neq \chi_0(d)$.

3. Since both cases lead to contradictions, we conclude that if $c$ is a non-principal Dirichlet character modulo $d$, then $d > 1$.

### Mathematical insight
This theorem establishes a fundamental property of Dirichlet characters: non-principal characters can only exist for moduli greater than 1. This makes sense in the context of number theory because:

- When $d = 0$, the definition of Dirichlet character forces all characters to be the principal character.
- When $d = 1$, all integers are coprime to 1, so any Dirichlet character must take the value 1 everywhere, making it the principal character.

This result is important in the theory of Dirichlet characters and L-functions, as it tells us that to find interesting (non-principal) characters, we must look at moduli $d \geq 2$. Non-principal characters are crucial in analytic number theory, particularly in the proof of Dirichlet's theorem on primes in arithmetic progressions.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_0`: Characterizes Dirichlet characters modulo 0
  - `DIRICHLET_CHARACTER_1`: Characterizes Dirichlet characters modulo 1
- Definitions:
  - `dirichlet_character`: Defines the properties of a Dirichlet character
  - `chi_0`: Defines the principal character

### Porting notes
When porting this to other systems, note that:
- The definition of Dirichlet characters may vary slightly between different formalizations, particularly regarding how the case $d=0$ is handled.
- Some systems might prefer to define Dirichlet characters only for $d \geq 1$ and handle the case $d=0$ separately or exclude it.
- The proof is straightforward and should translate easily to other systems once the dependencies are in place.

---

## DIRICHLET_CHARACTER_ZEROSUM

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ZEROSUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..d) c = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(COMPLEX_RING
   `!x. x * c = c /\ ~(x = Cx(&1)) ==> c = Cx(&0)`) THEN
  EXISTS_TAC `(c:num->complex) m` THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(MESON[]
   `!t. vsum t f = vsum s f /\ vsum t g = vsum s g /\ vsum t f = vsum t g
        ==> vsum s f = vsum s g`) THEN
  EXISTS_TAC `{n | coprime(n,d) /\ n < d}` THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_NUMSEG; LT_IMP_LE; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THENL
     [ASM_CASES_TAC `r = 0` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[COPRIME_0];
      ASM_CASES_TAC `coprime(r,d)` THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `r:num = d` THEN ASM_REWRITE_TAC[LT_REFL] THENL
         [ASM_MESON_TAC[COPRIME_REFL]; ASM_ARITH_TAC];
        REWRITE_TAC[COMPLEX_VEC_0] THEN
        ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]];
    ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_MUL (CONJUNCT1 th))]) THEN
  SIMP_TAC[VSUM; PHI_FINITE_LEMMA] THEN
  MATCH_MP_TAC ITERATE_OVER_COPRIME THEN SIMP_TAC[MONOIDAL_VECTOR_ADD] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG]);;
```

### Informal statement
For any modulus $d$ and Dirichlet character $c$ modulo $d$, if $c$ is not the principal character $\chi_0$ modulo $d$, then:

$$\sum_{n=1}^{d} c(n) = 0$$

where the sum is taken over all integers from $1$ to $d$ inclusive, and the result is in the complex plane.

### Informal proof
The proof demonstrates that the sum of values of any non-principal Dirichlet character over a complete residue system modulo $d$ equals zero.

- First, we establish that if $c$ is a non-principal character modulo $d$, then $d \neq 0$ and $d \neq 1$ (using `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`).

- Since $c$ is non-principal, there exists some $m$ coprime to $d$ such that $c(m) \neq 0$ and $c(m) \neq 1$ (using `DIRICHLET_CHARACTER_NONPRINCIPAL`).

- To prove the sum is zero, we show that $c(m) \cdot \sum_{n=1}^{d} c(n) = \sum_{n=1}^{d} c(n)$ where $c(m) \neq 1$. This implies the sum must be zero.

- We simplify our task by focusing on the subset of integers coprime to $d$ and less than $d$, as all other terms in the original sum contribute zero (by the definition of a Dirichlet character).

- For this subset, we show that multiplication by $m$ (modulo $d$) permutes the elements, and the character values remain invariant under this permutation due to the multiplicative property of Dirichlet characters. Specifically:
  $$\sum_{n \in \{r \mid \gcd(r,d)=1, r < d\}} c(m \cdot n) = \sum_{n \in \{r \mid \gcd(r,d)=1, r < d\}} c(n)$$

- Since $c(m \cdot n) = c(m) \cdot c(n)$ by the multiplicative property of Dirichlet characters, we have:
  $$c(m) \cdot \sum_{n \in \{r \mid \gcd(r,d)=1, r < d\}} c(n) = \sum_{n \in \{r \mid \gcd(r,d)=1, r < d\}} c(n)$$

- Given that $c(m) \neq 1$, the only solution is that the sum equals zero.

### Mathematical insight
This theorem captures a fundamental orthogonality property of non-principal Dirichlet characters: their sum over a complete residue system modulo $d$ vanishes. This is analogous to how non-trivial characters of a finite group sum to zero over the group elements.

This property is crucial in the development of Dirichlet's theorem on primes in arithmetic progressions. The orthogonality relations between Dirichlet characters enable the sieving of specific arithmetic progressions, which is key to studying the distribution of primes in these progressions.

The vanishing sum also reflects the deeper algebraic structure of Dirichlet characters as homomorphisms from the multiplicative group of units modulo $d$ to the complex numbers.

### Dependencies
- Theorems:
  - `PHI_FINITE_LEMMA`: The set of numbers less than n and coprime to n is finite
  - `ITERATE_OVER_COPRIME`: Theorem about iterating functions over coprime residues
  - `DIRICHLET_CHARACTER_EQ_0`: A Dirichlet character equals zero exactly when its input is not coprime to the modulus
  - `DIRICHLET_CHARACTER_MUL`: Multiplicative property of Dirichlet characters
  - `DIRICHLET_CHARACTER_CONG`: Dirichlet characters depend only on congruence class modulo d
  - `DIRICHLET_CHARACTER_NONPRINCIPAL`: A non-principal character has values other than 0 or 1
  - `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`: Non-principal characters exist only for moduli > 1

- Definitions:
  - `dirichlet_character`: Defines the three key properties of Dirichlet characters (periodicity, zeros at non-coprime inputs, and multiplicativity)
  - `chi_0`: The principal Dirichlet character which equals 1 for inputs coprime to the modulus and 0 otherwise

### Porting notes
When implementing this result in other systems:
1. The proof technique relies on manipulating finite sums of complex numbers, so ensure that the target system has adequate support for complex arithmetic and finite summations.
2. The theorem uses the fact that multiplication by a unit modulo $d$ permutes the set of units modulo $d$, which might require a separate lemma in some proof assistants.
3. Ensure the target system correctly handles the zero and trivial cases for Dirichlet characters, as edge cases around $d=0$ and $d=1$ need special treatment.

---

## DIRICHLET_CHARACTER_ZEROSUM_MUL

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM_MUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ZEROSUM_MUL = prove
 (`!d c n. dirichlet_character d c /\ ~(c = chi_0 d)
           ==> vsum(1..d*n) c = Cx(&0)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH; COMPLEX_VEC_0] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;
```

### Informal statement
For any positive integer $d$, any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0(d)$, and any natural number $n$, the sum of the values of $c$ over the interval $[1, d \cdot n]$ is zero:

$$\forall d,c,n.\ \text{dirichlet\_character}(d,c) \land c \neq \chi_0(d) \Rightarrow \sum_{i=1}^{d \cdot n} c(i) = 0$$

### Informal proof
We prove this theorem by induction on $n$.

**Base case**: When $n = 0$, we have $d \cdot 0 = 0$, so the sum is over an empty interval $[1,0]$, which equals $0$ by definition.

**Inductive step**: Assume the result holds for $n$, i.e., $\sum_{i=1}^{d \cdot n} c(i) = 0$. We need to show it holds for $n+1$.

We have:
$$\sum_{i=1}^{d(n+1)} c(i) = \sum_{i=1}^{dn} c(i) + \sum_{i=dn+1}^{d(n+1)} c(i)$$

By the induction hypothesis, $\sum_{i=1}^{dn} c(i) = 0$.

For the second sum, we make a variable substitution $j = i - dn$, which transforms:
$$\sum_{i=dn+1}^{d(n+1)} c(i) = \sum_{j=1}^{d} c(j+dn)$$

Since $c$ is a Dirichlet character modulo $d$, it has period $d$, so $c(j+dn) = c(j)$ for all $j$. Therefore:
$$\sum_{j=1}^{d} c(j+dn) = \sum_{j=1}^{d} c(j)$$

By the `DIRICHLET_CHARACTER_ZEROSUM` theorem, since $c$ is not the principal character, $\sum_{j=1}^{d} c(j) = 0$.

Therefore, $\sum_{i=1}^{d(n+1)} c(i) = 0 + 0 = 0$, which completes the proof.

### Mathematical insight
This theorem extends the result about Dirichlet characters summing to zero over a complete period (as stated in `DIRICHLET_CHARACTER_ZEROSUM`) to sums over multiple periods. It shows that the zero-sum property holds not just over a single period $[1,d]$ but over any number of consecutive periods $[1,d\cdot n]$.

This orthogonality property of non-principal Dirichlet characters is fundamental in analytic number theory, particularly in the study of Dirichlet $L$-functions and applications to problems like the distribution of primes in arithmetic progressions.

### Dependencies
#### Theorems
- `DIRICHLET_CHARACTER_CONG`: If $c$ is a Dirichlet character modulo $d$ and $m \equiv n \pmod{d}$, then $c(m) = c(n)$.
- `DIRICHLET_CHARACTER_ZEROSUM`: For a non-principal Dirichlet character $c$ modulo $d$, the sum $\sum_{i=1}^{d} c(i) = 0$.

#### Definitions
- `dirichlet_character`: A function $c$ from natural numbers to complex numbers is a Dirichlet character modulo $d$ if:
  1. It has period $d$: $c(n+d) = c(n)$ for all $n$
  2. $c(n) = 0$ if and only if $\gcd(n,d) > 1$
  3. $c$ is completely multiplicative: $c(mn) = c(m)c(n)$ for all $m,n$
- `chi_0`: The principal character modulo $d$: $\chi_0(d)(n) = 1$ if $\gcd(n,d) = 1$, and $0$ otherwise.

### Porting notes
When porting this theorem:
1. Ensure that the definition of Dirichlet characters matches exactly, particularly regarding their periodicity and multiplicative properties.
2. The proof relies heavily on the structure of sums and the periodicity of Dirichlet characters.
3. The `NUMBER_TAC` tactic in HOL Light handles the modular arithmetic proof at the end; you'll need to explicitly prove that $i \equiv i+d\cdot n \pmod{d}$ in other systems.

---

## DIRICHLET_CHARACTER_SUM_MOD

### DIRICHLET_CHARACTER_SUM_MOD
- DIRICHLET_CHARACTER_SUM_MOD

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_MOD = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..n) c = vsum(1..(n MOD d)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM_MUL; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0(d)$, the following equality holds:

$$\sum_{i=1}^{n} c(i) = \sum_{i=1}^{n \bmod d} c(i)$$

where $n \bmod d$ is the remainder when $n$ is divided by $d$.

### Informal proof
Let $d$ be a positive integer and $c$ be a Dirichlet character modulo $d$ that is not the principal character.

First, we establish that $d > 1$ using the theorem `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`, which states that if $c$ is a non-principal character modulo $d$, then $d$ is neither 0 nor 1.

By the division theorem (referenced as `DIVISION` in the proof), we can write $n = d \cdot q + r$ where $r = n \bmod d$ is the remainder when $n$ is divided by $d$.

Now, we can split the sum:
$$\sum_{i=1}^{n} c(i) = \sum_{i=1}^{d \cdot q} c(i) + \sum_{i=d \cdot q + 1}^{d \cdot q + r} c(i)$$

For the first term, by the theorem `DIRICHLET_CHARACTER_ZEROSUM_MUL` which states that the sum of a non-principal character over a complete set of residues modulo $d$ times any integer is zero, we have:
$$\sum_{i=1}^{d \cdot q} c(i) = 0$$

For the second term, using the periodicity of Dirichlet characters:
$$\sum_{i=d \cdot q + 1}^{d \cdot q + r} c(i) = \sum_{i=1}^{r} c(d \cdot q + i) = \sum_{i=1}^{r} c(i)$$

The last equality follows from the theorem `DIRICHLET_CHARACTER_CONG`, which states that if $m \equiv n \pmod{d}$, then $c(m) = c(n)$. Here we use that $(d \cdot q + i) \equiv i \pmod{d}$.

Therefore, $\sum_{i=1}^{n} c(i) = \sum_{i=1}^{n \bmod d} c(i)$.

### Mathematical insight
This theorem effectively demonstrates that the sum of a non-principal Dirichlet character is periodic with period $d$. This periodicity property is fundamental in number theory and in the study of Dirichlet $L$-functions.

The result highlights that to compute the sum of a character up to any bound $n$, we only need to compute the sum up to $n \bmod d$, which can significantly reduce computational complexity when $n$ is large compared to $d$.

This property is particularly useful in analytical number theory, especially in the study of Dirichlet $L$-functions and in establishing properties of the distribution of primes in arithmetic progressions.

### Dependencies
#### Theorems
- `DIRICHLET_CHARACTER_CONG`: If $m \equiv n \pmod{d}$ and $c$ is a Dirichlet character modulo $d$, then $c(m) = c(n)$.
- `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`: If $c$ is a non-principal Dirichlet character modulo $d$, then $d > 1$.
- `DIRICHLET_CHARACTER_ZEROSUM`: If $c$ is a non-principal Dirichlet character modulo $d$, then $\sum_{i=1}^{d} c(i) = 0$.
- `DIRICHLET_CHARACTER_ZEROSUM_MUL`: If $c$ is a non-principal Dirichlet character modulo $d$, then $\sum_{i=1}^{d \cdot n} c(i) = 0$ for any positive integer $n$.

#### Definitions
- `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function $c$ satisfying periodicity ($c(n+d) = c(n)$), character property ($c(m \cdot n) = c(m) \cdot c(n)$), and zero value condition ($c(n) = 0$ if and only if $\gcd(n,d) \neq 1$).
- `chi_0`: Defines the principal character modulo $d$ as $\chi_0(d)(n) = 1$ if $\gcd(n,d) = 1$ and $0$ otherwise.

### Porting notes
When porting this theorem, ensure that the Dirichlet character definition includes the necessary properties: periodicity, multiplicativity, and the relationship between zero values and coprimality. The proof relies on the division theorem and properties of modular arithmetic, which should be available in most proof assistants, though the exact formulation may differ.

---

## FINITE_DIRICHLET_CHARACTERS

### FINITE_DIRICHLET_CHARACTERS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FINITE_DIRICHLET_CHARACTERS = prove
 (`!d. FINITE {c | dirichlet_character d c}`,
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_SIMP_TAC[DIRICHLET_CHARACTER_0; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[FINITE_RULES];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\c n. c(n MOD d))
                    {c | (!m. m IN {m | m < d}
                             ==> c(m) IN (Cx(&0) INSERT
                                          {z | z pow (phi d) = Cx(&1)})) /\
                         (!m. ~(m IN {m | m < d})
                              ==> c(m) = Cx(&0))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; FINITE_INSERT] THEN
    MATCH_MP_TAC FINITE_COMPLEX_ROOTS_UNITY THEN
    ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG; LE_1];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
  DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INSERT] THEN
  EXISTS_TAC `\n:num. if n < d then c(n) else Cx(&0)` THEN
  ASM_SIMP_TAC[DIVISION; FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THENL
   [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
    ASM_MESON_TAC[CONG_MOD; CONG_SYM];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_ROOT; COPRIME_SYM;
                  DIRICHLET_CHARACTER_EQ_0]]);;
```

### Informal statement
The theorem states that for any natural number $d$, the set of Dirichlet characters modulo $d$ is finite:

$$\forall d \in \mathbb{N}. \text{FINITE } \{c \mid \text{dirichlet\_character } d \, c\}$$

Where a Dirichlet character $c$ modulo $d$ is a function $c: \mathbb{N} \to \mathbb{C}$ satisfying:
- $c(n+d) = c(n)$ for all $n$ (periodicity)
- $c(n) = 0$ if and only if $\gcd(n,d) > 1$ (detection of non-coprime numbers)
- $c(m \cdot n) = c(m) \cdot c(n)$ for all $m,n$ (multiplicativity)

### Informal proof

The proof proceeds by case analysis on whether $d = 0$ or $d \neq 0$.

* Case $d = 0$:
  - When $d = 0$, by the theorem `DIRICHLET_CHARACTER_0`, there is exactly one Dirichlet character modulo 0, namely $\chi_0(0)$.
  - A singleton set is finite, so the result follows.

* Case $d \neq 0$:
  - The proof shows that the set of all Dirichlet characters modulo $d$ is a subset of a finite set, and thus finite.
  - We define a set of functions mapping numbers to either 0 or to a $\phi(d)$-th root of unity, where $\phi$ is Euler's totient function.
  - Specifically, we consider functions $c$ where:
    1. For $m < d$, $c(m) \in \{0\} \cup \{z \mid z^{\phi(d)} = 1\}$ 
    2. For $m \geq d$, $c(m) = 0$
  - These functions can be uniquely identified by their values on $\{m \mid m < d\}$.
  - We can map any Dirichlet character to such a function via $c \mapsto \lambda n.c(n \bmod d)$.
  - The theorem `FINITE_COMPLEX_ROOTS_UNITY` ensures that the set of $\phi(d)$-th roots of unity is finite.
  - Since $\phi(d) \geq 1$ for $d \neq 0$, and we're considering functions with finite domain and finite codomain, the resulting set is finite.
  - To show this is a valid mapping, we use:
    - `DIRICHLET_CHARACTER_CONG` to show that Dirichlet characters respect congruence modulo $d$
    - `DIRICHLET_CHARACTER_ROOT` to show that for $n$ coprime to $d$, $c(n)^{\phi(d)} = 1$
    - `DIRICHLET_CHARACTER_EQ_0` to handle the case where $n$ is not coprime to $d$

Therefore, for any $d$, the set of Dirichlet characters modulo $d$ is finite.

### Mathematical insight

Dirichlet characters are fundamental objects in number theory, especially in the study of L-functions and the distribution of primes in arithmetic progressions. This theorem establishes that there are only finitely many Dirichlet characters modulo any given number $d$.

The proof reveals the structure of Dirichlet characters:
- For $d = 0$, there is exactly one character.
- For $d > 0$, characters are determined by their values on the reduced residue system modulo $d$.
- These values must be either 0 (for non-coprime values) or roots of unity of order dividing $\phi(d)$ (for coprime values).

This theorem is a prerequisite for many results in analytic number theory, particularly those involving sums over characters. The finiteness allows for various limiting arguments and ensures that such sums are well-defined.

While not stated explicitly in this theorem, the exact count of Dirichlet characters modulo $d$ is $\phi(d)$, which corresponds to the size of the multiplicative group modulo $d$.

### Dependencies

**Theorems:**
- `DIRICHLET_CHARACTER_0`: Characterizes Dirichlet characters modulo 0
- `DIRICHLET_CHARACTER_CONG`: Shows that Dirichlet characters respect congruence
- `DIRICHLET_CHARACTER_ROOT`: Shows that for $n$ coprime to $d$, $c(n)^{\phi(d)} = 1$
- `DIRICHLET_CHARACTER_EQ_0`: Characterizes when a Dirichlet character equals zero
- `FINITE_COMPLEX_ROOTS_UNITY`: Shows finiteness of complex roots of unity
- `CONG_MOD`: Shows that $a \bmod n \equiv a \pmod{n}$

**Definitions:**
- `dirichlet_character`: Defines the conditions for a function to be a Dirichlet character

### Porting notes
When porting this result:
1. Ensure that your definition of Dirichlet characters matches the one used here.
2. The proof relies heavily on the properties of Dirichlet characters, so make sure those are established first.
3. The proof also uses properties of modular arithmetic and complex roots of unity, which may require different approaches in other systems.
4. Some proof assistants may require more detailed arguments about the finiteness of function spaces with finite domain and codomain.

---

## DIRICHLET_CHARACTER_MUL_CNJ

### Name of formal statement
DIRICHLET_CHARACTER_MUL_CNJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_MUL_CNJ = prove
 (`!d c n. dirichlet_character d c /\ ~(c n = Cx(&0))
           ==> cnj(c n) * c n = Cx(&1) /\ c n * cnj(c n) = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `inv z = w /\ ~(z = Cx(&0)) ==> w * z = Cx(&1) /\ z * w = Cx(&1)`) THEN
  ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPLEX_NORM_NZ]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL; COMPLEX_POW_ONE] THEN
  REWRITE_TAC[COMPLEX_DIV_1]);;
```

### Informal statement
For any numbers $d$ and $n$, and a Dirichlet character $c$, if $c$ is a Dirichlet character modulo $d$ and $c(n) \neq 0$, then:
$$\overline{c(n)} \cdot c(n) = 1 \quad \text{and} \quad c(n) \cdot \overline{c(n)} = 1$$

where $\overline{c(n)}$ denotes the complex conjugate of $c(n)$.

### Informal proof
We will prove that when $c$ is a Dirichlet character and $c(n) \neq 0$, then $c(n)$ has magnitude 1 and its complex conjugate equals its multiplicative inverse.

First, we can use a basic complex analysis fact: if $z \neq 0$ and $w = 1/z$, then $wz = 1$ and $zw = 1$.

We set $z = c(n)$ and $w = \overline{c(n)}$, and we need to show that $\overline{c(n)} = 1/c(n)$.

By the property of complex numbers, $1/z = \overline{z}/|z|^2$. So:
$$\frac{1}{c(n)} = \frac{\overline{c(n)}}{|c(n)|^2}$$

From the theorem `DIRICHLET_CHARACTER_NORM`, we know that for any Dirichlet character $c$ modulo $d$:
$$|c(n)| = \begin{cases} 
1 & \text{if } \gcd(d,n) = 1 \\
0 & \text{otherwise}
\end{cases}$$

Since we're given that $c(n) \neq 0$, we must have $\gcd(d,n) = 1$, which means $|c(n)| = 1$.

Therefore:
$$\frac{1}{c(n)} = \frac{\overline{c(n)}}{|c(n)|^2} = \frac{\overline{c(n)}}{1} = \overline{c(n)}$$

Thus, $\overline{c(n)} = 1/c(n)$, which implies $\overline{c(n)} \cdot c(n) = 1$ and $c(n) \cdot \overline{c(n)} = 1$.

### Mathematical insight
This theorem establishes that non-zero values of a Dirichlet character are complex numbers of unit modulus (i.e., they lie on the unit circle in the complex plane). This is a fundamental property that reveals the group structure of Dirichlet characters: the non-zero values form a subgroup of the unit circle.

The result is important because it shows that Dirichlet characters take values in the unit circle of the complex plane, which connects them to roots of unity and gives them a natural group structure. This property is essential in analytic number theory, particularly in the study of Dirichlet L-functions and their applications to prime number theory.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_NORM`: States that for a Dirichlet character $c$ modulo $d$, the norm $|c(n)|$ equals 1 if $\gcd(d,n)=1$ and 0 otherwise.

- **Definitions**:
  - `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function $c$ such that:
    1. $c(n+d) = c(n)$ for all $n$ (periodicity)
    2. $c(n) = 0$ if and only if $\gcd(n,d) \neq 1$ (support property)
    3. $c(mn) = c(m)c(n)$ for all $m,n$ (multiplicativity)

### Porting notes
When implementing this in other proof assistants, note that:
1. The proof relies on complex analysis results about conjugates and inverses
2. It uses the characterization of Dirichlet characters having unit norm when evaluated at numbers coprime to the modulus
3. The complex field automation in HOL Light handles much of the algebraic manipulation; other systems may need explicit steps for complex number properties

---

## DIRICHLET_CHARACTER_CNJ

### DIRICHLET_CHARACTER_CNJ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CNJ = prove
 (`!d c. dirichlet_character d c ==> dirichlet_character d (\n. cnj(c n))`,
  SIMP_TAC[dirichlet_character; CNJ_MUL; CNJ_EQ_CX]);;
```

### Informal statement
For any positive integer $d$ and function $c: \mathbb{N} \rightarrow \mathbb{C}$, if $c$ is a Dirichlet character modulo $d$, then the function $n \mapsto \overline{c(n)}$ (where $\overline{c(n)}$ denotes the complex conjugate of $c(n)$) is also a Dirichlet character modulo $d$.

### Informal proof
To prove this theorem, we need to show that the complex conjugate of a Dirichlet character satisfies all the defining properties of a Dirichlet character.

Let $d$ be a positive integer and $c: \mathbb{N} \rightarrow \mathbb{C}$ be a Dirichlet character modulo $d$. Define $c': \mathbb{N} \rightarrow \mathbb{C}$ by $c'(n) = \overline{c(n)}$. We need to verify that $c'$ satisfies all conditions of a Dirichlet character:

1. **Periodicity**: For all $n$, $c'(n + d) = c'(n)$
   This follows directly from the periodicity of $c$:
   $c'(n + d) = \overline{c(n + d)} = \overline{c(n)} = c'(n)$

2. **Vanishing condition**: For all $n$, $c'(n) = 0$ if and only if $n$ and $d$ are not coprime
   Since $\overline{c(n)} = 0$ if and only if $c(n) = 0$ (as the conjugate of 0 is 0), and we know that $c(n) = 0$ if and only if $n$ and $d$ are not coprime, this property holds for $c'$.

3. **Multiplicativity**: For all $m, n$, $c'(m \cdot n) = c'(m) \cdot c'(n)$
   Using the fact that the conjugate of a product is the product of the conjugates:
   $c'(m \cdot n) = \overline{c(m \cdot n)} = \overline{c(m) \cdot c(n)} = \overline{c(m)} \cdot \overline{c(n)} = c'(m) \cdot c'(n)$

The proof uses the properties `CNJ_MUL` (conjugate of a product is the product of conjugates) and `CNJ_EQ_CX` (equality of complex conjugates) to efficiently establish these conditions.

### Mathematical insight
This theorem establishes that the set of Dirichlet characters modulo $d$ is closed under complex conjugation. This is an important property for the theory of Dirichlet characters and has implications for the theory of L-functions.

The complex conjugate of a Dirichlet character is sometimes called the "dual" character, and it plays a crucial role in various aspects of analytic number theory, including functional equations of L-functions and orthogonality relations among characters.

This closure property is analogous to how the set of group characters (homomorphisms from a group to the multiplicative group of complex numbers) is closed under complex conjugation, which is a fundamental fact in representation theory.

### Dependencies
- **Definitions**:
  - `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function from natural numbers to complex numbers satisfying periodicity, the vanishing condition, and multiplicativity.

- **Theorems**:
  - `CNJ_MUL`: The conjugate of a product is the product of conjugates.
  - `CNJ_EQ_CX`: Relates equality of complex conjugates to the original complex numbers.

### Porting notes
When porting this theorem:
- Ensure your target system's complex number library includes properties of complex conjugation, particularly that conjugation distributes over multiplication.
- The proof is straightforward once the definition of Dirichlet character is established, making it a good candidate for automation.
- Check that your definition of Dirichlet character uses the same conventions, particularly regarding when characters vanish.

---

## DIRICHLET_CHARACTER_GROUPMUL

### DIRICHLET_CHARACTER_GROUPMUL

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPMUL = prove
 (`!d c1 c2. dirichlet_character d c1 /\ dirichlet_character d c2
             ==> dirichlet_character d (\n. c1(n) * c2(n))`,
  SIMP_TAC[dirichlet_character; COMPLEX_ENTIRE] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;
```

### Informal statement
Let $d$ be a positive integer. If $c_1$ and $c_2$ are both Dirichlet characters modulo $d$, then the pointwise product $n \mapsto c_1(n) \cdot c_2(n)$ is also a Dirichlet character modulo $d$.

More formally, for any integer $d$ and functions $c_1, c_2: \mathbb{N} \to \mathbb{C}$, if $c_1$ and $c_2$ are Dirichlet characters modulo $d$, then the function $n \mapsto c_1(n) \cdot c_2(n)$ is also a Dirichlet character modulo $d$.

### Informal proof
To prove that the pointwise product of two Dirichlet characters is also a Dirichlet character, we need to verify three conditions from the definition of `dirichlet_character`:

1. $c(n+d) = c(n)$ for all $n$ (periodicity)
2. $c(n) = 0$ if and only if $n$ and $d$ are not coprime
3. $c(m \cdot n) = c(m) \cdot c(n)$ for all $m, n$ (multiplicativity)

Let $c(n) = c_1(n) \cdot c_2(n)$ be the pointwise product. 

For condition 1, for all $n$:
$c(n+d) = c_1(n+d) \cdot c_2(n+d) = c_1(n) \cdot c_2(n) = c(n)$

For condition 2, for all $n$:
$c(n) = 0$ if and only if $c_1(n) \cdot c_2(n) = 0$
This happens if and only if either $c_1(n) = 0$ or $c_2(n) = 0$
By the definition of Dirichlet characters, this is equivalent to $n$ and $d$ not being coprime.

For condition 3, for all $m, n$:
$c(m \cdot n) = c_1(m \cdot n) \cdot c_2(m \cdot n) = (c_1(m) \cdot c_1(n)) \cdot (c_2(m) \cdot c_2(n))$
By associativity and commutativity of complex multiplication, this equals:
$(c_1(m) \cdot c_2(m)) \cdot (c_1(n) \cdot c_2(n)) = c(m) \cdot c(n)$

The proof in HOL Light uses simplification with the definition of Dirichlet character and properties of complex multiplication (entirety, associativity, and commutativity) to establish these conditions.

### Mathematical insight
This theorem establishes that Dirichlet characters modulo $d$ form a group under pointwise multiplication. This is an important algebraic property that allows for the construction of new characters from existing ones. The group structure of Dirichlet characters is fundamental in analytic number theory, particularly in the study of Dirichlet L-functions and their applications to the distribution of primes in arithmetic progressions.

The closure under multiplication is one step toward showing that the set of Dirichlet characters modulo $d$ forms a finite abelian group, which is isomorphic to the group $(\mathbb{Z}/d\mathbb{Z})^*$, the multiplicative group of units modulo $d$.

### Dependencies
#### Definitions
- `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function $c: \mathbb{N} \to \mathbb{C}$ satisfying three properties: it is periodic with period $d$, it is zero exactly when the input is not coprime to $d$, and it is multiplicative.

#### Theorems
- `COMPLEX_ENTIRE`: States that the product of two complex numbers is zero if and only if at least one of the factors is zero.
- `COMPLEX_MUL_AC`: States the associativity and commutativity properties of complex multiplication.

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the definition of Dirichlet character includes all three conditions: periodicity, behavior on non-coprime inputs, and multiplicativity.
2. The proof relies on properties of complex numbers, particularly the fact that a product is zero if and only if at least one factor is zero. This property needs to be available in the target system.
3. The proof also uses associativity and commutativity of complex multiplication, which should be standard in most proof assistants.

---

## DIRICHLET_CHARACTER_GROUPINV

### DIRICHLET_CHARACTER_GROUPINV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPINV = prove
 (`!d c. dirichlet_character d c ==> (\n. cnj(c n) * c n) = chi_0 d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_MUL_CNJ; DIRICHLET_CHARACTER_EQ_0];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$, the function $n \mapsto \overline{c(n)} \cdot c(n)$ equals $\chi_0^d$, where $\chi_0^d$ is the principal character modulo $d$ defined as:

$$\chi_0^d(n) = \begin{cases} 1 & \text{if } \gcd(n,d) = 1 \\ 0 & \text{otherwise} \end{cases}$$

Here, $\overline{c(n)}$ denotes the complex conjugate of $c(n)$.

### Informal proof
To prove this theorem, we need to show that for all integers $n$, $\overline{c(n)} \cdot c(n) = \chi_0^d(n)$.

First, we consider two cases based on whether $n$ is coprime to $d$.

Case 1: When $\gcd(n,d) = 1$ (i.e., $n$ is coprime to $d$)
- In this case, $\chi_0^d(n) = 1$ by definition.
- Since $c$ is a Dirichlet character and $\gcd(n,d) = 1$, we know $c(n) \neq 0$ (from the property of Dirichlet characters).
- By the theorem `DIRICHLET_CHARACTER_MUL_CNJ`, when $c(n) \neq 0$, we have $\overline{c(n)} \cdot c(n) = 1$.
- Therefore, $\overline{c(n)} \cdot c(n) = 1 = \chi_0^d(n)$ in this case.

Case 2: When $\gcd(n,d) > 1$ (i.e., $n$ is not coprime to $d$)
- In this case, $\chi_0^d(n) = 0$ by definition.
- Since $c$ is a Dirichlet character and $\gcd(n,d) > 1$, we have $c(n) = 0$ (from the property of Dirichlet characters).
- Therefore, $\overline{c(n)} \cdot c(n) = \overline{0} \cdot 0 = 0 = \chi_0^d(n)$ in this case.

Thus, for all integers $n$, $\overline{c(n)} \cdot c(n) = \chi_0^d(n)$, which completes the proof.

### Mathematical insight
This theorem establishes an important property of Dirichlet characters - the product of a character value with its complex conjugate gives the principal character. This result is crucial because:

1. It demonstrates that for any non-zero value of a Dirichlet character (which occurs precisely when $\gcd(n,d) = 1$), the absolute value is 1. This confirms the character values lie on the unit circle in the complex plane.

2. It establishes that Dirichlet characters form a group under pointwise multiplication, with the complex conjugate of a character serving as its inverse.

3. The principal character $\chi_0^d$ serves as the identity element in this group structure.

This result is fundamental in the theory of Dirichlet L-functions and has important applications in analytic number theory, particularly in the study of arithmetic progressions and distribution of primes.

### Dependencies
- **Theorems:**
  - `DIRICHLET_CHARACTER_EQ_0`: States that for a Dirichlet character $c$ modulo $d$, $c(n) = 0$ if and only if $\gcd(n,d) > 1$.
  - `DIRICHLET_CHARACTER_MUL_CNJ`: Shows that for a Dirichlet character $c$ modulo $d$ and $n$ such that $c(n) \neq 0$, the product $\overline{c(n)} \cdot c(n) = 1$.

- **Definitions:**
  - `dirichlet_character`: Defines the essential properties of a Dirichlet character.
  - `chi_0`: Defines the principal character modulo $d$.

### Porting notes
When porting this theorem to another proof assistant:

1. Ensure the definition of Dirichlet characters includes the three key properties: periodicity, multiplicativity, and the exact characterization of when the character equals zero.

2. The proof relies heavily on case analysis based on whether integers are coprime to the modulus. Make sure the target system has appropriate tools for handling such case distinctions.

3. The result depends on complex number properties, particularly conjugation. Ensure the target system has an adequate complex number theory library with conjugation operations.

---

## DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_NUMBERS = prove
 (`!d c. dirichlet_character d c
         ==> vsum (1..d) c = if c = chi_0 d then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[chi_0] THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG; GSYM COMPLEX_VEC_0] THEN
  SIMP_TAC[phi; VSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `coprime(x,d)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;
```

### Informal statement
For all positive integers $d$ and Dirichlet characters $c$ modulo $d$, the sum of the character values over all numbers from 1 to $d$ is:

$$\sum_{n=1}^d c(n) = \begin{cases}
\phi(d) & \text{if } c = \chi_0^d \\
0 & \text{otherwise}
\end{cases}$$

where $\chi_0^d$ is the principal character modulo $d$ defined by $\chi_0^d(n) = 1$ if $\gcd(n,d) = 1$ and $\chi_0^d(n) = 0$ otherwise, and $\phi(d)$ is Euler's totient function that counts the number of integers from 1 to $d$ that are coprime to $d$.

### Informal proof
We proceed by case analysis on whether $c$ equals the principal character $\chi_0^d$ or not:

* If $c \neq \chi_0^d$, then by the theorem `DIRICHLET_CHARACTER_ZEROSUM`, we have $\sum_{n=1}^d c(n) = 0$.

* If $c = \chi_0^d$, then:
  - Substitute the definition of $\chi_0^d$ which gives $c(n) = 1$ if $\gcd(n,d) = 1$ and $c(n) = 0$ otherwise
  - The sum $\sum_{n=1}^d c(n)$ can be rewritten as $\sum_{n=1}^d [n \in S] \cdot 1$, where $S = \{n \mid 1 \leq n \leq d \text{ and } \gcd(n,d) = 1\}$ and $[n \in S]$ is the indicator function
  - This sum equals the cardinality of set $S$, which is precisely $\phi(d)$ by definition
  - Therefore, $\sum_{n=1}^d c(n) = \phi(d)$

### Mathematical insight
This theorem establishes a fundamental orthogonality relation for Dirichlet characters. It shows that the sum of a Dirichlet character over a complete set of residues modulo $d$ is zero unless the character is the principal character (in which case it equals $\phi(d)$).

This result is critical in analytic number theory, particularly in the theory of Dirichlet L-functions. It serves as a basic building block for proving deeper orthogonality relations between different characters, which in turn are essential for studying the distribution of primes in arithmetic progressions.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_ZEROSUM`: If $c$ is a non-principal Dirichlet character modulo $d$, then the sum of $c(n)$ over all integers from 1 to $d$ equals zero.
- Definitions:
  - `dirichlet_character`: Defines the properties of a Dirichlet character modulo $d$
  - `chi_0`: Defines the principal character modulo $d$
  - `phi`: Euler's totient function (implicitly used)

### Porting notes
When porting this theorem:
1. Ensure that your system has a suitable representation of Dirichlet characters
2. The proof relies on the orthogonality property of non-principal characters, so ensure `DIRICHLET_CHARACTER_ZEROSUM` is ported first
3. The definition of the principal character and Euler's totient function should be consistent with standard mathematical definitions

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK = prove
 (`!d n. vsum {c | dirichlet_character d c} (\x. x n) = Cx(&0) \/
         coprime(n,d) /\ !c. dirichlet_character d c ==> c(n) = Cx(&1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    DISJ1_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; COMPLEX_VEC_0; DIRICHLET_CHARACTER_EQ_0]] THEN
  SUBGOAL_THEN
    `!c'. dirichlet_character d c'
          ==> vsum {c | dirichlet_character d c}
                   ((\c. c(n)) o (\c n. c'(n) * c(n))) =
              vsum {c | dirichlet_character d c} (\c. c(n))`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[o_DEF; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
    REWRITE_TAC[COMPLEX_RING `a * x = x <=> a = Cx(&1) \/ x = Cx(&0)`] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_INJECTION THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_GROUPMUL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(\c n. cnj(c'(n:num)) * c n)`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `coprime(m,d)` THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  MATCH_MP_TAC(COMPLEX_RING
    `a * b = Cx(&1) ==> a * b * x = a * b * y ==> x = y`) THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; DIRICHLET_CHARACTER_MUL_CNJ]);;
```

### Informal statement
For any positive integer $d$ and any integer $n$, the sum of the values of all Dirichlet characters modulo $d$ at $n$, denoted $\sum_{c \in \{c \mid \text{dirichlet_character } d \, c\}} c(n)$, is either:
- equal to 0, or
- if $n$ and $d$ are coprime, then all Dirichlet characters $c$ modulo $d$ satisfy $c(n) = 1$.

Here, a Dirichlet character modulo $d$ is a function $c: \mathbb{N} \rightarrow \mathbb{C}$ satisfying:
1. $c(n + d) = c(n)$ for all $n$ (periodicity)
2. $c(n) = 0$ if and only if $n$ and $d$ are not coprime
3. $c(m \cdot n) = c(m) \cdot c(n)$ for all $m, n$ (multiplicativity)

### Informal proof
We prove this theorem by considering two cases:

**Case 1:** When $n$ is not coprime to $d$ (i.e., $\gcd(n,d) > 1$).

In this case, by the definition of Dirichlet characters, for any Dirichlet character $c$ modulo $d$, we have $c(n) = 0$. Thus, the sum $\sum_{c} c(n) = 0$, satisfying the first part of the conclusion.

**Case 2:** When $n$ is coprime to $d$ (i.e., $\gcd(n,d) = 1$).

Let $c'$ be any Dirichlet character modulo $d$. Define the mapping $\phi_n: c \mapsto c'(n) \cdot c$ which transforms each character $c$ to a function where $\phi_n(c)(m) = c'(n) \cdot c(m)$.

We prove that $\phi_n$ maps the set of Dirichlet characters to itself, and is bijective:

- First, if $c$ is a Dirichlet character, then $\phi_n(c)$ is also a Dirichlet character by the closure of Dirichlet characters under multiplication.

- The function $\phi_n$ is injective: Suppose $\phi_n(c_1) = \phi_n(c_2)$ for characters $c_1$ and $c_2$. Then:
  $c'(n) \cdot c_1(m) = c'(n) \cdot c_2(m)$ for all $m$.
  
  If $\gcd(m,d) > 1$, then $c_1(m) = c_2(m) = 0$, so equality holds trivially.
  
  If $\gcd(m,d) = 1$, then $c'(n) \neq 0$ and we can multiply both sides by $\overline{c'(n)}$. Since $\overline{c'(n)} \cdot c'(n) = 1$ (because $c'(n)$ must be a root of unity when $\gcd(n,d) = 1$), we get $c_1(m) = c_2(m)$.
  
  Therefore, $c_1 = c_2$.

Since $\phi_n$ is a bijection from the set of Dirichlet characters to itself, we have:
$\sum_{c} \phi_n(c)(n) = \sum_{c} c(n)$

But $\phi_n(c)(n) = c'(n) \cdot c(n)$, so:
$c'(n) \cdot \sum_{c} c(n) = \sum_{c} c(n)$

This implies that either $\sum_{c} c(n) = 0$ or $c'(n) = 1$. Since $c'$ was arbitrary, if the sum is not zero, then every Dirichlet character must satisfy $c(n) = 1$ when $\gcd(n,d) = 1$.

### Mathematical insight
This theorem reveals a fundamental orthogonality property of Dirichlet characters. The result shows that when $n$ is coprime to $d$, either all Dirichlet characters take the value 1 at $n$ (which happens only in the trivial case where there's just one character), or their values at $n$ sum to 0. This orthogonality is key in number theory, particularly in the study of Dirichlet L-functions and distribution of primes in arithmetic progressions.

The proof uses a clever technique of creating a bijection on the set of characters that preserves the sum, forcing a strong constraint on the possible values of this sum. This is a standard technique in the theory of characters of finite groups.

This result is a weaker version of the full orthogonality relation for Dirichlet characters, which states more generally about sums of products of characters.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_EQ_0`: Defines when a Dirichlet character equals 0
  - `FINITE_DIRICHLET_CHARACTERS`: States that the set of Dirichlet characters modulo d is finite
  - `DIRICHLET_CHARACTER_MUL_CNJ`: Properties of conjugates of Dirichlet characters
  - `DIRICHLET_CHARACTER_GROUPMUL`: Closure of Dirichlet characters under multiplication

- **Definitions**:
  - `dirichlet_character`: Defines the properties of a Dirichlet character

### Porting notes
When implementing this in another system, pay attention to:
1. The representation of complex numbers and complex arithmetic
2. The handling of finite summations over complex-valued functions
3. The definition of Dirichlet characters, ensuring all three key properties are preserved

The proof relies on functional properties of Dirichlet characters and set-theoretic bijections, which might require different approaches in systems with different foundations.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS = prove
 (`!d n. real(vsum {c | dirichlet_character d c} (\c. c n)) /\
         &0 <= Re(vsum {c | dirichlet_character d c} (\c. c n))`,
  MP_TAC DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_VSUM;
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; RE_VSUM] THEN
    MATCH_MP_TAC SUM_POS_LE] THEN
  ASM_SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM; REAL_CX; RE_CX] THEN
  REWRITE_TAC[REAL_POS]);;
```

### Informal statement
For all integers $d$ and $n$, the sum of the values $c(n)$ over all Dirichlet characters $c$ modulo $d$ is a real number, and its real part is non-negative:

$$\forall d, n.\; \text{real}\left(\sum_{c \in \{\chi \mid \chi \text{ is a Dirichlet character mod } d\}} c(n)\right) \land 0 \leq \text{Re}\left(\sum_{c \in \{\chi \mid \chi \text{ is a Dirichlet character mod } d\}} c(n)\right)$$

### Informal proof
The proof relies on `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`, which states that for any $d$ and $n$:
- Either the sum $\sum_{c} c(n) = 0$
- Or $n$ is coprime to $d$ and $c(n) = 1$ for all Dirichlet characters $c$ modulo $d$

Based on this, we consider both cases:

- In the first case where the sum is 0, we have $\text{Re}(\sum_{c} c(n)) = \text{Re}(0) = 0$, which satisfies our requirement.
  
- In the second case where $n$ is coprime to $d$ and all $c(n) = 1$, the sum equals the number of Dirichlet characters modulo $d$, which is a real number (in fact, a positive integer). Therefore, the real part of this sum is itself, which is non-negative.

For the first part of our goal (proving the sum is real):
- We apply `REAL_VSUM`, which proves that a sum is real when all its summands are real.
- Since in the second case all $c(n) = 1$, which is real, the sum is real.

For the second part (proving the real part is non-negative):
- We use `RE_VSUM` to show that the real part of the sum equals the sum of the real parts.
- We use `SUM_POS_LE` to show that a sum of non-negative terms is non-negative.
- Each term is either 0 or 1, both of which have non-negative real parts.

### Mathematical insight
This theorem establishes an important property of the sum of Dirichlet character values: the sum is always real with a non-negative real part. This is somewhat surprising since individual Dirichlet characters can take complex values in general.

The result is particularly useful in analytic number theory when studying properties of Dirichlet characters or L-functions. When summing over all characters modulo $d$, we get a value that behaves nicely, either vanishing completely (when $n$ is not coprime to $d$) or equaling the number of Dirichlet characters (when $n$ is coprime to $d$). This orthogonality property is fundamental and often used in establishing various number-theoretic results.

### Dependencies
- Theorems:
  - `FINITE_DIRICHLET_CHARACTERS`: Proves that the set of Dirichlet characters modulo $d$ is finite.
  - `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`: States that the sum of Dirichlet character values at $n$ is either 0 or, when $n$ is coprime to $d$, all characters evaluate to 1 at $n$.
  
- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a completely multiplicative function that is $d$-periodic and equals 0 exactly when the input is not coprime to $d$.

### Porting notes
When porting this theorem:
- Ensure your system has a well-defined concept of Dirichlet characters with the same properties.
- The manipulation of real and complex numbers (with functions like `Re` for the real part) will need appropriate counterparts.
- The proof flow relies on case analysis from the dependent theorem and then applying properties of summation, which should be adaptable to most proof assistants.

---

## CHARACTER_EXTEND_FROM_SUBGROUP

### CHARACTER_EXTEND_FROM_SUBGROUP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CHARACTER_EXTEND_FROM_SUBGROUP = prove
 (`!f h a d.
        h SUBSET {x | x < d /\ coprime(x,d)} /\
        (1 IN h) /\
        (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
        (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
        (!x. x IN h ==> ~(f x = Cx(&0))) /\
        (!x y. x IN h /\ y IN h
                 ==> f((x * y) MOD d) = f(x) * f(y)) /\
        a IN {x | x < d /\ coprime(x,d)} DIFF h
        ==> ?f' h'. (a INSERT h) SUBSET h' /\
                    h' SUBSET {x | x < d /\ coprime(x,d)} /\
                    (!x. x IN h ==> f'(x) = f(x)) /\
                    ~(f' a = Cx(&1)) /\
                    1 IN h' /\
                    (!x y. x IN h' /\ y IN h' ==> ((x * y) MOD d) IN h') /\
                    (!x. x IN h' ==> ?y. y IN h' /\ (x * y == 1) (mod d)) /\
                    (!x. x IN h' ==> ~(f' x = Cx(&0))) /\
                    (!x y. x IN h' /\ y IN h'
                           ==> f'((x * y) MOD d) = f'(x) * f'(y))`,
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < d` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  SUBGOAL_THEN `?m x. 0 < m /\ x IN h /\ (a EXP m == x) (mod d)` MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`phi d`; `1`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]; ALL_TAC] THEN
    MATCH_MP_TAC FERMAT_LITTLE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x s. x IN h ==> ((x EXP s) MOD d) IN h` ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[EXP; MOD_LT] THEN
    SUBGOAL_THEN `((x * (x EXP s) MOD d) MOD d) IN h` MP_TAC THEN
    ASM_MESON_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `am:num` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `0 < m ==> m = 1 \/ 2 <= m`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC `(a EXP 1 == am) (mod d)` THEN
    ASM_SIMP_TAC[EXP_1; GSYM CONG_MOD_LT; MOD_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `r:num` o SPEC `r MOD m`) THEN
  ASM_SIMP_TAC[DIVISION; LE_1; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r x. x IN h /\ (a EXP r == x) (mod d) ==> m divides r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVIDES_MOD; LE_1] THEN
    REWRITE_TAC[ARITH_RULE `n = 0 <=> ~(0 < n)`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(a EXP (r MOD m)) MOD d` THEN
    ASM_SIMP_TAC[CONG_RMOD; LE_1; CONG_REFL] THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `(a EXP (m * r DIV m)) MOD d`) THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM EXP_EXP] THEN
      SUBGOAL_THEN
       `(a EXP m) EXP (r DIV m) MOD d = (am EXP (r DIV m)) MOD d`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_SIMP_TAC[GSYM CONG; LE_1] THEN
      ASM_SIMP_TAC[CONG_LMOD; CONG_EXP; LE_1];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(a EXP r == x) (mod d)` THEN
    MP_TAC(SPECL [`r:num`; `m:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_ADD] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num` o MATCH_MP
    (NUMBER_RULE `!a. (x:num == y) (mod n) ==> (a * x == a * y) (mod n)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(y * e * a == z) (mod n)
      ==> (e * y == 1) (mod n) ==> (a == z) (mod n)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `a EXP (m * r DIV m) MOD d * y` THEN
      ASM_SIMP_TAC[CONG_MULT; CONG_REFL; CONG_RMOD; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONG; LE_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(f:num->complex) am`; `m:num`]
               EXISTS_COMPLEX_ROOT_NONTRIVIAL) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?g. !x k. x IN h ==> g((x * a EXP k) MOD d) = f(x) * z pow k`
  MP_TAC THENL
   [REWRITE_TAC[MESON[] `(?g. !x a. p x ==> g(f a x) = h a x) <=>
                         (?g. !y x a. p x /\ f a x = y ==> g y = h a x)`] THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN
    REWRITE_TAC[MESON[]
     `(!y. ?z. !x k. p x /\ f x k = y ==> z = g x k) <=>
      (!x k x' k'. p x /\ p x' /\ f x k = f x' k' ==> g x k = g x' k')`] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(!x k y j. P x k y j) <=> (!k j x y. P x k y j)`] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN STRIP_TAC THEN
    UNDISCH_TAC `k:num <= j` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `m divides i` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(z * x) MOD d` THEN ASM_SIMP_TAC[CONG_RMOD; LE_1] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `y * a EXP k` THEN
      REWRITE_TAC[COPRIME_LMUL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + i)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD] THEN UNDISCH_TAC `(y * z == 1) (mod d)` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((y * (am EXP r) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[CONG_MOD_LT] THEN
      MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `y * (a EXP m) EXP r` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONG_MULT THEN
        ASM_SIMP_TAC[CONG_MULT; CONG_LMOD; CONG_REFL; LE_1] THEN
        MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC[CONG_SYM];
        ALL_TAC] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a EXP k` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + m * r)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD; EXP_EXP] THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    SPEC_TAC(`r:num`,`s:num`) THEN INDUCT_TAC THEN
    ASM_SIMP_TAC[EXP; MOD_LT; complex_pow; COMPLEX_MUL_RID] THENL
     [UNDISCH_TAC
       `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d):complex = f x * f y` THEN
      DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
      ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
      UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((am * (am EXP s) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[]] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:num->complex` THEN
  DISCH_THEN (LABEL_TAC "*") THEN
  EXISTS_TAC `{(x * a EXP k) MOD d | x IN h /\ k IN (:num)}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNIV] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC [`1`; `1`];
      MAP_EVERY EXISTS_TAC [`x:num`; `0`]] THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; EXP; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[DIVISION; LE_1; COPRIME_LMOD; COPRIME_LMUL] THEN
    ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:num`; `0`]) THEN
    ASM_SIMP_TAC[MOD_LT; EXP; MULT_CLAUSES; complex_pow; COMPLEX_MUL_RID];
    REMOVE_THEN "*" (MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; MOD_LT; COMPLEX_POW_1] THEN
    UNDISCH_TAC `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d) = f x * f y` THEN
    DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
    UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC [`1`; `0`] THEN
    ASM_SIMP_TAC[EXP; MULT_CLAUSES; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(x * y) MOD d`; `j + k:num`] THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
    REWRITE_TAC[EXP_ADD; MULT_AC];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(z * a EXP ((phi d - 1) * k)) MOD d` THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `(x * a EXP k) * (z * a EXP ((phi d - 1) * k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_MULT THEN ASM_SIMP_TAC[CONG_MOD; LE_1]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `(x * a) * (z * ak):num = (x * z) * (a * ak)`] THEN
    GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `1 = 1 * 1`] THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `k + (phi d - 1) * k = phi(d) * k` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k + a * k = (a + 1) * k`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[SUB_ADD; PHI_LOWERBOUND_1_STRONG];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN SUBST1_TAC(SYM(SPEC `k:num` EXP_ONE)) THEN
    MATCH_MP_TAC CONG_EXP THEN ASM_SIMP_TAC[FERMAT_LITTLE];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0] THEN
    UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
    DISCH_THEN(MP_TAC o SPEC `am:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `z pow m = f(am:num)`)) THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0] THEN ASM_SIMP_TAC[LE_1];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `g(((x * y) MOD d * a EXP (k + j)) MOD d):complex` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
      REWRITE_TAC[EXP_ADD; MULT_AC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_AC]]);;
```

### Informal statement
Let $f$ be a function from a subset $h$ of $\{x : x < d \text{ and } \gcd(x,d)=1\}$ to the complex numbers, where $h$ satisfies:
- $1 \in h$
- $h$ is closed under multiplication modulo $d$: if $x,y \in h$ then $(x \cdot y) \bmod d \in h$
- Every element in $h$ has a multiplicative inverse in $h$ modulo $d$
- $f$ never takes the value 0
- $f$ is a character: $f((x \cdot y) \bmod d) = f(x) \cdot f(y)$ for all $x,y \in h$

Then, if $a \in \{x : x < d \text{ and } \gcd(x,d)=1\}$ but $a \notin h$, there exists an extension $f'$ of $f$ to a larger subset $h'$ containing $h \cup \{a\}$ such that:
- $h'$ maintains all the properties of $h$ listed above
- $f'$ agrees with $f$ on $h$
- $f'(a) \neq 1$

### Informal proof
The proof, which is substantial, proceeds as follows:

First, note that $1 < d$ (since $h$ is a subset of $\{x : x < d \text{ and } \gcd(x,d)=1\}$ and $1 \in h$).

By Fermat's Little Theorem, for any $a$ coprime to $d$, we know that $a^{\phi(d)} \equiv 1 \pmod{d}$ where $\phi$ is Euler's totient function. This means there exists some power of $a$ that belongs to $h$ - specifically, $a^{\phi(d)} \equiv 1 \pmod{d}$.

Let $m$ be the smallest positive integer such that $a^m \equiv x \pmod{d}$ for some $x \in h$. By the well-ordering principle of natural numbers, such an $m$ exists.

If $m = 1$, then $a \equiv x \pmod{d}$ for some $x \in h$, which contradicts our assumption that $a \not\in h$ (since $a < d$ and elements of $h$ are less than $d$).

So $m \geq 2$. Let $a_m \in h$ be such that $a^m \equiv a_m \pmod{d}$.

The key idea is that for any $r$, if $a^r \equiv y \pmod{d}$ for some $y \in h$, then $m$ divides $r$. This follows from the minimality of $m$.

Now, since $m \geq 2$, there exists a complex number $z$ such that $z^m = f(a_m)$ and $z \neq 1$.

We can then define a function $g$ such that $g((x \cdot a^k) \bmod d) = f(x) \cdot z^k$ for all $x \in h$ and $k \in \mathbb{N}$. This definition makes sense because:
1. If $x \cdot a^k \equiv x' \cdot a^{k'} \pmod{d}$ with $x, x' \in h$, then $f(x) \cdot z^k = f(x') \cdot z^{k'}$
2. This equality holds because $m$ must divide $k'-k$ by our earlier argument

Finally, we define $h' = \{(x \cdot a^k) \bmod d : x \in h, k \in \mathbb{N}\}$ and $f' = g$. We verify that:
- $h \cup \{a\} \subset h'$ (taking $k=0$ gives $h \subset h'$, and $a = (1 \cdot a^1) \bmod d \in h'$)
- $h' \subset \{x : x < d \text{ and } \gcd(x,d)=1\}$ (since $\gcd$ is preserved under multiplication)
- $f'$ agrees with $f$ on $h$ (from our definition of $g$ with $k=0$)
- $f'(a) = z \neq 1$
- $1 \in h'$ (since $1 \in h$)
- $h'$ is closed under multiplication modulo $d$
- Every element in $h'$ has a multiplicative inverse in $h'$ modulo $d$ (using Fermat's Little Theorem)
- $f'$ never takes the value 0 (since neither does $f$ and $z \neq 0$)
- $f'$ is a character (by construction)

### Mathematical insight
This theorem is critical for the construction of Dirichlet characters. It shows that a character defined on a subgroup of $(\mathbb{Z}/d\mathbb{Z})^*$ can be extended to a larger subgroup while preserving its key properties.

The result is particularly important because:
1. It provides a way to build characters step-by-step by extending from simpler subgroups
2. It guarantees we can construct characters with specific values at chosen points
3. It demonstrates that Dirichlet characters, which are vital for analytic number theory and Dirichlet's theorem on primes in arithmetic progressions, exist in abundance

The construction technique used here is a standard approach in character theory - defining values on generators and extending multiplicatively.

### Dependencies
- Number theory theorems:
  - `CONG_MULT`: Congruence is preserved under multiplication
  - `CONG_EXP`: Congruence is preserved under exponentiation
  - `CONG_MOD`: `a MOD n` is congruent to `a` modulo `n`
  - `CONG_MOD_LT`: Characterization of modular congruence for values less than the modulus
  - `FERMAT_LITTLE`: Fermat's Little Theorem
  - `PHI_LOWERBOUND_1_STRONG`: Lower bound properties of Euler's totient function
- Complex analysis theorems:
  - `EXISTS_COMPLEX_ROOT_NONTRIVIAL`: Existence of complex roots other than 1

### Porting notes
When porting this theorem:
1. The congruence relation `==` in HOL Light corresponds to modular equivalence (≡) in mathematical notation
2. The handling of subgroups and characters requires careful attention to the algebraic structure
3. The proof makes heavy use of number-theoretic properties of modular arithmetic
4. The complex root existence theorem (`EXISTS_COMPLEX_ROOT_NONTRIVIAL`) is needed for the construction

---

## DIRICHLET_CHARACTER_DISCRIMINATOR

### DIRICHLET_CHARACTER_DISCRIMINATOR
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DISCRIMINATOR = prove
 (`!d n. 1 < d /\ ~((n == 1) (mod d))
          ==> ?c. dirichlet_character d c /\ ~(c n = Cx(&1))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    EXISTS_TAC `chi_0 d` THEN
    ASM_REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0; chi_0] THEN
    CONV_TAC COMPLEX_RING] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `{1}`; `n MOD d`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
  ASM_SIMP_TAC[IN_SING; IN_ELIM_THM; IN_DIFF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET; MULT_CLAUSES; MOD_LT; LE_1; IN_SING;
                 IN_ELIM_THM; DIVISION; COPRIME_LMOD; CONG_MOD_LT;
                 COMPLEX_MUL_LID; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    ASM_MESON_TAC[COPRIME_1; COPRIME_SYM; CONG_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f0:num->complex`; `h0:num->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= CARD {x | x < d /\ coprime(x,d)}
        ==> ?f h. h SUBSET {x | x < d /\ coprime(x,d)} /\
                 (1 IN h) /\ (n MOD d) IN h /\
                 (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
                 (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
                 ~(f(n MOD d) = Cx(&1)) /\
                 (!x. x IN h ==> ~(f x = Cx(&0))) /\
                 (!x y. x IN h /\ y IN h
                          ==> f((x * y) MOD d) = f(x) * f(y)) /\
                 m <= CARD h`
  MP_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(LABEL_TAC "*") THEN DISCH_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [MAP_EVERY EXISTS_TAC [`f0:num->complex`; `h0:num->bool`] THEN
      ASM_REWRITE_TAC[LE_0] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
     (MATCH_MP (ARITH_RULE `~(m = 0) ==> m - 1 < m`) (ASSUME `~(m = 0)`))) THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= n ==> x - 1 <= n`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m <= CARD(h:num->bool)` THENL
     [MAP_EVERY EXISTS_TAC [`f:num->complex`; `h:num->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `h SUBSET {x | x < d /\ coprime (x,d)}`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = t) ==> ?a. a IN t /\ ~(a IN s)`)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:num->complex`; `h:num->bool`; `a:num`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ff:num->complex` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `hh:num->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((a:num) INSERT h)` THEN
    SUBGOAL_THEN `FINITE(h:num->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES] THEN
      UNDISCH_TAC `m - 1 <= CARD(h:num->bool)` THEN ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `CARD {x | x < d /\ coprime(x,d)}`) THEN
  REWRITE_TAC[LE_REFL] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN
  ASM_CASES_TAC `h = {x | x < d /\ coprime (x,d)}` THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
    REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_REWRITE_TAC[PSUBSET] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < d}` THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN SET_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\n. if coprime(n,d) then f(n MOD d) else Cx(&0)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THENL
   [REWRITE_TAC[NUMBER_RULE `coprime(x + d:num,d) <=> coprime(x,d)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COPRIME_LMOD; DIVISION; LE_1];
    X_GEN_TAC `y:num` THEN REWRITE_TAC[COPRIME_LMUL] THEN
    MAP_EVERY ASM_CASES_TAC [`coprime(x,d)`; `coprime(y,d)`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f(((x MOD d) * (y MOD d)) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_MOD2; LE_1];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[DIVISION; COPRIME_LMOD; LE_1]]]);;
```

### Informal statement
For any modulus $d > 1$ and integer $n$ that is not congruent to $1$ modulo $d$, there exists a Dirichlet character $c$ modulo $d$ such that $c(n) \neq 1$.

More precisely, for all $d, n$ where $d > 1$ and $n \not\equiv 1 \pmod{d}$, there exists a function $c: \mathbb{N} \to \mathbb{C}$ such that:
1. $c$ is a Dirichlet character modulo $d$ (i.e., $c(n+d) = c(n)$, $c(n) = 0$ if and only if $\gcd(n,d) > 1$, and $c(mn) = c(m)c(n)$ for all $m,n$)
2. $c(n) \neq 1$

### Informal proof
We proceed by considering two cases:

* **Case 1:** If $\gcd(n,d) > 1$ (i.e., $n$ is not coprime to $d$)
  - We can use the principal character $\chi_0$ which is defined as:
    $$\chi_0(n) = \begin{cases} 1 & \text{if}\ \gcd(n,d) = 1 \\ 0 & \text{if}\ \gcd(n,d) > 1 \end{cases}$$
  - Since $\gcd(n,d) > 1$ in this case, we have $\chi_0(n) = 0 \neq 1$
  - $\chi_0$ is a Dirichlet character by `DIRICHLET_CHARACTER_CHI_0`

* **Case 2:** If $\gcd(n,d) = 1$ (i.e., $n$ is coprime to $d$)
  - We start with the trivial character that maps everything to 1 and the singleton set $\{1\}$
  - We use `CHARACTER_EXTEND_FROM_SUBGROUP` to extend this character to include $n \bmod d$, obtaining a character $f_0$ and a set $h_0$ such that $f_0(n \bmod d) \neq 1$
  
  - We then prove by induction on $m$ that for any $m \leq |\{x : x < d \land \gcd(x,d) = 1\}|$, there exist $f$ and $h$ such that:
    - $h \subseteq \{x : x < d \land \gcd(x,d) = 1\}$
    - $1 \in h$ and $(n \bmod d) \in h$
    - $h$ is closed under multiplication modulo $d$
    - For every $x \in h$, there exists $y \in h$ with $xy \equiv 1 \pmod{d}$
    - $f(n \bmod d) \neq 1$
    - $f(x) \neq 0$ for all $x \in h$
    - $f$ is multiplicative on $h$: $f((xy) \bmod d) = f(x)f(y)$ for $x,y \in h$
    - $m \leq |h|$
    
  - Setting $m = |\{x : x < d \land \gcd(x,d) = 1\}|$, we obtain $h = \{x : x < d \land \gcd(x,d) = 1\}$
  
  - We define our Dirichlet character $c$ as:
    $$c(n) = \begin{cases} f(n \bmod d) & \text{if}\ \gcd(n,d) = 1 \\ 0 & \text{if}\ \gcd(n,d) > 1 \end{cases}$$
    
  - We verify that $c$ satisfies the properties of a Dirichlet character:
    - $c(n+d) = c(n)$ because $(n+d) \equiv n \pmod{d}$ and $\gcd(n+d,d) = \gcd(n,d)$
    - $c(n) = 0$ if and only if $\gcd(n,d) > 1$ by construction
    - $c(mn) = c(m)c(n)$ by cases:
      * If either $\gcd(m,d) > 1$ or $\gcd(n,d) > 1$, then $\gcd(mn,d) > 1$, so $c(mn) = 0 = c(m)c(n)$
      * If both $\gcd(m,d) = \gcd(n,d) = 1$, then $c(mn) = f(mn \bmod d) = f((m \bmod d \cdot n \bmod d) \bmod d) = f(m \bmod d)f(n \bmod d) = c(m)c(n)$
  
  - Since $f(n \bmod d) \neq 1$, we have $c(n) \neq 1$

### Mathematical insight
This theorem establishes the existence of discriminating Dirichlet characters, which is a fundamental result in the theory of Dirichlet characters and has important applications in number theory.

The key insight is that for any non-principal residue class modulo $d$, there exists a Dirichlet character that can distinguish it from the principal residue class. This property is essential for the orthogonality relations of Dirichlet characters and ultimately for proving Dirichlet's theorem on primes in arithmetic progressions.

The proof uses a constructive approach by extending characters from subgroups, showing how to systematically build a character with the desired properties. This construction demonstrates the rich structure of the group of Dirichlet characters modulo $d$.

### Dependencies
- Theorems:
  - `CONG_MOD_LT`: Relates modular congruence to remainder
  - `DIRICHLET_CHARACTER_CHI_0`: Shows that $\chi_0$ is a Dirichlet character
  - `CHARACTER_EXTEND_FROM_SUBGROUP`: Allows extending a character from a subgroup

- Definitions:
  - `dirichlet_character`: Defines the properties of a Dirichlet character
  - `chi_0`: Defines the principal character

### Porting notes
When porting this theorem:
1. Ensure that the definition of Dirichlet characters in the target system matches HOL Light's definition
2. The character extension theorem (`CHARACTER_EXTEND_FROM_SUBGROUP`) is key and may require significant work to port
3. The proof relies on finite set properties and cardinality arguments, which may need different approaches in systems with different set libraries
4. Complex numbers are used as the codomain of characters, but other systems might use different representations

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT = prove
 (`!d n. vsum {c | dirichlet_character d c} (\c. c n) =
                if (n == 1) (mod d)
                then Cx(&(CARD {c | dirichlet_character d c}))
                else Cx(&0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; DIRICHLET_CHARACTER_0; SET_RULE
     `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[chi_0; COPRIME_0; VECTOR_ADD_RID] THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[CONG_MOD_1; DIRICHLET_CHARACTER_1] THEN
    REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_ADD_RID; ARITH];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum {c | dirichlet_character d c} (\c. Cx(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_CONG];
      SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; VSUM_CONST] THEN
      REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]];
    MP_TAC(SPECL [`d:num`; `n:num`]
      DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_DISCRIMINATOR;
                  ARITH_RULE `~(d = 0) /\ ~(d = 1) ==> 1 < d`]]);;
```

### Informal statement
For any modulus $d$ and integer $n$, the sum over all Dirichlet characters modulo $d$ evaluated at $n$ is given by:

$$\sum_{c \in \{c \mid \text{dirichlet\_character}(d,c)\}} c(n) = \begin{cases}
|\{c \mid \text{dirichlet\_character}(d,c)\}| & \text{if } n \equiv 1 \pmod{d} \\
0 & \text{otherwise}
\end{cases}$$

where $|\{c \mid \text{dirichlet\_character}(d,c)\}|$ denotes the number of Dirichlet characters modulo $d$.

### Informal proof
We proceed by case analysis on the modulus $d$:

* **Case $d = 0$**: When $d = 0$, the congruence relation $n \equiv 1 \pmod{0}$ simplifies to $n = 1$. From the theorem `DIRICHLET_CHARACTER_0`, we know that there is only one Dirichlet character modulo 0, namely $\chi_0(0)$. This character is defined as:
  $$\chi_0(0)(n) = \begin{cases}
  1 & \text{if } \text{coprime}(n,0) \\
  0 & \text{otherwise}
  \end{cases}$$
  Since $\text{coprime}(n,0)$ is only true when $n = 1$, the sum equals 1 when $n = 1$ and 0 otherwise, which matches our desired result.

* **Case $d = 1$**: When $d = 1$, all integers are congruent modulo 1, so $n \equiv 1 \pmod{1}$ always holds. From `DIRICHLET_CHARACTER_1`, we know that any Dirichlet character $c$ modulo 1 satisfies $c(n) = 1$ for all $n$. There is only one such character, so the sum equals 1, matching our desired result.

* **Case $d > 1$**: We consider two subcases:
  
  - **Subcase $n \equiv 1 \pmod{d}$**: By `DIRICHLET_CHARACTER_CONG` and `DIRICHLET_CHARACTER_EQ_1`, all Dirichlet characters $c$ modulo $d$ satisfy $c(n) = c(1) = 1$. Therefore, the sum equals the number of Dirichlet characters modulo $d$.
  
  - **Subcase $n \not\equiv 1 \pmod{d}$**: We use `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` which tells us that the sum either equals 0 or all characters evaluate to 1 at $n$. However, by `DIRICHLET_CHARACTER_DISCRIMINATOR`, since $d > 1$ and $n \not\equiv 1 \pmod{d}$, there exists a character $c$ such that $c(n) \neq 1$. This eliminates the second possibility, so the sum must equal 0.

### Mathematical insight
This theorem provides the second orthogonality relation for Dirichlet characters, complementing the first orthogonality relation (which sums over values of characters at different inputs). This result is fundamental in analytic number theory, particularly in the study of Dirichlet L-functions and their applications.

The result shows that Dirichlet characters form an orthogonal basis for the space of arithmetic functions that are periodic modulo $d$. Specifically, the characters detect whether an integer is congruent to 1 modulo $d$ when summed together.

The value of the sum when $n \equiv 1 \pmod{d}$ is precisely the total number of Dirichlet characters modulo $d$, which for $d > 1$ equals $\phi(d)$, the Euler's totient function of $d$.

### Dependencies
- `DIRICHLET_CHARACTER_EQ_1`: A Dirichlet character always takes the value 1 at input 1.
- `DIRICHLET_CHARACTER_CONG`: Dirichlet characters respect congruence modulo d.
- `DIRICHLET_CHARACTER_0`: Characterizes Dirichlet characters modulo 0.
- `DIRICHLET_CHARACTER_1`: Characterizes Dirichlet characters modulo 1.
- `FINITE_DIRICHLET_CHARACTERS`: The set of Dirichlet characters modulo d is finite.
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`: Weak form of the orthogonality relation.
- `DIRICHLET_CHARACTER_DISCRIMINATOR`: For d > 1 and n ≢ 1 (mod d), there exists a character not evaluating to 1 at n.
- `chi_0`: Principal Dirichlet character.

### Porting notes
When porting this theorem, ensure that:
1. The definition of Dirichlet characters matches exactly, particularly the periodicity and multiplicative properties.
2. The handling of special cases for d=0 and d=1 is preserved.
3. Finite sums over character spaces are properly supported in the target system.
4. The congruence relation and coprime relation are properly defined.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS

### DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS = prove
 (`!d n. 1 <= d
         ==> vsum {c | dirichlet_character d c} (\c. c(n)) =
                if (n == 1) (mod d) then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\c n. (c:num->complex) n`; `{c | dirichlet_character d c}`;
                 `1..d`;] VSUM_SWAP) THEN
  SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT;
           DIRICHLET_CHARACTER_SUM_OVER_NUMBERS; FINITE_NUMSEG;
           FINITE_DIRICHLET_CHARACTERS; ETA_AX] THEN
  REWRITE_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `{j | j IN 1..d /\ (j == 1) (mod d)} = {1}`
   (fun th -> SIMP_TAC[th; VSUM_SING]) THEN
  REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LE_REFL; CONG_REFL] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_SIMP_TAC[CONG_MOD_1; LE_ANTISYM] THEN
  ASM_CASES_TAC `k:num = d` THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(d == 1) (mod d) <=> d divides 1`] THEN
    ASM_REWRITE_TAC[DIVIDES_ONE];
    STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[LT_LE]]);;
```

### Informal statement
For any natural numbers $d$ and $n$ with $d \geq 1$, the sum of the values of all Dirichlet characters modulo $d$ at $n$ is given by:

$$\sum_{c \in \{c \,|\, \text{dirichlet\_character } d \, c\}} c(n) = 
\begin{cases}
\phi(d) & \text{if } n \equiv 1 \pmod{d} \\
0 & \text{otherwise}
\end{cases}$$

Where $\phi(d)$ is Euler's totient function, and $\text{dirichlet\_character } d \, c$ means $c$ is a Dirichlet character modulo $d$.

### Informal proof
The proof proceeds as follows:

1. First, we apply `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT` which gives us:
   $$\sum_{c \in \{c \,|\, \text{dirichlet\_character } d \, c\}} c(n) = 
   \begin{cases}
   |C_d| & \text{if } n \equiv 1 \pmod{d} \\
   0 & \text{otherwise}
   \end{cases}$$
   where $C_d = \{c \,|\, \text{dirichlet\_character } d \, c\}$ and $|C_d|$ is the cardinality of this set.

2. We now need to show that $|C_d| = \phi(d)$. We use a clever swap of summations:
   - Apply `VSUM_SWAP` to switch the order of summation between characters and numbers
   - This gives us: $\sum_{c \in C_d} \sum_{j=1}^d c(j) = \sum_{j=1}^d \sum_{c \in C_d} c(j)$

3. For the right side, we use `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT` to get:
   $$\sum_{c \in C_d} c(j) = \begin{cases}
   |C_d| & \text{if } j \equiv 1 \pmod{d} \\
   0 & \text{otherwise}
   \end{cases}$$

4. For the left side, we use `DIRICHLET_CHARACTER_SUM_OVER_NUMBERS` which shows:
   $$\sum_{j=1}^d c(j) = \begin{cases}
   \phi(d) & \text{if } c = \chi_0 \\
   0 & \text{otherwise}
   \end{cases}$$
   where $\chi_0$ is the principal character modulo $d$.

5. We prove that the only $j \in \{1,\ldots,d\}$ such that $j \equiv 1 \pmod{d}$ is $j = 1$ itself:
   - If $d = 1$, this is trivial since all numbers are congruent to 1 mod 1
   - If $d > 1$ and $1 \leq j \leq d$ with $j \equiv 1 \pmod{d}$, then $j = 1$ because:
     - If $j = d$, then we'd have $d \equiv 1 \pmod{d}$, which implies $d$ divides 1, impossible for $d > 1$
     - If $j < d$ and $j \equiv 1 \pmod{d}$, by `CONG_IMP_EQ`, we have $j = 1$

6. Combining these results, we get:
   $$|C_d| = \phi(d)$$

7. Therefore, the sum over all Dirichlet characters at $n$ is:
   $$\sum_{c \in C_d} c(n) = \begin{cases}
   \phi(d) & \text{if } n \equiv 1 \pmod{d} \\
   0 & \text{otherwise}
   \end{cases}$$

### Mathematical insight
This theorem provides a powerful orthogonality relation for Dirichlet characters. It states that when summing the values of all Dirichlet characters at a specific point $n$, we get a non-zero value (specifically $\phi(d)$) only when $n \equiv 1 \pmod{d}$.

This is analogous to the orthogonality relations for characters of finite groups, which are fundamental in representation theory. The result highlights a key property of Dirichlet characters: they form an orthogonal system under the inner product defined by summation over the character group.

This orthogonality property is crucial for the theory of Dirichlet L-functions and their applications in number theory, particularly for proving results about the distribution of primes in arithmetic progressions.

### Dependencies
- **Theorems:**
  - `CONG_IMP_EQ`: If $x < n$, $y < n$, and $x \equiv y \pmod{n}$, then $x = y$.
  - `DIRICHLET_CHARACTER_CHI_0`: The function $\chi_0$ is a Dirichlet character modulo $d$.
  - `FINITE_DIRICHLET_CHARACTERS`: The set of Dirichlet characters modulo $d$ is finite.
  - `DIRICHLET_CHARACTER_SUM_OVER_NUMBERS`: For a Dirichlet character $c$ modulo $d$, the sum $\sum_{n=1}^d c(n) = \phi(d)$ if $c$ is the principal character, and 0 otherwise.
  - `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT`: The sum $\sum_{c} c(n)$ over all Dirichlet characters modulo $d$ equals $|C_d|$ if $n \equiv 1 \pmod{d}$ and 0 otherwise.

- **Definitions:**
  - `dirichlet_character`: A function $c: \mathbb{N} \to \mathbb{C}$ is a Dirichlet character modulo $d$ if:
    - It is periodic with period $d$: $c(n+d) = c(n)$ for all $n$
    - $c(n) = 0$ if and only if $\gcd(n,d) > 1$
    - It is completely multiplicative: $c(mn) = c(m)c(n)$ for all $m,n$

### Porting notes
When porting this theorem:
1. Pay attention to how Dirichlet characters are defined in the target system, as there are several equivalent definitions.
2. The proof relies heavily on the orthogonality relations between characters, which should be approached similarly in other systems.
3. The handling of the special case $d=1$ might need separate treatment in systems with different natural number representations.
4. Ensure that the target system has appropriate libraries for modular arithmetic, especially congruence relations.

---

## Lfunction_DEF

### Lfunction_DEF

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let Lfunction_DEF = new_definition
 `Lfunction c = infsum (from 1) (\n. c(n) / Cx(&n))`;;
```

### Informal statement
The L-function for a complex sequence $c$ is defined as the infinite sum:

$$L(c) = \sum_{n=1}^{\infty} \frac{c(n)}{n}$$

where $c(n)$ is a complex sequence and $n$ is a natural number starting from 1.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
L-functions are fundamental objects in analytic number theory. This definition specifically defines an L-function at the point $s = 1$, which is a specialization of the more general Dirichlet L-function:

$$L(c, s) = \sum_{n=1}^{\infty} \frac{c(n)}{n^s}$$

In this implementation, the definition uses `Cx(&n)` to convert the natural number $n$ to a complex number, as division in this context is between complex numbers.

L-functions at $s = 1$ are particularly important in number theory, as they often relate to significant arithmetic properties. For example, when $c$ is a Dirichlet character, the value of $L(c, 1)$ can provide information about class numbers of number fields.

### Dependencies
No explicit dependencies were provided in the input.

### Porting notes
When porting this definition:
1. Ensure your target system has a suitable definition of infinite sums (`infsum`).
2. Make sure the type conversion from natural numbers to complex numbers is handled appropriately (represented by `Cx(&n)` in HOL Light).
3. Verify that your system has appropriate convergence conditions for infinite sums, as L-functions only converge for certain sequences $c$.

---

## BOUNDED_LFUNCTION_PARTIAL_SUMS

### BOUNDED_LFUNCTION_PARTIAL_SUMS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_PARTIAL_SUMS = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded {vsum (1..n) c | n IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_SUM_MOD th]) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (\n. vsum(1..n) c:complex) (0..d)` THEN
  SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE; FINITE_NUMSEG] THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV; IN_IMAGE] THEN
  EXISTS_TAC `n MOD d` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LT_IMP_LE; DIVISION;
                DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL]);;
```

### Informal statement
For any modulus $d$ and Dirichlet character $c$ that is not the principal character $\chi_0(d)$, the set of partial sums $\{\sum_{i=1}^n c(i) \mid n \in \mathbb{N}\}$ is bounded.

### Informal proof
To prove that the set of partial sums is bounded, we proceed as follows:

- First, by applying the theorem `DIRICHLET_CHARACTER_SUM_MOD`, we can rewrite any partial sum $\sum_{i=1}^n c(i)$ as $\sum_{i=1}^{n \bmod d} c(i)$.
  
- This means that every partial sum in our set is actually equal to one of the sums $\sum_{i=1}^k c(i)$ where $k \in \{0,1,2,\ldots,d\}$.

- Therefore, our set of partial sums is a subset of $\{\sum_{i=1}^k c(i) \mid k \in \{0,1,2,\ldots,d\}\}$.

- Since $\{0,1,2,\ldots,d\}$ is a finite set, its image under the function $k \mapsto \sum_{i=1}^k c(i)$ is also finite.

- Every finite set of complex numbers is bounded, so our set of partial sums is bounded.

- Note that for the application of `DIRICHLET_CHARACTER_SUM_MOD` to be valid, we need $d \neq 0$ and $d \neq 1$, which follows from `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` since we assumed that $c$ is not the principal character.

### Mathematical insight
This theorem establishes an important property of L-functions associated with non-principal Dirichlet characters: the boundedness of their partial sums. This boundedness is a key component in the analytic theory of L-functions and is used in establishing their convergence properties.

The proof leverages the periodicity of Dirichlet characters to show that there are only finitely many distinct partial sums (at most $d+1$ of them), which immediately implies boundedness. This is a clever application of modular arithmetic to obtain a strong analytical result.

In the broader context, this result is part of the foundation for the analytic theory of Dirichlet L-functions, which have significant applications in number theory, particularly in the study of the distribution of prime numbers in arithmetic progressions.

### Dependencies
- **Theorems**:
  - `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`: If $c$ is a Dirichlet character modulo $d$ and $c \neq \chi_0(d)$, then $d \neq 0$ and $d \neq 1$.
  - `DIRICHLET_CHARACTER_SUM_MOD`: For a non-principal Dirichlet character $c$ modulo $d$, the sum $\sum_{i=1}^n c(i) = \sum_{i=1}^{n \bmod d} c(i)$ for any $n$.
- **Definitions**:
  - `dirichlet_character`: A function $c: \mathbb{N} \rightarrow \mathbb{C}$ is a Dirichlet character modulo $d$ if it satisfies: (1) it is periodic with period $d$, (2) it is zero exactly when its input is not coprime to $d$, and (3) it is completely multiplicative.
  - `chi_0`: The principal Dirichlet character defined by $\chi_0(d)(n) = 1$ if $\gcd(n,d) = 1$, and $0$ otherwise.

### Porting notes
When porting this theorem:
- Ensure that your definition of Dirichlet character includes all three required properties (periodicity, zero values precisely when not coprime to modulus, and multiplicativity).
- The proof relies on modular arithmetic and the finiteness of sets, which should translate well to most proof assistants.
- The most system-specific part may be how sets and boundedness are formalized - adjust accordingly for your target system.

---

## LFUNCTION

### LFUNCTION
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LFUNCTION = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ((\n. c(n) / Cx(&n)) sums (Lfunction c)) (from 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SIMP_TAC[Lfunction_DEF; SUMS_INFSUM] THEN
  REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  REPEAT(EXISTS_TAC `1`) THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD]);;
```

### Informal statement
For any positive integer $d$ and function $c$, if $c$ is a Dirichlet character modulo $d$ and $c$ is not the principal character $\chi_0(d)$, then the series $\sum_{n=1}^{\infty} \frac{c(n)}{n}$ converges to the Dirichlet L-function $L(c)$.

More formally, if $c$ is a Dirichlet character modulo $d$ and $c \neq \chi_0(d)$, then the sequence $(\sum_{n=1}^{N} \frac{c(n)}{n})_{N=1}^{\infty}$ sums to $L(c)$.

### Informal proof
We need to prove that the sequence of partial sums $(\sum_{n=1}^{N} \frac{c(n)}{n})_{N=1}^{\infty}$ converges to $L(c)$.

By the definition of $L(c)$, we have $L(c) = \sum_{n=1}^{\infty} \frac{c(n)}{n}$, so we need to show this infinite sum converges.

The proof proceeds as follows:

* First, rewrite the complex division as multiplication: $\frac{c(n)}{n} = c(n) \cdot \frac{1}{n}$

* Apply Dirichlet's test for complex series convergence (theorem `SERIES_DIRICHLET_COMPLEX`). This requires showing:
  1. The partial sums of $c(n)$ are bounded
  2. The sequence $\frac{1}{n}$ is monotonically decreasing and converges to 0

* For the first condition, we use the theorem `BOUNDED_LFUNCTION_PARTIAL_SUMS`, which states that if $c$ is a non-principal Dirichlet character modulo $d$, then the set of partial sums $\{\sum_{n=1}^{N} c(n) | N \in \mathbb{N}\}$ is bounded.

* For the second condition, we use `LIM_INV_N`, which confirms that $\frac{1}{n} \to 0$ as $n \to \infty$. The sequence $\frac{1}{n}$ is also obviously decreasing for $n \geq 1$.

Therefore, the conditions for Dirichlet's test are satisfied, and the series $\sum_{n=1}^{\infty} \frac{c(n)}{n}$ converges to $L(c)$.

### Mathematical insight
This theorem establishes the convergence of Dirichlet L-functions for non-principal characters. The convergence of L-functions is fundamental in analytic number theory.

The key insight is that while the terms $\frac{c(n)}{n}$ don't necessarily decrease monotonically in absolute value (due to the character values), we can exploit the special properties of Dirichlet characters. Specifically, the partial sums of a non-principal character are bounded (they don't grow arbitrarily large), which allows us to apply Dirichlet's test for convergence.

The exclusion of the principal character $\chi_0$ is important because for this character, the L-function would reduce to the harmonic series with some terms removed, which diverges logarithmically.

### Dependencies
- **Theorems**:
  - `LIM_INV_N`: The limit of the sequence $\frac{1}{n}$ is 0
  - `BOUNDED_LFUNCTION_PARTIAL_SUMS`: The partial sums of a non-principal Dirichlet character are bounded
  - `SERIES_DIRICHLET_COMPLEX` (used but not listed in dependencies): Dirichlet's test for complex series convergence

- **Definitions**:
  - `dirichlet_character`: A function $c: \mathbb{N} \to \mathbb{C}$ satisfying: 
    - $c(n+d) = c(n)$ for all $n$ (periodicity)
    - $c(n) = 0$ if and only if $\gcd(n,d) > 1$ (zeros exactly at non-coprime inputs)
    - $c(mn) = c(m)c(n)$ for all $m,n$ (multiplicativity)
  - `chi_0`: The principal character, defined as $\chi_0(d)(n) = 1$ if $\gcd(n,d) = 1$ and 0 otherwise
  - `Lfunction_DEF`: Defines the Dirichlet L-function as $L(c) = \sum_{n=1}^{\infty} \frac{c(n)}{n}$

### Porting notes
When porting this theorem, ensure that the foundational results about Dirichlet characters and complex analysis are available. Specifically:

1. The complex Dirichlet test for convergence will be needed
2. The boundedness of partial sums for non-principal characters is a key lemma
3. The definition of Dirichlet L-functions may differ slightly in other systems - be careful about the starting index of summation (here it's 1)
4. Handling of complex numbers might differ between proof assistants

---

## CNJ_CHI_0

### Name of formal statement
CNJ_CHI_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CNJ_CHI_0 = prove
 (`!d n. cnj(chi_0 d n) = chi_0 d n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chi_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CNJ_CX]);;
```

### Informal statement
For all integers $d$ and $n$, the complex conjugate of $\chi_0(d, n)$ is equal to $\chi_0(d, n)$, i.e.,
$$\overline{\chi_0(d, n)} = \chi_0(d, n)$$

where $\chi_0$ is the principal Dirichlet character defined as:
$$\chi_0(d, n) = \begin{cases}
1 & \text{if}\ \gcd(n,d) = 1 \\
0 & \text{otherwise}
\end{cases}$$
expressed as a complex number.

### Informal proof
We prove that the complex conjugate of $\chi_0(d, n)$ equals $\chi_0(d, n)$ for all integers $d$ and $n$.

- First, we expand the definition of $\chi_0(d, n)$. By definition, $\chi_0(d, n)$ equals $1$ if $n$ and $d$ are coprime, and $0$ otherwise.
- In both cases, $\chi_0(d, n)$ is a real number represented as a complex number:
  - If $\gcd(n,d) = 1$, then $\chi_0(d, n) = 1$.
  - Otherwise, $\chi_0(d, n) = 0$.
- Since the complex conjugate of a real number is itself, we have $\overline{\chi_0(d, n)} = \chi_0(d, n)$ in both cases.

The theorem follows directly from the fact that the principal Dirichlet character $\chi_0$ always returns real values (either 0 or 1).

### Mathematical insight
This theorem establishes that the principal Dirichlet character $\chi_0$ is real-valued. This is important because while characters are generally complex-valued functions, the principal character is actually real-valued, which simplifies various computations and formulas involving it. 

The principal character $\chi_0$ is special among Dirichlet characters because it simply detects whether an integer is coprime to the modulus. It plays a foundational role in the theory of Dirichlet characters and L-functions, often serving as a baseline case.

This property (being equal to its complex conjugate) is a specific instance of the general fact that real numbers are invariant under complex conjugation.

### Dependencies
- Definitions:
  - `chi_0`: The principal Dirichlet character defined as 1 for integers coprime to the modulus and 0 otherwise
- Theorems:
  - `CNJ_CX`: The complex conjugate of a real number represented as a complex number equals itself

### Porting notes
This should be straightforward to port to other systems. The proof relies only on basic properties of complex conjugation and the definition of the principal character. When porting, ensure your system has:

1. A notion of coprime integers
2. A way to represent complex numbers or a notion of complex conjugation
3. The fact that complex conjugation of a real number gives the same real number

---

## LFUNCTION_CNJ

### Name of formal statement
LFUNCTION_CNJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_CNJ = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> Lfunction (\n. cnj(c n)) = cnj(Lfunction c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[Lfunction_DEF] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  ONCE_REWRITE_TAC[GSYM CNJ_CX] THEN
  REWRITE_TAC[GSYM CNJ_DIV] THEN
  REWRITE_TAC[SUMS_CNJ; CNJ_CX; GSYM Lfunction_DEF] THEN
  ASM_MESON_TAC[LFUNCTION]);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0$ modulo $d$, the L-function of the complex conjugate of $c$ is equal to the complex conjugate of the L-function of $c$:

$$\forall d, c. \text{dirichlet\_character}(d, c) \land c \neq \chi_0(d) \Rightarrow L(\overline{c}) = \overline{L(c)}$$

where $\overline{c}$ denotes the character defined by $\overline{c}(n) = \overline{c(n)}$ (complex conjugate of $c(n)$).

### Informal proof
We will show that $L(\overline{c}) = \overline{L(c)}$ by using the definition of the L-function and properties of complex conjugation:

- By definition, $L(c) = \sum_{n=1}^{\infty} \frac{c(n)}{n}$.
- Similarly, $L(\overline{c}) = \sum_{n=1}^{\infty} \frac{\overline{c(n)}}{n}$.

We proceed as follows:

1. Apply the definition of the L-function: $L(\overline{c}) = \text{infsum}(\text{from }1)(\lambda n. \frac{\overline{c(n)}}{n})$

2. Express $\frac{\overline{c(n)}}{n}$ as $\overline{\frac{c(n)}{n}}$ using the property that $\overline{\frac{z}{w}} = \frac{\overline{z}}{\overline{w}}$ for complex numbers $z$ and $w$, and that $\overline{n} = n$ for real $n$.

3. Use the fact that for a convergent series $\sum a_n = A$, we have $\sum \overline{a_n} = \overline{A}$.

4. Given that $c$ is a Dirichlet character that is not the principal character, we know from the `LFUNCTION` theorem that the series $\sum_{n=1}^{\infty} \frac{c(n)}{n}$ converges to $L(c)$.

5. Therefore, the series $\sum_{n=1}^{\infty} \overline{\frac{c(n)}{n}} = \sum_{n=1}^{\infty} \frac{\overline{c(n)}}{n}$ converges to $\overline{L(c)}$.

6. Since $L(\overline{c})$ is defined as exactly this sum, we have $L(\overline{c}) = \overline{L(c)}$.

### Mathematical insight
This theorem establishes an important symmetry property of L-functions: the L-function of a conjugated character equals the conjugate of the original L-function. This relation is fundamental in analytic number theory and is used in studying zeros of L-functions and their functional equations.

For real-valued Dirichlet characters, this implies that their L-functions are real-valued as well. For complex-valued characters, this theorem helps relate the values of L-functions of conjugate characters, which is particularly useful in studying the distribution of primes in arithmetic progressions.

The theorem is a direct consequence of the linearity of the infinite sum and the properties of complex conjugation. It's a natural property one would expect from L-functions, but it requires formal verification due to the delicate convergence issues involved with infinite series.

### Dependencies
- Definitions:
  - `dirichlet_character`: Definition of a Dirichlet character
  - `chi_0`: The principal Dirichlet character
  - `Lfunction_DEF`: Definition of the L-function as an infinite sum

- Theorems:
  - `LFUNCTION`: States that for a non-principal Dirichlet character c, the series $\sum_{n=1}^{\infty} \frac{c(n)}{n}$ converges to L(c)

### Porting notes
When porting this theorem:
- Ensure that the definition of Dirichlet characters and L-functions match exactly
- Verify that theorems about complex conjugation of infinite sums are available
- The proof relies on the convergence of the L-function series, which is established in the `LFUNCTION` theorem. This convergence proof might need different approaches in other proof assistants based on their libraries for analysis.

---

## LFUNCTION_PARTIAL_SUM

### Name of formal statement
LFUNCTION_PARTIAL_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_PARTIAL_SUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. 1 <= n
                     ==> norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                          <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:num->complex`; `\n. inv(Cx(&n))`; `1`; `1`]
                SERIES_DIRICHLET_COMPLEX_EXPLICIT) THEN
  REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD] THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_NUM] THEN
  REWRITE_TAC[CX_INV; GSYM complex_div; GSYM real_div] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. vsum(k+1..n) (\n. c(n) / Cx(&n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION) THEN
    MP_TAC(ISPECL [`sequentially`; `vsum (1..k) (\n. c n / Cx (&n))`]
                LIM_CONST) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT; sums; FROM_INTER_NUMSEG] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k + 1` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `k + 1 <= m ==> k <= m`)) THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= k ==> 1 <= k + 1`] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`; REAL_OF_NUM_ADD]]);;
```

### Informal statement
For any modulus $d$ and Dirichlet character $c$ such that $c$ is not the principal character $\chi_0(d)$, there exists a constant $B > 0$ such that for all $n \geq 1$:
$$\left\| L(c) - \sum_{i=1}^{n} \frac{c(i)}{i} \right\| \leq \frac{B}{n+1}$$

Here, $L(c)$ represents the L-function associated with the Dirichlet character $c$, which is the sum of the infinite series $\sum_{i=1}^{\infty} \frac{c(i)}{i}$.

### Informal proof
We prove that the partial sums of the Dirichlet L-function converge at a controlled rate. The proof proceeds as follows:

- We apply the theorem `SERIES_DIRICHLET_COMPLEX_EXPLICIT` to the character $c$ and the function $\frac{1}{n}$, with index starting at $1$.

- Since $c$ is not the principal character $\chi_0(d)$, we can use `BOUNDED_LFUNCTION_PARTIAL_SUMS` to establish that the partial sums of the Dirichlet character are bounded.

- We use `LIM_INV_N` which states that $\frac{1}{n} \to 0$ as $n \to \infty$.

- After simplifying expressions involving complex and real numbers, we establish that:
  1. The sequence of partial sums $\sum_{i=1}^{n} \frac{c(i)}{i}$ converges to $L(c)$ (using the `LFUNCTION` theorem)
  2. For any $k \geq 1$, the tail of the series $\sum_{i=k+1}^{n} \frac{c(i)}{i}$ converges to $L(c) - \sum_{i=1}^{k} \frac{c(i)}{i}$
  3. This convergence follows a controlled rate bounded by $\frac{B}{n+1}$ for some constant $B > 0$

- By applying `LIM_NORM_UBOUND` to this tail series and using the continuity of the norm function, we obtain the desired inequality for the error term when truncating the L-function series.

### Mathematical insight
This theorem provides an explicit error bound for approximating the Dirichlet L-function $L(c)$ by its partial sums. For non-principal characters, it shows that the error decreases at a rate of $O(\frac{1}{n})$. This is a fundamental result for numerical approximations of L-functions and for proving various analytic properties of these functions.

The result is particularly important because:
- It gives a concrete, computable upper bound on the approximation error
- The convergence rate of $O(\frac{1}{n})$ is related to the fact that Dirichlet series converge conditionally rather than absolutely for non-principal characters
- Such explicit bounds are essential for computational number theory and for proving more advanced properties of L-functions

### Dependencies
**Theorems:**
- `LIM_INV_N`: Limit of $\frac{1}{n}$ tends to 0 as n approaches infinity
- `BOUNDED_LFUNCTION_PARTIAL_SUMS`: The partial sums of a non-principal Dirichlet character are bounded
- `LFUNCTION`: Defines the Dirichlet L-function as the sum of the series $\sum_{n=1}^{\infty} \frac{c(n)}{n}$
- `SERIES_DIRICHLET_COMPLEX_EXPLICIT` (used but not listed in dependencies)
- `LIM_NORM_UBOUND` (used but not listed in dependencies)

**Definitions:**
- `dirichlet_character`: A function satisfying the properties of a Dirichlet character
- `chi_0`: The principal character, defined as 1 when n is coprime to d and 0 otherwise

### Porting notes
When porting this theorem:
1. Ensure your system has a representation of complex numbers and their operations
2. The proof relies heavily on theorems about convergence of Dirichlet series, which may require different approaches in other systems
3. The explicit error bound $\frac{B}{n+1}$ is system-agnostic and should be achievable in any system
4. Pay attention to the handling of partial sums and series convergence, as different systems may have different primitives for these concepts

---

## LFUNCTION_PARTIAL_SUM_STRONG

### Name of formal statement
LFUNCTION_PARTIAL_SUM_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_PARTIAL_SUM_STRONG = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                         <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION_PARTIAL_SUM) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B (norm(Lfunction c))` THEN
  ASM_SIMP_TAC[REAL_LT_MAX] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; VECTOR_SUB_RZERO; ARITH] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
For any modulus $d$ and Dirichlet character $c$ that is not the principal character $\chi_0(d)$, there exists a positive real number $B > 0$ such that for all natural numbers $n$, the norm of the difference between the $L$-function $L(c)$ and its partial sum $\sum_{i=1}^{n} \frac{c(i)}{i}$ is bounded by:

$$\left\| L(c) - \sum_{i=1}^{n} \frac{c(i)}{i} \right\| \leq \frac{B}{n+1}$$

### Informal proof
This theorem strengthens the `LFUNCTION_PARTIAL_SUM` result by removing the condition that $n \geq 1$ in the hypothesis.

The proof proceeds as follows:

* We begin with the given conditions that $c$ is a Dirichlet character modulo $d$ and $c$ is not the principal character.
* We apply the earlier theorem `LFUNCTION_PARTIAL_SUM` to these conditions, obtaining a constant $B > 0$ such that for all $n \geq 1$:
  $$\left\| L(c) - \sum_{i=1}^{n} \frac{c(i)}{i} \right\| \leq \frac{B}{n+1}$$
* We define a new constant as $\max(B, \|L(c)\|)$, which is positive since $B > 0$.
* For the case where $n = 0$:
  * The sum $\sum_{i=1}^{0}$ is empty, so it evaluates to 0
  * The expression becomes $\|L(c) - 0\| = \|L(c)\| \leq \max(B, \|L(c)\|) = \frac{\max(B, \|L(c)\|)}{0+1}$
* For the case where $n \geq 1$:
  * We apply the bound from `LFUNCTION_PARTIAL_SUM` directly
  * Since $\frac{B}{n+1} \leq \frac{\max(B, \|L(c)\|)}{n+1}$, the result follows

### Mathematical insight
This theorem provides a slightly stronger version of the bound for the approximation of an L-function by its partial sums. The key insight is extending the bound to include $n = 0$, which makes the result more generally applicable.

The estimate gives us a uniform rate of convergence for the Dirichlet series representing the L-function. The bound $\frac{B}{n+1}$ shows that the approximation error decreases at least as fast as $\frac{1}{n+1}$, which is a commonly encountered convergence rate for such series.

This result is important for numerical approximations of L-functions and for theoretical analyses that require explicit error bounds on truncated Dirichlet series.

### Dependencies
- Theorems:
  - `LFUNCTION_PARTIAL_SUM`: Gives the bound for the case when $n \geq 1$
- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character modulo $d$
  - `chi_0`: Defines the principal character modulo $d$

### Porting notes
When porting this theorem, pay attention to:
- The definition of the L-function and how it's represented in the target system
- The handling of partial sums of infinite series
- The vector norms used to measure the approximation error

The proof is relatively straightforward, mainly extending an existing result to include the boundary case at $n = 0$.

---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) -
                vsum(1..x) (\n. c(n) * Cx(log(&n) / &n)) | x IN (:num)}`,
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[LOG_MANGOLDT_SUM; real_div; CX_MUL;  GSYM VSUM_CX; FINITE_DIVISORS;
           LE_1; GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; COMPLEX_INV_MUL; CX_MUL; CX_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(ck * cn) * cm * k * n:complex = (ck * k) * (cn * cm * n)`] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&18 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[real_abs; MANGOLDT_POS_LE] THEN ASM_CASES_TAC `x = 0` THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_LE_MUL; REAL_LT_IMP_LE;
               REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. B / &x * mangoldt n)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B / &x * &18 * &x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REWRITE_RULE[ETA_AX] PSI_BOUND];
      ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> B / x * &18 * x = &18 * B`;
                   REAL_OF_NUM_EQ; REAL_LE_REFL]]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_MUL;
               REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; MANGOLDT_POS_LE] THEN
  REWRITE_TAC[real_div; REAL_ARITH `a * b * c <= d <=> (a * c) * b <= d`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[MANGOLDT_POS_LE] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / (&(x DIV n) + &1)` THEN
  ASM_REWRITE_TAC[GSYM complex_div] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `1 <= x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;
```

### Informal statement
For any modulus $d$ and Dirichlet character $c$ that is not the principal character $\chi_0$, the set 
$$ \left\{ L(c) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} - \sum_{n=1}^{x} c(n) \cdot \frac{\log(n)}{n} \,\middle|\, x \in \mathbb{N} \right\} $$
is bounded.

Here:
- $L(c)$ is the Dirichlet L-function associated with the character $c$
- $\Lambda(n)$ is the von Mangoldt function
- $\chi_0$ is the principal character defined by $\chi_0(n) = 1$ if $\gcd(n,d) = 1$ and $\chi_0(n) = 0$ otherwise

### Informal proof
We need to show the existence of a positive real number that bounds the norm of all elements in the given set. By the definition of a bounded set, we need to find $M > 0$ such that for all $x \in \mathbb{N}$, the norm of the corresponding complex number is at most $M$.

First, we use the identity 
$$\log(n) = \sum_{d|n} \Lambda(d)$$

from `LOG_MANGOLDT_SUM` to rewrite our expressions. After distributing the character $c$ and applying linearity of summation, we can rearrange the terms using the divisor-sum identity from `VSUM_VSUM_DIVISORS`.

Since $c$ is a Dirichlet character, we have the multiplicative property $c(mn) = c(m)c(n)$ from `DIRICHLET_CHARACTER_MUL`.

By `LFUNCTION_PARTIAL_SUM_STRONG`, for any non-principal character $c$, there exists $B > 0$ such that
$$\left\|L(c) - \sum_{n=1}^{x} \frac{c(n)}{n}\right\| \leq \frac{B}{x+1}$$

We claim that $18B$ is a bound for our set. To show this, we:

- Apply the triangle inequality for the sum
- Use the fact that $|c(n)| = 1$ if $\gcd(n,d) = 1$ and $|c(n)| = 0$ otherwise (from `DIRICHLET_CHARACTER_NORM`)
- Apply the bound $\sum_{n=1}^{x} \Lambda(n) \leq 18x$ from `PSI_BOUND`
- Use the properties of the von Mangoldt function, particularly that it's non-negative (`MANGOLDT_POS_LE`)

After careful manipulation of inequalities and applying the division theorem to handle the terms involving $x \div n$, we establish that $18B$ indeed serves as the required bound.

### Mathematical insight
This lemma provides a crucial bound for the difference between certain partial sums related to Dirichlet L-functions. It plays an important role in the theory of Dirichlet L-functions and the distribution of prime numbers in arithmetic progressions.

The result helps establish that while the individual sums $\sum c(n)\Lambda(n)/n$ and $\sum c(n)\log(n)/n$ might grow with $x$, their difference (after appropriate normalization by $L(c)$) remains bounded. This boundedness is essential for proving properties like non-vanishing of L-functions at $s=1$, which in turn leads to the Prime Number Theorem for arithmetic progressions.

The result is non-trivial because it requires careful analysis of how the von Mangoldt function $\Lambda(n)$ interacts with Dirichlet characters.

### Dependencies
- **Theorems**:
  - `MANGOLDT_POS_LE`: The von Mangoldt function is non-negative
  - `LOG_MANGOLDT_SUM`: For $n ≠ 0$, $\log(n) = \sum_{d|n} \Lambda(d)$
  - `PSI_BOUND`: A bound on the summatory von Mangoldt function: $\sum_{n=1}^x \Lambda(n) \leq 18x$
  - `VSUM_VSUM_DIVISORS`: An identity for rearranging sums over divisors
  - `DIRICHLET_CHARACTER_MUL`: Multiplicativity of Dirichlet characters: $c(mn) = c(m)c(n)$
  - `DIRICHLET_CHARACTER_NORM`: Norm of a Dirichlet character value
  - `LFUNCTION_PARTIAL_SUM_STRONG`: Convergence bound for Dirichlet L-functions

- **Definitions**:
  - `dirichlet_character`: Definition of a Dirichlet character
  - `chi_0`: The principal Dirichlet character

### Porting notes
- The proof relies heavily on manipulation of sums and inequalities involving Dirichlet characters and the von Mangoldt function. Any system porting this would need good support for summation operations and inequality reasoning.
- The bound constant "18" in `PSI_BOUND` is a specific numerical result that might be derived differently in other systems.
- The definition of "bounded set" might vary slightly between systems, but the core concept of finding a uniform bound should be consistent.

---

## SUMMABLE_CHARACTER_LOG_OVER_N

### Name of formal statement
SUMMABLE_CHARACTER_LOG_OVER_N

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_CHARACTER_LOG_OVER_N = prove
 (`!c d. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> summable (from 1) (\n. c(n) * Cx(log(&n) / &n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  MAP_EVERY EXISTS_TAC [`4`; `1`] THEN REWRITE_TAC[REAL_CX] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  CONJ_TAC THENL
   [SIMP_TAC[DECREASING_LOG_OVER_N; GSYM REAL_OF_NUM_ADD; RE_CX];
    MP_TAC LIM_LOG_OVER_N THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[CX_LOG; CX_DIV; LE_1; REAL_OF_NUM_LT]]);;
```

### Informal statement
For any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0$ modulo $d$, the series $\sum_{n=1}^{\infty} c(n) \cdot \frac{\log n}{n}$ is summable.

More precisely, for all $c$ and $d$ where:
- $c$ is a Dirichlet character modulo $d$ (satisfying periodicity, relation with coprimality, and multiplicativity)
- $c \neq \chi_0(d)$ (i.e., $c$ is not the principal character)

Then the infinite series $\sum_{n=1}^{\infty} c(n) \cdot \frac{\log n}{n}$ converges.

### Informal proof
We prove this theorem using the Dirichlet test for summability of complex series. The proof consists of several key steps:

* Apply the Dirichlet test for complex series (`SERIES_DIRICHLET_COMPLEX`), which requires:
  - The sequence of partial sums from the Dirichlet character values is bounded
  - The sequence $\frac{\log n}{n}$ is decreasing for sufficiently large $n$
  - The sequence $\frac{\log n}{n}$ converges to $0$

* For the first condition, we use `BOUNDED_LFUNCTION_PARTIAL_SUMS` which states that for any non-principal Dirichlet character, the set of partial sums $\{\sum_{i=1}^{n} c(i) \mid n \in \mathbb{N}\}$ is bounded.

* For the second condition, we use `DECREASING_LOG_OVER_N` which shows that $\frac{\log(n+1)}{n+1} \leq \frac{\log(n)}{n}$ for all $n \geq 4$.

* For the third condition, we use `LIM_LOG_OVER_N` which establishes that $\lim_{n \to \infty} \frac{\log n}{n} = 0$.

* We set the parameters in the Dirichlet test as starting from index $4$ and with coefficient $1$, ensuring all conditions of the test are satisfied.

### Mathematical insight
This theorem is fundamental in analytic number theory, particularly in the study of Dirichlet L-functions. The summability of $\sum_{n=1}^{\infty} c(n) \cdot \frac{\log n}{n}$ is closely related to the behavior of the derivative of Dirichlet L-functions at $s = 1$.

The distinction between principal and non-principal characters is crucial here: for non-principal characters, the partial sums of character values remain bounded, which enables the application of the Dirichlet test. This boundedness property fails for the principal character.

This result forms part of the analytical machinery needed to establish properties of L-functions, which are essential tools in understanding the distribution of primes in arithmetic progressions and other number-theoretic problems.

### Dependencies
#### Theorems:
- `SERIES_DIRICHLET_COMPLEX`: The Dirichlet test for summability of complex series
- `BOUNDED_LFUNCTION_PARTIAL_SUMS`: Shows that partial sums of non-principal Dirichlet characters are bounded
- `DECREASING_LOG_OVER_N`: Proves that $\frac{\log(n+1)}{n+1} \leq \frac{\log(n)}{n}$ for $n \geq 4$
- `LIM_LOG_OVER_N`: Establishes that $\lim_{n \to \infty} \frac{\log n}{n} = 0$
- `CX_LOG`: Relates complex and real logarithms

#### Definitions:
- `dirichlet_character`: Defines a Dirichlet character modulo d
- `chi_0`: The principal character modulo d

### Porting notes
When porting this theorem:
1. Ensure your system has a well-established theory of Dirichlet characters with the required properties
2. Carefully handle the complex-valued functions and convergence criteria
3. The proof relies on the Dirichlet test for complex series, which should be available in the target system
4. The treatment of real and complex numbers in the target system may require adjustments to the representation of $\frac{\log n}{n}$

---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT

### Name of formal statement
BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_CHARACTER_LOG_OVER_N) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_SUMS_BOUNDED) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUMS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE;
              GSYM CONJ_ASSOC] THEN
  X_GEN_TAC `n:num` THEN REPEAT(EXISTS_TAC `n:num`) THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For all positive integers $d$ and Dirichlet characters $c$ modulo $d$, if $c$ is non-principal (i.e., $c \neq \chi_0(d)$), then the set
$$\left\{ L(c) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} \mid x \in \mathbb{N} \right\}$$
is bounded.

Here, $L(c)$ is the Dirichlet L-function associated with the character $c$, $\Lambda(n)$ is the von Mangoldt function, and $\chi_0(d)$ is the principal character modulo $d$.

### Informal proof
The proof proceeds in several steps:

* First, we apply the lemma `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA` to our assumption that $c$ is a non-principal Dirichlet character. This lemma tells us that the set 
  $$\left\{ L(c) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} - \sum_{n=1}^{x} c(n) \cdot \frac{\log(n)}{n} \mid x \in \mathbb{N} \right\}$$
  is bounded.

* Next, from the same assumption, we apply `SUMMABLE_CHARACTER_LOG_OVER_N`, which states that the series $\sum_{n=1}^{\infty} c(n) \cdot \frac{\log(n)}{n}$ is convergent.

* Using `SUMMABLE_IMP_SUMS_BOUNDED`, we deduce that the partial sums of this convergent series form a bounded set.

* By applying `BOUNDED_SUMS` to the result, we know that the set of all these partial sums is bounded.

* Finally, we use `BOUNDED_SUBSET` to show that our target set is a subset of the sum of the two bounded sets from above, and therefore it is also bounded.

* The proof is completed with some technical manipulations involving set theory and vector arithmetic.

### Mathematical insight
This theorem provides a crucial boundedness result for Dirichlet L-functions multiplied by specific partial sums involving the von Mangoldt function. The von Mangoldt function $\Lambda(n)$ equals $\log(p)$ when $n = p^k$ for some prime $p$ and positive integer $k$, and zero otherwise.

The boundedness of this expression is important in analytical number theory, particularly in the study of the distribution of primes in arithmetic progressions. This result is a key step in establishing the analytic properties of Dirichlet L-functions and their connections to the distribution of prime numbers.

The proof technique involves decomposing the expression into two parts: one that is directly shown to be bounded through the lemma, and another that is bounded because it forms the partial sums of a convergent series.

### Dependencies
- **Theorems**:
  - `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA`: Shows boundedness of L-function times the difference of two character sums
  - `SUMMABLE_CHARACTER_LOG_OVER_N`: Establishes convergence of the series of character values multiplied by logarithm terms
  - `SUMMABLE_IMP_SUMS_BOUNDED`: General theorem that convergent series have bounded partial sums
  - `BOUNDED_SUMS`: Boundedness of sums of bounded sets
  - `BOUNDED_SUBSET`: A subset of a bounded set is bounded

- **Definitions**:
  - `dirichlet_character`: Defines the properties of a Dirichlet character
  - `chi_0`: The principal character modulo d

### Porting notes
When porting this theorem:
1. Ensure that the Dirichlet L-function and von Mangoldt function are properly defined in your target system
2. The proof relies heavily on analytical concepts like boundedness and convergence of series, which might need specific library support
3. Be aware of potential differences in handling complex-valued functions and summations in different proof assistants

---

## BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_NONZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ ~(Lfunction c = Cx(&0))
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; COMPLEX_NORM_NZ] THEN
  ASM_MESON_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV]);;
```

### Informal statement
For any positive integer $d$ and any Dirichlet character $c$ modulo $d$ such that $c$ is not the principal character $\chi_0$ and the $L$-function $L(s,c)$ is nonzero, the set 
$$\left\{ \sum_{n=1}^{x} c(n) \frac{\Lambda(n)}{n} \mid x \in \mathbb{N} \right\}$$
is bounded, where $\Lambda(n)$ is the von Mangoldt function.

### Informal proof
We need to prove that the set of all partial sums of the series $\sum_{n=1}^{\infty} c(n) \frac{\Lambda(n)}{n}$ is bounded.

Given that $c$ is a Dirichlet character modulo $d$ that is not the principal character $\chi_0$, and $L(s,c) \neq 0$, we apply the theorem `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT` which states that the set 
$$\left\{ L(s,c) \cdot \sum_{n=1}^{x} c(n) \frac{\Lambda(n)}{n} \mid x \in \mathbb{N} \right\}$$
is bounded.

For a set to be bounded, there must exist a constant $M$ such that $\|z\| \leq M$ for all elements $z$ in the set. 

For each $x \in \mathbb{N}$, we have:
$$\left\|L(s,c) \cdot \sum_{n=1}^{x} c(n) \frac{\Lambda(n)}{n}\right\| \leq M$$

Using the property that $\|a \cdot b\| = \|a\| \cdot \|b\|$ for complex numbers, we get:
$$\left\|L(s,c)\right\| \cdot \left\|\sum_{n=1}^{x} c(n) \frac{\Lambda(n)}{n}\right\| \leq M$$

Since $L(s,c) \neq 0$, we have $\|L(s,c)\| \neq 0$, so we can divide both sides:
$$\left\|\sum_{n=1}^{x} c(n) \frac{\Lambda(n)}{n}\right\| \leq \frac{M}{\|L(s,c)\|}$$

This shows that the set of partial sums is bounded by the constant $\frac{M}{\|L(s,c)\|}$.

### Mathematical insight
This theorem establishes an important boundedness property for partial sums of Dirichlet series involving the von Mangoldt function $\Lambda(n)$ weighted by non-principal Dirichlet characters.

The boundedness of these partial sums is a crucial component in analytic number theory, particularly in the study of the distribution of prime numbers in arithmetic progressions. This result contributes to the broader machinery used in proving results like the Prime Number Theorem for arithmetic progressions.

The requirement that $L(s,c) \neq 0$ is significant - it allows us to normalize the bounded set by dividing by a non-zero value. This condition relates to the non-vanishing of Dirichlet L-functions, which is a deep topic in analytic number theory with connections to the Generalized Riemann Hypothesis.

### Dependencies
- Theorems:
  - `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT`: Establishes that the set of products of the L-function with partial sums of the Dirichlet-Mangoldt series is bounded when the character is non-principal.
  
- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character modulo d as a function satisfying periodicity, multiplicativity, and taking value zero exactly on numbers not coprime to d.
  - `chi_0`: The principal character modulo d, defined to be 1 on numbers coprime to d and 0 otherwise.

### Porting notes
When porting this theorem:
1. Ensure that the Dirichlet character, L-function, and von Mangoldt function are properly defined in the target system.
2. The proof relies on properties of complex numbers and basic analysis principles (boundedness, norms) which should be available in most proof assistants.
3. Be aware that HOL Light's representation of complex numbers and series may differ from other systems, so adaptations might be needed.
4. The argument based on dividing by a non-zero value to preserve boundedness is a key step that should be carefully translated.

---

## MANGOLDT_LOG_SUM

### Name of formal statement
MANGOLDT_LOG_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT_LOG_SUM = prove
 (`!n. 1 <= n
       ==> mangoldt(n) = --(sum {d | d divides n} (\d. mobius(d) * log(&d)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. mangoldt n`; `\n. log(&n)`] MOBIUS_INVERSION) THEN
  ASM_SIMP_TAC[LOG_MANGOLDT_SUM; LE_1] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {d | d divides n} (\x. mobius x * (log(&n) - log(&x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN
    ABBREV_TAC `q = n DIV d` THEN
    MAP_EVERY ASM_CASES_TAC [`q = 0`; `d = 0`] THEN
    ASM_SIMP_TAC[MULT_CLAUSES; LE_1] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; LOG_MUL; REAL_OF_NUM_LT; LE_1] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB; FINITE_DIVISORS; LE_1] THEN
    ASM_SIMP_TAC[SUM_RMUL; REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    MATCH_MP_TAC(REAL_ARITH `a = &0 ==> a - b = --b`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all positive integers $n \geq 1$, the von Mangoldt function $\Lambda(n)$ can be expressed as:

$$\Lambda(n) = -\sum_{d|n} \mu(d) \log(d)$$

where:
- $\mu(d)$ is the Möbius function
- $\log(d)$ is the natural logarithm of $d$
- The sum is over all divisors $d$ of $n$

### Informal proof
We begin by applying the Möbius inversion formula to express the von Mangoldt function in terms of logarithm. 

First, we know from `LOG_MANGOLDT_SUM` that for any non-zero natural number $n$, $\log(n) = \sum_{d|n} \Lambda(d)$.

Applying the Möbius inversion formula (`MOBIUS_INVERSION`), we get:
$\Lambda(n) = \sum_{d|n} \mu(d) \log(n/d)$

Now we transform the summation:
* For each divisor $d$ of $n$, let $q = n/d$
* Note that $\log(n/d) = \log(n) - \log(d)$ using the logarithm property $\log(a/b) = \log(a) - \log(b)$

Therefore:
$\Lambda(n) = \sum_{d|n} \mu(d) (\log(n) - \log(d))$
$= \sum_{d|n} \mu(d) \log(n) - \sum_{d|n} \mu(d) \log(d)$

From the property of the Möbius function (`DIVISORSUM_MOBIUS`), we know that $\sum_{d|n} \mu(d) = 0$ for $n > 1$ and $\sum_{d|n} \mu(d) = 1$ for $n = 1$.

In our case where $n \geq 1$:
* If $n > 1$, then $\sum_{d|n} \mu(d) \log(n) = \log(n) \cdot \sum_{d|n} \mu(d) = \log(n) \cdot 0 = 0$
* If $n = 1$, then $\sum_{d|n} \mu(d) \log(n) = \log(1) \cdot \sum_{d|n} \mu(d) = 0 \cdot 1 = 0$ since $\log(1) = 0$

Thus, $\Lambda(n) = -\sum_{d|n} \mu(d) \log(d)$, which is what we wanted to prove.

### Mathematical insight
This theorem expresses the von Mangoldt function $\Lambda(n)$ in terms of the Möbius function $\mu(n)$ and logarithms of its divisors. The von Mangoldt function is defined as:

$$\Lambda(n) = \begin{cases}
\log(p) & \text{if } n = p^k \text{ for some prime } p \text{ and integer } k \geq 1 \\
0 & \text{otherwise}
\end{cases}$$

The formula provided by this theorem gives an alternative representation using Möbius inversion, which is important in number theory. This relationship is crucial in analytic number theory, particularly in the study of the distribution of prime numbers and the Riemann zeta function.

The theorem is essentially an application of Möbius inversion to the relationship between the logarithm function and the von Mangoldt function. It highlights the profound interconnection between different number-theoretic functions.

### Dependencies
- Theorems:
  - `DIVISORSUM_MOBIUS`: The sum of the Möbius function over divisors is 1 for n=1 and 0 for n>1
  - `MOBIUS_INVERSION`: The Möbius inversion formula
  - `LOG_MUL`: Natural logarithm of a product equals sum of logarithms
  - `LOG_1`: Natural logarithm of 1 equals 0
  - `LOG_MANGOLDT_SUM`: The sum of von Mangoldt function over divisors equals logarithm

- Definitions:
  - `mobius`: The Möbius function

### Porting notes
When porting this theorem:
1. Ensure that the Möbius function and von Mangoldt function are defined with the same conventions
2. Pay attention to the type conversions between natural numbers and reals in the logarithm expressions
3. The proof relies on Möbius inversion, so ensure this theorem is ported first
4. The handling of divisors and divisibility might differ in other systems, so adapt the set notation accordingly

---

## BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c x.
        dirichlet_character d c /\ ~(c = chi_0 d) /\ 1 <= x
        ==> Cx(log(&x)) + vsum (1..x) (\n. c(n) * Cx(mangoldt n / &n)) =
            vsum (1..x) (\n. c(n) / Cx(&n) *
                             vsum {d | d divides n}
                                  (\d. Cx(mobius(d) * log(&x / &d))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MANGOLDT_LOG_SUM] THEN
  MATCH_MP_TAC(COMPLEX_RING `c - b = a ==> (a:complex) + b = c`) THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  SIMP_TAC[CX_NEG; CX_DIV; GSYM VSUM_CX; FINITE_NUMSEG; FINITE_DIVISORS;
           LE_1] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH
   `c / d * x - c * --y / d:complex = c / d * (x + y)`] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_DIVISORS; LE_1] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `vsum (1..x)
         (\n. c n / Cx(&n) * vsum {d | d divides n}
               (\d. Cx(mobius d * log(&x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[CX_MUL; GSYM COMPLEX_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_MESON_TAC[DIVIDES_ZERO; LE_1]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_OF_NUM_LT; LE_1] THEN REAL_ARITH_TAC;
    SIMP_TAC[FINITE_DIVISORS; CX_MUL; SUM_RMUL; LE_1; VSUM_CX] THEN
    SIMP_TAC[REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    SIMP_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    ASM_SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0; IN_NUMSEG; LE_REFL] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_EQ_1) THEN
    ASM_SIMP_TAC[COMPLEX_MUL_LID; COMPLEX_DIV_1]]);;
```

### Informal statement
For all $d, c, x$ such that $c$ is a Dirichlet character modulo $d$, $c$ is not the principal character $\chi_0$ modulo $d$, and $1 \leq x$, we have:
$$\mathbb{C}(\log(x)) + \sum_{n=1}^{x} c(n) \cdot \mathbb{C}\left(\frac{\Lambda(n)}{n}\right) = \sum_{n=1}^{x} \frac{c(n)}{\mathbb{C}(n)} \cdot \sum_{d|n} \mathbb{C}\left(\mu(d) \cdot \log\left(\frac{x}{d}\right)\right)$$

where:
- $\Lambda(n)$ is the von Mangoldt function
- $\mu(d)$ is the Möbius function
- $\mathbb{C}$ maps real numbers to complex numbers
- $\chi_0$ is the principal character defined as $\chi_0(n) = \mathbb{C}(1)$ if $\gcd(n,d)=1$ and $\mathbb{C}(0)$ otherwise

### Informal proof

The proof proceeds as follows:

- We start by applying the von Mangoldt-Möbius relation (`MANGOLDT_LOG_SUM`) which states that for all $n \geq 1$:
  $$\Lambda(n) = -\sum_{d|n} \mu(d) \log(d)$$

- After applying this relation, we need to manipulate the complex sums to obtain the desired identity.

- We rewrite the equation by taking $a + b = c$ and showing that $c - b = a$, then using properties of vector sums.

- For each term in the sum, we transform:
  $$\frac{c(n)}{\mathbb{C}(n)} \cdot \sum_{d|n} \mathbb{C}(\mu(d) \cdot \log(x/d)) - \frac{c(n) \cdot (-\mathbb{C}(\sum_{d|n} \mu(d) \cdot \log(d)))}{\mathbb{C}(n)}$$
  into:
  $$\frac{c(n)}{\mathbb{C}(n)} \cdot \left(\sum_{d|n} \mathbb{C}(\mu(d) \cdot \log(x/d)) + \sum_{d|n} \mathbb{C}(\mu(d) \cdot \log(d))\right)$$

- We then use the logarithm property $\log(x/d) = \log(x) - \log(d)$ to simplify the inner sum to:
  $$\sum_{d|n} \mathbb{C}(\mu(d) \cdot \log(x))$$

- Using the Möbius inversion formula (`DIVISORSUM_MOBIUS`), we know that $\sum_{d|n} \mu(d) = 1$ if $n = 1$ and $0$ otherwise.

- Finally, we use the property that $c(1) = \mathbb{C}(1)$ for any Dirichlet character (`DIRICHLET_CHARACTER_EQ_1`) to complete the proof.

### Mathematical insight

This lemma provides a reformulation of a sum involving Dirichlet characters and the von Mangoldt function. It's an important step in the study of Dirichlet L-functions and the distribution of primes in arithmetic progressions.

The key insight is how the Möbius inversion formula allows us to connect the von Mangoldt function with logarithmic sums, which is crucial for the analytic methods used in prime number theory.

This result is part of the analytic machinery needed for proving results like Dirichlet's theorem on primes in arithmetic progressions or for establishing bounds on character sums in the context of the Generalized Riemann Hypothesis.

### Dependencies
- Theorems:
  - `DIVISORSUM_MOBIUS`: Sum of Möbius function over divisors equals 1 if n=1, 0 otherwise
  - `LOG_DIV`: Logarithm of division is difference of logarithms
  - `DIRICHLET_CHARACTER_EQ_1`: Dirichlet character evaluated at 1 equals complex 1
  - `MANGOLDT_LOG_SUM`: Mangoldt function in terms of Möbius sum

- Definitions:
  - `mobius`: The Möbius function
  - `dirichlet_character`: Definition of Dirichlet character
  - `chi_0`: The principal Dirichlet character

### Porting notes
When porting this theorem:
- Ensure that your system has appropriate representations of complex numbers and the complex embedding of reals
- The definition of Dirichlet characters may vary between systems
- The theorem relies on properties of number-theoretic functions like the von Mangoldt function and the Möbius function, which should be defined consistently
- The vector sum notation `vsum` in HOL Light corresponds to finite sums in other systems

---

## SUM_LOG_OVER_X_BOUND

### Name of formal statement
SUM_LOG_OVER_X_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_LOG_OVER_X_BOUND = prove
 (`!x. abs(sum(1..x) (\n. log(&x / &n) / &x)) <= &4`,
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  SIMP_TAC[real_div; SUM_RMUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..x) (\n. abs(log(&x / &n)))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN
  ASM_SIMP_TAC[real_abs; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE; LOG_DIV] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; GSYM LOG_FACT] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOG_FACT_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * l + abs(x) + &1 <= b
    ==> abs(lf - (xl - x + &1)) <= &2 * l
        ==> xl - lf <= b`) THEN
 MATCH_MP_TAC(REAL_ARITH
   `&1 <= x /\ l <= x ==> &2 * l + abs(x) + &1 <= &4 * x`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_1; LOG_LE_REFL]);;
```

### Informal statement
For any natural number $x$, the absolute value of the sum $\sum_{n=1}^{x} \frac{\log(x/n)}{x}$ is bounded by $4$:

$$\forall x \in \mathbb{N}. \left| \sum_{n=1}^{x} \frac{\log(x/n)}{x} \right| \leq 4$$

### Informal proof
We prove that for any natural number $x$, the sum $\sum_{n=1}^{x} \frac{\log(x/n)}{x}$ has absolute value at most $4$.

- First, handle the case when $x = 0$:
  - The sum $\sum_{n=1}^{0}$ is empty, evaluating to $0$, and $|0| \leq 4$.

- For $x \neq 0$:
  - Rewrite $\frac{\log(x/n)}{x} = \frac{1}{x} \cdot \log(x/n)$
  - Factor out $\frac{1}{x}$ from the sum: $\frac{1}{x} \cdot \sum_{n=1}^{x} \log(x/n)$
  - Apply properties of absolute value: $\left|\frac{1}{x} \cdot \sum_{n=1}^{x} \log(x/n)\right| = \frac{1}{x} \cdot \left|\sum_{n=1}^{x} \log(x/n)\right|$
  - So we need to show: $\frac{1}{x} \cdot \left|\sum_{n=1}^{x} \log(x/n)\right| \leq 4$, or equivalently: $\left|\sum_{n=1}^{x} \log(x/n)\right| \leq 4x$
  
- The sum $\sum_{n=1}^{x} \log(x/n)$ can be bounded by $\sum_{n=1}^{x} |\log(x/n)|$
  - Note that for each $n$ from $1$ to $x$, we have $\frac{x}{n} \geq 1$, so $\log(x/n) \geq 0$ by `LOG_POS`
  - Therefore, $|\log(x/n)| = \log(x/n)$ for each term
  
- Using the logarithm property $\log(a/b) = \log(a) - \log(b)$ (from `LOG_DIV`):
  - $\sum_{n=1}^{x} \log(x/n) = \sum_{n=1}^{x} (\log(x) - \log(n))$
  - $= x\log(x) - \sum_{n=1}^{x} \log(n)$
  - $= x\log(x) - \log(\text{FACT}(x))$ using `LOG_FACT`
  
- From `LOG_FACT_BOUNDS`, if $x \neq 0$:
  - $|\log(\text{FACT}(x)) - (x\log(x) - x + 1)| \leq 2\log(x)$
  
- Thus, $|x\log(x) - \log(\text{FACT}(x))| \leq 2\log(x) + |x - 1|$
- Since $x \geq 1$ and $\log(x) \leq x$ (from `LOG_LE_REFL`), we have:
  - $2\log(x) + |x - 1| + 1 \leq 4x$, which completes the proof.

### Mathematical insight
This theorem provides a constant bound (namely 4) on the absolute value of the sum of logarithmic terms divided by $x$. This type of bound is important in analytic number theory, particularly in the study of the distribution of prime numbers.

The sum $\sum_{n=1}^{x} \frac{\log(x/n)}{x}$ can be seen as an average of logarithmic ratios. What makes this result interesting is that despite $x$ potentially growing without bound, the sum remains bounded by a constant. This is achieved by carefully analyzing how the terms $\log(x/n)$ behave, using connections to factorials through the equality $\sum_{n=1}^{x} \log(n) = \log(\text{FACT}(x))$, and applying Stirling's approximation (which appears in the `LOG_FACT_BOUNDS` theorem).

### Dependencies
#### Theorems
- `LOG_DIV`: For $x, y > 0$, $\log(x/y) = \log(x) - \log(y)$
- `LOG_POS`: For $x \geq 1$, $\log(x) \geq 0$
- `LOG_FACT`: For all $n$, $\log(\text{FACT}(n)) = \sum_{d=1}^{n} \log(d)$
- `LOG_LE_REFL`: For $n \neq 0$, $\log(n) \leq n$
- `LOG_FACT_BOUNDS`: For $n \neq 0$, $|\log(\text{FACT}(n)) - (n\log(n) - n + 1)| \leq 2\log(n)$

### Porting notes
When porting this theorem:
1. Ensure your target system has the necessary logarithmic properties and theorems about factorial approximation.
2. The proof relies on Stirling's approximation (via `LOG_FACT_BOUNDS`), which may need to be ported first.
3. The proof involves several inequalities and algebraic manipulations that should translate well to other proof assistants.
4. Note that HOL Light uses `&n` to represent the real number corresponding to natural number `n`, which might have different notation in other systems.

---

## BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_ZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ Lfunction c = Cx(&0)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) +
                    Cx(log(&x)) | x IN (:num)}`,
  ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SIMP_TAC[SET_RULE `{f x | x IN (:num)} = f 0 INSERT {f x | ~(x = 0)}`] THEN
  REWRITE_TAC[BOUNDED_INSERT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_DIRICHLET_MANGOLDT_LEMMA) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_DIVISORS; LE_1] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL; complex_div; COMPLEX_INV_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `((ck * cn) * k' * n') * m * l = (cn * m * n') * l * (ck * k')`] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  EXISTS_TAC `&4 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(1..x) (\n. inv(&n) * log(&x / &n) * B / (&(x DIV n) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_INV_EQ; REAL_POS] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ASM_SIMP_TAC[REAL_FIELD `&1 <= n ==> inv(n) * n = &1`; REAL_OF_NUM_LE;
                   REAL_ABS_MOBIUS];
      SIMP_TAC[CX_LOG; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
      SIMP_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1;
                   REAL_MUL_LID; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SIMP_TAC[real_div; REAL_RING `a * l * B * i:real = ((l * i) * a) * B`] THEN
  REWRITE_TAC[SUM_RMUL] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. log(&x / &n) / &x)` THEN
  ASM_SIMP_TAC[REAL_ARITH `abs x <= a ==> x <= a`; SUM_LOG_OVER_X_BOUND] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[GSYM real_div; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;
```

### Informal statement
For any integer $d$ and Dirichlet character $c$ modulo $d$, if $c$ is non-principal (i.e., $c \neq \chi_0(d)$) and $L(c) = 0$, then the set
$$\left\{\sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} + \log(x) \mid x \in \mathbb{N}\right\}$$
is bounded, where $\Lambda(n)$ is the von Mangoldt function.

### Informal proof
The proof proceeds by showing that for all sufficiently large $x$, the sum in question can be bounded by a constant:

* First, we rewrite the theorem using symmetry of addition to work with $\log(x) + \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n}$.

* We apply `LFUNCTION_PARTIAL_SUM_STRONG` to the non-principal character $c$, which tells us that there exists a positive constant $B$ such that 
$$\|L(c) - \sum_{n=1}^{x} \frac{c(n)}{n}\| \leq \frac{B}{x+1}$$
  
  Since $L(c) = 0$ by our hypothesis, this simplifies to 
$$\|\sum_{n=1}^{x} \frac{c(n)}{n}\| \leq \frac{B}{x+1}$$

* We note that the set we're examining can be written as a singleton set (for $x=0$) union with the set for $x \geq 1$, so we can focus on bounding the values for $x \geq 1$.

* For $x \geq 1$, we apply `BOUNDED_DIRICHLET_MANGOLDT_LEMMA`, which allows us to express $\log(x) + \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n}$ in terms of divisor sums:
$$\log(x) + \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} = \sum_{n=1}^{x} \frac{c(n)}{n} \cdot \sum_{d|n} \mu(d) \log\left(\frac{x}{d}\right)$$

* Using the multiplicative property of Dirichlet characters (`DIRICHLET_CHARACTER_MUL`), we restructure the sum in a way that allows us to apply the triangle inequality.

* We then establish the bound $4B$ and demonstrate that our sum has absolute value at most this constant, by:
  - Using the triangle inequality for vector sums
  - Applying the Dirichlet character norm bound (which is 1 for integers coprime to $d$ and 0 otherwise)
  - Using the fact that $|\mu(d)| \leq 1$ for all $d$ (`REAL_ABS_MOBIUS`)
  - Leveraging the sum bound for logarithmic terms with `SUM_LOG_OVER_X_BOUND`

Therefore, the set in question is bounded as claimed.

### Mathematical insight
This theorem is related to a key step in understanding the behavior of Dirichlet $L$-functions at their zeros. When a Dirichlet $L$-function $L(c)$ vanishes, this result shows that the partial sums involving the von Mangoldt function weighted by the character values has a specific bounded behavior.

The boundedness of the set is significant because it connects the analytical properties of the $L$-function (having a zero) with the behavior of arithmetic functions (the von Mangoldt function) weighted by that character. This is part of the machinery used in proving the Prime Number Theorem for arithmetic progressions and analyzing the distribution of primes in different residue classes.

The theorem specifically shows that when $L(c) = 0$ for a non-principal character, the partial sums involving the von Mangoldt function remain within a controlled range when corrected by the logarithmic term $\log(x)$.

### Dependencies
- Theorems:
  - `REAL_ABS_MOBIUS`: For any integer $n$, $|\mu(n)| \leq 1$.
  - `LOG_POS`: For any real $x \geq 1$, $\log(x) \geq 0$.
  - `CX_LOG`: For any real $z > 0$, $\mathbb{C}(\log(z)) = \log_{\mathbb{C}}(\mathbb{C}(z))$.
  - `VSUM_VSUM_DIVISORS`: Identity for rearranging sums over divisors.
  - `DIRICHLET_CHARACTER_MUL`: For a Dirichlet character $c$ modulo $d$, $c(mn) = c(m) \cdot c(n)$.
  - `DIRICHLET_CHARACTER_NORM`: For a Dirichlet character $c$ modulo $d$, $|c(n)| = 1$ if $\gcd(d,n)=1$, and $0$ otherwise.
  - `LFUNCTION_PARTIAL_SUM_STRONG`: Bounds for the error in partial sums of $L$-functions.
  - `BOUNDED_DIRICHLET_MANGOLDT_LEMMA`: Identity relating von Mangoldt sums to divisor sums.
  - `SUM_LOG_OVER_X_BOUND`: $|\sum_{n=1}^{x} \frac{\log(x/n)}{x}| \leq 4$.

- Definitions:
  - `dirichlet_character`: Definition of a Dirichlet character modulo $d$.
  - `chi_0`: The principal character modulo $d$.

### Porting notes
When implementing this theorem:

1. Ensure that your system has a solid theory of Dirichlet characters and $L$-functions.
2. The von Mangoldt function $\Lambda(n)$ should be properly defined.
3. The manipulation of complex sums and norms requires good complex arithmetic support.
4. Several steps use inequalities about sums of logarithmic functions that may need separate proofs.
5. Watch out for different treatments of complex numbers and norms in other proof assistants.

---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA = prove
 (`!d. 1 <= d
       ==> norm(vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)))
            <= sum {p | prime p /\ p divides d} (\p. log(&p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides d}
                  (\p. sum {k | 1 <= k /\ p EXP k <= x}
                           (\k. log(&p) / &p pow k))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 <= p /\ 1 <= p /\ 1 < p` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p /\ 1 <= p`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..x) (\k. log(&p) / &p pow k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[IN_DIFF; IN_NUMSEG; IN_ELIM_THM; SUBSET; REAL_POW_LE;
                   REAL_POS; REAL_LE_DIV; LOG_POS; REAL_OF_NUM_LE;
                   PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE];
      REWRITE_TAC[real_div; SUM_LMUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; LOG_POS_LT; REAL_OF_NUM_LT] THEN
      SIMP_TAC[GSYM REAL_POW_INV; SUM_GP; REAL_INV_EQ_1; REAL_OF_NUM_EQ] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_LT_LDIV_EQ;
                   REAL_MUL_LID; REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[real_pow] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x * y /\ &2 * x <= &1
                                ==> x pow 1 - x * y <= &1 - x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT;
                   REAL_OF_NUM_LE; LE_1]]] THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SUM_PRODUCT o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..x` THEN
      SIMP_TAC[SUBSET; FINITE_NUMSEG; IN_NUMSEG; IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE; PRIME_GE_2];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[chi_0; COND_RAND; COND_RATOR] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_SUB_LZERO] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NORM_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[mangoldt; COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
    REWRITE_TAC[TAUT `(if a then &0 else if b then x else &0) =
                      (if ~a /\ b then x else &0)`] THEN
    SIMP_TAC[GSYM real_div; GSYM SUM_RESTRICT_SET; FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_EQ_GENERAL THEN EXISTS_TAC `\(p,k). p EXP k` THEN
    REWRITE_TAC[EXISTS_UNIQUE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; PAIR_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:num` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(coprime(p EXP k,d))` THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`q:num`; `j:num`] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[EQ_PRIME_EXP] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`]  THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[EXP_EQ_0; LE_1; PRIME_0]; ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_ABS_DIV; REAL_ABS_POW;
                REAL_ABS_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = y ==> abs x = y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; PRIME_IMP_NZ; LE_1] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[] THEN EQ_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k = SUC(k - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[EXP; DIVIDES_RMUL; DIVIDES_REFL]]]);;
```

### Informal statement
For all positive integers $d \geq 1$, the following inequality holds:
$$\left\|\sum_{n=1}^{x} (\chi_0(d,n) - 1) \cdot \frac{\Lambda(n)}{n}\right\| \leq \sum_{p \in P} \log(p)$$

where:
- $P = \{p \mid p \text{ is prime and } p \text{ divides } d\}$
- $\chi_0(d,n)$ is the principal character, defined as $1$ if $n$ is coprime to $d$ and $0$ otherwise
- $\Lambda(n)$ is the von Mangoldt function
- $\|\cdot\|$ denotes the complex norm

### Informal proof
The proof establishes the inequality by bounding the left-hand side with a more manageable expression.

We first introduce an intermediate bound:
$$\sum_{p \in P} \sum_{k \geq 1, p^k \leq x} \frac{\log(p)}{p^k}$$

The proof proceeds in two main steps:

1. First, we show that this intermediate expression is bounded by the right-hand side:
   
   For each prime $p$ that divides $d$, we need to show:
   $$\sum_{k \geq 1, p^k \leq x} \frac{\log(p)}{p^k} \leq \log(p)$$
   
   This is proven by:
   - Using the fact that $\sum_{k=1}^{x} \frac{\log(p)}{p^k} \geq \sum_{k \geq 1, p^k \leq x} \frac{\log(p)}{p^k}$ since the latter sum is restricted to values where $p^k \leq x$
   - For each prime $p$ dividing $d$, we have $p \geq 2$ and therefore $p > 1$
   - Using the formula for the sum of a geometric series: $\sum_{k=1}^{\infty} \frac{1}{p^k} = \frac{1}{p-1}$
   - Since $p \geq 2$, we have $\frac{1}{p-1} \leq 1$, thus $\log(p) \cdot \frac{1}{p-1} \leq \log(p)$

2. Second, we show that the left-hand side is bounded by the intermediate expression:
   
   We use the triangle inequality on the complex norm and analyze when the expression $(\chi_0(d,n) - 1) \cdot \frac{\Lambda(n)}{n}$ is non-zero:
   - The term is non-zero when $\chi_0(d,n) \neq 1$ (i.e., when $n$ is not coprime to $d$) and $\Lambda(n) \neq 0$
   - The von Mangoldt function $\Lambda(n)$ is non-zero only when $n = p^k$ for some prime $p$ and integer $k \geq 1$, in which case $\Lambda(p^k) = \log(p)$
   - When $n = p^k$ is not coprime to $d$, this means $p$ divides $d$
   
   Thus, the non-zero terms in the sum correspond exactly to pairs $(p,k)$ where $p$ is a prime dividing $d$ and $p^k \leq x$, and each such term contributes $\frac{\log(p)}{p^k}$ to the sum.

By combining these two steps, we establish the desired inequality.

### Mathematical insight
This lemma bounds the difference between the sum involving the principal character and the corresponding sum for the trivial character, weighted by the von Mangoldt function. It's a key component in the analytic treatment of Dirichlet's theorem on primes in arithmetic progressions.

The result isolates the contribution from prime divisors of the modulus $d$, showing that the principal character behaves almost like the trivial character except for terms related to the prime factorization of $d$. This is important because it helps separate the "main term" from the "error term" in the analysis of Dirichlet's L-functions.

The bound is tight and directly relates to the logarithm of the modulus $d$, as the sum on the right is essentially $\log(d)$ by the properties of the logarithm.

### Dependencies
- `chi_0`: Definition of the principal character
- `LOG_POS`: Theorem that if $x \geq 1$ then $\log(x) \geq 0$
- `LOG_POS_LT`: Theorem that if $x > 1$ then $\log(x) > 0$

### Porting notes
When porting this theorem:
1. Ensure that the von Mangoldt function is defined correctly: $\Lambda(n) = \log(p)$ if $n = p^k$ for a prime $p$ and $k \geq 1$, and $\Lambda(n) = 0$ otherwise
2. The principal character $\chi_0$ should be defined as a complex-valued function that takes 1 when inputs are coprime and 0 otherwise
3. The proof relies heavily on properties of the logarithm, geometric series, and basic number theory results about prime powers and divisibility

---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL = prove
 (`!d. 1 <= d
       ==> bounded { vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) -
                     Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bounded; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  EXISTS_TAC
   `abs(sum {p | prime p /\ p divides d} (\p. log(&p))) +
    abs(log(&0)) + &21` THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; ARITH; VECTOR_SUB_LZERO] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b ==> x <= a + abs y + b`) THEN
  MATCH_MP_TAC(NORM_ARITH
   `!s'. norm(s') <= p /\ norm(s - s' - l) <= &21
        ==> norm(s - l) <= abs p + &21`) THEN
  EXISTS_TAC `vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n))` THEN
  ASM_SIMP_TAC[BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_RING `c * x - (c - Cx(&1)) * x = x`] THEN
  SIMP_TAC[GSYM CX_SUB; VSUM_CX; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC MERTENS_LEMMA THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For any integer $d \geq 1$, the set
$$\left\{\sum_{n=1}^x \chi_0(d,n) \cdot \frac{\Lambda(n)}{n} - \log(x) \,\middle|\, x \in \mathbb{N}\right\}$$
is bounded, where:
- $\chi_0(d,n)$ is the principal Dirichlet character modulo $d$, which equals 1 if $n$ and $d$ are coprime, and 0 otherwise
- $\Lambda(n)$ is the von Mangoldt function
- The sum is taken over all integers from 1 to $x$

### Informal proof
Let's prove that for any $d \geq 1$, the set of sums described in the theorem is bounded.

By the definition of boundedness, we need to show there exists a constant $M$ such that the norm of each element in the set is at most $M$. We choose 
$$M = \left|\sum_{p \mid d, p \text{ prime}} \log p\right| + |\log(0)| + 21$$

For the case where $x = 0$, the sum is empty so the expression simplifies to $-\log(0)$, and its norm satisfies our bound trivially.

For $x > 0$, we apply a triangle inequality approach. We introduce an auxiliary sum:
$$s' = \sum_{n=1}^x (\chi_0(d,n) - 1) \cdot \frac{\Lambda(n)}{n}$$

By `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA`, we know that 
$$\|s'\| \leq \sum_{p \mid d, p \text{ prime}} \log p$$

We also need to show that $\|s - s' - \log(x)\| \leq 21$, where $s$ is our original sum. Note that:
$$s - s' = \sum_{n=1}^x \frac{\Lambda(n)}{n}$$

This is because the difference between $\chi_0(d,n)$ and $(\chi_0(d,n) - 1)$ is just the constant 1.

By Mertens' lemma (`MERTENS_LEMMA`), we know that for $x > 0$:
$$\left|\sum_{n=1}^x \frac{\Lambda(n)}{n} - \log(x)\right| \leq 21$$

Combining these results through the triangle inequality:
$$\|s - \log(x)\| \leq \|s'\| + \|s - s' - \log(x)\| \leq \left|\sum_{p \mid d, p \text{ prime}} \log p\right| + 21$$

Therefore, the set is bounded by the constant $M$ as defined above.

### Mathematical insight
This theorem establishes a key bound related to the distribution of the von Mangoldt function $\Lambda(n)$ when weighted by the principal character modulo $d$. In analytic number theory, this type of result is crucial for understanding the distribution of primes in arithmetic progressions.

The result shows that the weighted sum of the von Mangoldt function, adjusted by $\log(x)$, remains bounded regardless of how large $x$ becomes. This is a partial step toward the Prime Number Theorem for arithmetic progressions, which characterizes the asymptotic distribution of primes in different congruence classes.

The theorem combines character theory (through the principal character $\chi_0$) with estimates on the von Mangoldt function. The fact that the bound depends on the prime divisors of $d$ highlights how the arithmetic structure of the modulus affects the distribution of the related primes.

### Dependencies
- **Theorems**:
  - `MERTENS_LEMMA`: States that for $n \neq 0$, $|\sum_{d=1}^n \frac{\Lambda(d)}{d} - \log(n)| \leq 21$
  - `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA`: States that for $d \geq 1$, the norm of the sum $\sum_{n=1}^x (\chi_0(d,n) - 1) \cdot \frac{\Lambda(n)}{n}$ is bounded by $\sum_{p|d, \text{p prime}} \log(p)$

- **Definitions**:
  - `chi_0`: The principal character modulo $d$, defined as $\chi_0(d,n) = 1$ if $\gcd(n,d) = 1$, and 0 otherwise

### Porting notes
When implementing this in other systems:
1. Ensure the von Mangoldt function $\Lambda$ is properly defined
2. The principal character $\chi_0$ should be implemented using the coprime relation
3. Be careful with the handling of $\log(0)$ which is undefined in the standard sense but appears in the bound
4. The constant 21 in Mertens' lemma is a specific numerical bound that should be preserved
5. Some systems might require more explicit handling of complex numbers and norms than HOL Light does

---

## SUM_OF_NUMBERS

### SUM_OF_NUMBERS
- `SUM_OF_NUMBERS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_OF_NUMBERS = prove
 (`!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
The theorem states that for any natural number $n$, the sum of all integers from $0$ to $n$ equals $\frac{n(n+1)}{2}$.

Formally, $\forall n. \sum_{i=0}^{n} i = \frac{n(n+1)}{2}$

### Informal proof
This theorem is proved using mathematical induction on $n$:

- **Base case**: When $n = 0$, we need to show that $\sum_{i=0}^{0} i = \frac{0 \cdot (0+1)}{2}$.
  The left side equals $0$, and the right side equals $\frac{0 \cdot 1}{2} = 0$, so the base case holds.

- **Inductive step**: Assuming the formula holds for some $n$, we need to prove it for $n+1$.
  
  $\sum_{i=0}^{n+1} i = \sum_{i=0}^{n} i + (n+1) = \frac{n(n+1)}{2} + (n+1)$
  
  Using algebra:
  $\frac{n(n+1)}{2} + (n+1) = \frac{n(n+1) + 2(n+1)}{2} = \frac{(n+1)(n+2)}{2} = \frac{(n+1)((n+1)+1)}{2}$
  
  This completes the induction.

The proof in HOL Light uses `INDUCT_TAC` to set up the induction, `ASM_REWRITE_TAC` with the `NSUM_CLAUSES_NUMSEG` theorem to handle the summation, and `ARITH_TAC` to verify the arithmetic for both the base case and inductive step.

### Mathematical insight
This theorem provides the well-known formula for the sum of the first $n$ natural numbers, often attributed to Gauss. It's a fundamental result in discrete mathematics and number theory, frequently used in algorithm analysis, combinatorics, and probability theory.

The formula can be intuitively understood by pairing the numbers in the series: $(0 + n), (1 + (n-1)), (2 + (n-2)), ...$. Each pair sums to $n$, and there are $(n+1)/2$ such pairs, giving us $n(n+1)/2$.

### Dependencies
- `INDUCT_TAC`: tactic for mathematical induction
- `ASM_REWRITE_TAC`: rewriting tactic using assumptions
- `NSUM_CLAUSES_NUMSEG`: theorem for handling summations over integer ranges
- `ARITH_TAC`: tactic for solving arithmetic goals

### Porting notes
When porting to other proof assistants:
- The summation notation might differ between systems
- The division operation (`DIV`) in HOL Light represents integer division - ensure your target system handles this appropriately
- Make sure your induction principle is properly set up for natural numbers

---

## PRODUCT_POW_NSUM

### Name of formal statement
PRODUCT_POW_NSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRODUCT_POW_NSUM = prove
 (`!s. FINITE s ==> product s (\i. z pow (f i)) = z pow (nsum s f)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NSUM_CLAUSES; real_pow; REAL_POW_ADD]);;
```

### Informal statement
For any finite set $s$, the product of $z^{f(i)}$ over all $i \in s$ is equal to $z$ raised to the power of the sum of $f(i)$ over all $i \in s$. Formally:

$$\forall s. \text{FINITE}(s) \implies \prod_{i \in s} z^{f(i)} = z^{\sum_{i \in s} f(i)}$$

This theorem expresses the familiar exponent law that $(z^a)(z^b) = z^{a+b}$ generalized to products over finite sets.

### Informal proof
This theorem is proven by mathematical induction on finite sets.

* Base case: For the empty set, both the product of $z^{f(i)}$ and $z$ raised to the sum of $f(i)$ evaluate to $1$ (since an empty product is $1$ by definition and an empty sum is $0$, with $z^0 = 1$).

* Inductive step: Assume the property holds for a finite set $s$, and consider $s \cup \{x\}$ where $x \notin s$. Then:
  $$\prod_{i \in s \cup \{x\}} z^{f(i)} = \left(\prod_{i \in s} z^{f(i)}\right) \cdot z^{f(x)} = z^{\sum_{i \in s} f(i)} \cdot z^{f(x)} = z^{\sum_{i \in s} f(i) + f(x)} = z^{\sum_{i \in s \cup \{x\}} f(i)}$$

The proof uses:
- Strong induction on finite sets (`FINITE_INDUCT_STRONG`)
- Properties of products over sets (`PRODUCT_CLAUSES`)
- Properties of sums over sets (`NSUM_CLAUSES`)
- The definition of real exponentiation (`real_pow`)
- The exponent addition law (`REAL_POW_ADD`): $z^a \cdot z^b = z^{a+b}$

### Mathematical insight
This theorem represents a fundamental property that connects products of powers to powers of sums, which is a generalization of the familiar exponent law. It's particularly useful in simplifying expressions involving products of powers with the same base.

The proof illustrates the power of induction on finite sets: starting with the base case of an empty set, we incrementally build up to arbitrary finite sets by adding one element at a time and applying the basic exponent addition law.

This result is often used as a stepping stone in more complex proofs about sums and products, especially in combinatorial contexts or when dealing with probability distributions.

### Dependencies
- Theorems:
  - `FINITE_INDUCT_STRONG`: Principle of strong induction for finite sets
  - `PRODUCT_CLAUSES`: Basic properties of the product operator over sets
  - `NSUM_CLAUSES`: Basic properties of the numeric sum operator over sets
  - `REAL_POW_ADD`: The exponent addition law for real powers: $x^a \cdot x^b = x^{a+b}$
- Definitions:
  - `real_pow`: Definition of real exponentiation

### Porting notes
When porting this theorem:
- Ensure that your target system's definition of products and sums over sets aligns with HOL Light's behavior for empty sets
- Verify that the exponentiation operation in your target system follows the same laws
- The proof is quite straightforward, primarily relying on standard algebraic properties, so it should translate smoothly to most systems

---

## PRODUCT_SPECIAL

### PRODUCT_SPECIAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRODUCT_SPECIAL = prove
 (`!z i. product (0..n) (\i. z pow i) = z pow ((n * (n + 1)) DIV 2)`,
  SIMP_TAC[PRODUCT_POW_NSUM; FINITE_NUMSEG; SUM_OF_NUMBERS]);;
```

### Informal statement
For all real numbers $z$ and non-negative integers $n$:
$$\prod_{i=0}^{n} z^i = z^{\frac{n(n+1)}{2}}$$

This theorem states that the product of powers of $z$ with exponents ranging from $0$ to $n$ equals $z$ raised to the power of the sum of all integers from $0$ to $n$, which is $\frac{n(n+1)}{2}$.

### Informal proof
The proof follows from applying two key theorems:

1. First, we use `PRODUCT_POW_NSUM`, which states that for a finite set $s$, the product of $z$ raised to various powers equals $z$ raised to the sum of those powers:
   $$\prod_{i \in s} z^{f(i)} = z^{\sum_{i \in s} f(i)}$$

2. Then we use `SUM_OF_NUMBERS`, which gives us the closed formula for the sum of consecutive integers from $0$ to $n$:
   $$\sum_{i=0}^{n} i = \frac{n(n+1)}{2}$$

By applying these two theorems and noting that the range $0..n$ is a finite set, we obtain:
$$\prod_{i=0}^{n} z^i = z^{\sum_{i=0}^{n} i} = z^{\frac{n(n+1)}{2}}$$

### Mathematical insight
This theorem provides a closed-form expression for the product of powers with consecutive exponents. It is particularly useful in combinatorial calculations and generating functions.

The result can be seen as an application of the general principle that exponents add when multiplying powers with the same base. When we organize this addition of exponents systematically, we get the arithmetic sequence sum formula.

This theorem is related to the concept of triangular numbers, as $\frac{n(n+1)}{2}$ represents the $n$-th triangular number, which is the sum of the first $n$ natural numbers.

### Dependencies
- `PRODUCT_POW_NSUM`: For any finite set $s$, $\prod_{i \in s} z^{f(i)} = z^{\sum_{i \in s} f(i)}$
- `SUM_OF_NUMBERS`: $\sum_{i=0}^{n} i = \frac{n(n+1)}{2}$
- `FINITE_NUMSEG`: The range $0..n$ is a finite set

### Porting notes
When porting this theorem to other systems, ensure that:
- The system has a well-defined notion of finite products over ranges
- The power function is properly defined for the number type being used
- Integer division (DIV) is appropriately translated if the target system uses a different notation for division or floor division

---

## AGM_SPECIAL

### Name of formal statement
AGM_SPECIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AGM_SPECIAL = prove
 (`!n t. &0 <= t
         ==> (&n + &1) pow 2 * t pow n <= (sum(0..n) (\k. t pow k)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n + 1`; `\k. (t:real) pow (k - 1)`] AGM) THEN
  ASM_SIMP_TAC[REAL_POW_LE; ARITH_RULE `1 <= n + 1`] THEN
  SUBGOAL_THEN `1..n+1 = 0+1..n+1` SUBST1_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; PRODUCT_OFFSET; ADD_SUB] THEN
  REWRITE_TAC[PRODUCT_SPECIAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2)) THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN
  ASM_SIMP_TAC[PRODUCT_POS_LE_NUMSEG; REAL_POW_LE] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SUBGOAL_THEN `2 * (n * (n + 1)) DIV 2 = n * (n + 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
     [REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN CONV_TAC TAUT;
      SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH]];
    REWRITE_TAC[GSYM REAL_POW_POW] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2_REV)) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_RDIV_EQ; REAL_POW_LT;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;
```

### Informal statement
For all natural numbers $n$ and real numbers $t$ such that $t \geq 0$, we have:
$$(n + 1)^2 \cdot t^n \leq \left(\sum_{k=0}^{n} t^k\right)^2$$

### Informal proof
This theorem proves a special case of the arithmetic-geometric mean inequality. The proof proceeds as follows:

- We start by applying the general arithmetic-geometric mean inequality (AGM) to the set of values $\{t^0, t^1, \ldots, t^n\}$.
- First, we invoke the AGM theorem with parameters $n+1$ and the function $k \mapsto t^{k-1}$.
- Since $t \geq 0$, all powers of $t$ are non-negative, satisfying the precondition of AGM.
- We rewrite the range $1..n+1$ as $0+1..n+1$ to utilize summation and product offset properties.
- Apply `SUM_OFFSET` and `PRODUCT_OFFSET` to adjust the indices, then use `PRODUCT_SPECIAL` to simplify the product term.
- The product term becomes $t^{(n \cdot (n+1))/2}$.
- We raise both sides of the inequality to the power of 2.
- We simplify $2 \cdot (n \cdot (n+1)) \text{ DIV } 2$ to $n \cdot (n+1)$ by proving that $n \cdot (n+1)$ is always even:
  - If $n$ is even, then $n \cdot (n+1)$ is even due to $n$ being a factor
  - If $n$ is odd, then $n+1$ is even, thus $n \cdot (n+1)$ is even due to $n+1$ being a factor
- After algebraic manipulations and applying properties of powers, we arrive at the desired inequality $(n+1)^2 \cdot t^n \leq \left(\sum_{k=0}^{n} t^k\right)^2$.

### Mathematical insight
This theorem presents a special case of the arithmetic-geometric mean inequality applied to powers of a non-negative real number. The inequality relates the square of the sum of powers of $t$ to a single power of $t$ multiplied by $(n+1)^2$. This result is particularly useful in analysis involving geometric series and their properties.

The inequality is tight in the sense that equality holds when $t = 1$ (as all terms in the sum become 1). The theorem provides a way to bound powers of a number in terms of sums of powers, which has applications in approximation theory and convergence analysis.

### Dependencies
#### Theorems
- `AGM`: The general arithmetic-geometric mean inequality
- `PRODUCT_POS_LE_NUMSEG`: Positivity of product over a range when function values are non-negative
- `PRODUCT_OFFSET`: Formula for shifting indices in a product
- `PRODUCT_SPECIAL`: Formula for product of powers with specific structure
- `SUM_OFFSET`: Formula for shifting indices in a sum
- `REAL_POW_LE2`: Inequality preservation when raising to an even power
- `REAL_POW_LE2_REV`: Reverse inequality preservation for even powers

### Porting notes
When porting this theorem:
- Ensure that the arithmetic-geometric mean inequality (AGM) is available in your target system
- The proof relies heavily on manipulation of finite sums and products over ranges, so corresponding libraries should be available
- Pay attention to the handling of integer division (`DIV`) and evenness properties, which may have different representations in other systems
- The proof uses multiple arithmetic simplification tactics that may need different approaches in other provers

---

## DIVISORSUM_PRIMEPOW

### DIVISORSUM_PRIMEPOW
- `DIVISORSUM_PRIMEPOW`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIVISORSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> sum {m | m divides (p EXP k)} c = sum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC SUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;
```

### Informal statement
For any function $f$, any prime number $p$, and any natural number $k$:
$$\sum_{m \mid p^k} f(m) = \sum_{i=0}^k f(p^i)$$

This theorem states that the sum of $f(m)$ over all divisors $m$ of $p^k$ equals the sum of $f(p^i)$ for $i$ ranging from $0$ to $k$.

### Informal proof
The proof proceeds as follows:

1. We first note that for a prime number $p$ and natural number $k$, the divisors of $p^k$ are precisely the powers of $p$ from $p^0$ to $p^k$.
   - This uses the fact that if $m$ divides $p^k$, then $m = p^i$ for some $0 \leq i \leq k$ when $p$ is prime.

2. We rewrite the set of divisors:
   $$\{m \mid m \text{ divides } p^k\} = \{p^i \mid 0 \leq i \leq k\}$$

3. This transforms the left-hand sum into a sum over the image of the function $i \mapsto p^i$ applied to the set $\{i \mid 0 \leq i \leq k\}$.

4. We then apply a theorem about sums over image sets to convert this to a sum over the index set $\{0, 1, \ldots, k\}$.

5. The condition that the function $i \mapsto p^i$ is injective on this domain follows from the properties of exponentiation with a prime base.

### Mathematical insight
This theorem provides a simple expression for the sum of a function over all divisors of a prime power. It relies on the fact that the divisor structure of $p^k$ is extremely simple: the only divisors are powers of $p$ up to $p^k$.

This result is useful for many number-theoretic calculations involving sums over divisors, particularly when working with multiplicative functions. It forms the basis for computing various divisor sums for arbitrary natural numbers by using the prime factorization and multiplicative properties.

### Dependencies
- `DIVIDES_PRIMEPOW`: Characterizes the divisors of a prime power
- `SET_RULE`: Used for set-theoretic manipulations
- `SUM_IMAGE`: Relates the sum over an image set to the sum over the original set
- `EQ_EXP`: Relates equality of exponents
- `FINITE_NUMSEG_LE`: States that a numeric segment is finite
- `PRIME_0`, `PRIME_1`: Basic theorems about primality of 0 and 1

### Porting notes
When porting this theorem, be aware that:
- The proof relies on the specific characterization of divisors of prime powers.
- The implementation of sums over sets may differ between proof assistants.
- The notation for sets and set comprehensions may need adjustment.
- Different systems may have different conventions for representing the range of a sum.

---

## DIVISORVSUM_PRIMEPOW

### DIVISORVSUM_PRIMEPOW

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIVISORVSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> vsum {m | m divides (p EXP k)} c = vsum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC VSUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;
```

### Informal statement
For any function $f$, prime number $p$, and natural number $k$, if $p$ is prime, then:
$$\sum_{m \mid p^k} f(m) = \sum_{i=0}^{k} f(p^i)$$

This theorem states that the sum of the function $f$ evaluated at all divisors of $p^k$ equals the sum of the function $f$ evaluated at powers of $p$ from $p^0$ to $p^k$.

### Informal proof
The proof proceeds as follows:

- First, we use the characterization of the divisors of a prime power $p^k$: by `DIVIDES_PRIMEPOW`, all divisors of $p^k$ are exactly the powers $p^i$ where $0 \leq i \leq k$.

- We can rewrite the set of divisors $\{m \mid m \text{ divides } p^k\}$ as $\{p^i \mid 0 \leq i \leq k\}$, or equivalently as the image of the function $i \mapsto p^i$ over the set $\{i \mid 0 \leq i \leq k\}$.

- The sum over this set can be rewritten as a sum over the image of the function $i \mapsto p^i$ applied to the set $\{0, 1, ..., k\}$.

- Using the theorem `VSUM_IMAGE` about summing over image sets, we can transform this into a sum over the range from $0$ to $k$.

- The result follows, noting that the mapping $i \mapsto p^i$ is injective over the range $\{0, 1, ..., k\}$ because $p$ is a prime number (and therefore greater than 1), making different powers of $p$ distinct.

### Mathematical insight
This theorem gives a simplified way to compute sums over the divisors of a prime power. Instead of finding all divisors and then summing the function values, one can simply sum over the powers of the prime from 0 to k. This is particularly useful in number theory for computing number-theoretic functions defined on divisors, such as the sum of divisors function or the number of divisors function.

The result relies on the fact that prime powers have a very simple divisor structure: the divisors of $p^k$ are precisely $1, p, p^2, \ldots, p^k$ (or equivalently, $p^0, p^1, p^2, \ldots, p^k$).

### Dependencies
- `DIVIDES_PRIMEPOW`: Characterizes the divisors of a prime power
- `SET_RULE`: Used to rewrite set comprehensions
- `o_DEF`: Definition of function composition
- `GSYM NUMSEG_LE`: Relates to numeric ranges
- `VSUM_IMAGE`: Theorem about summing over image sets
- `FINITE_NUMSEG_LE`: States that numeric ranges are finite
- `PRIME_0`: States that 0 is not prime
- `PRIME_1`: States that 1 is not prime
- `EQ_EXP`: Relates to equality of exponential expressions

### Porting notes
When porting this theorem:
- Ensure that your target system has a suitable representation of prime numbers and divisibility.
- Verify that your system has a summation operation corresponding to HOL Light's `vsum`.
- The proof relies on set-theoretic manipulations, so you may need to adapt these to match your target system's set theory library.
- The theorem uses the exponentiation operation `EXP` and divisibility relation `divides`, which should have equivalents in most proof assistants.

---

## DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_EQ_1 = prove
 (`!d c p k. dirichlet_character d c /\ prime p /\ p divides d
             ==> vsum {m | m divides (p EXP k)} c = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `vsum {1} c : complex` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[VSUM_SING] THEN ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_SING; IN_ELIM_THM; DIVIDES_1] THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `i:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_REXP] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[COPRIME_SYM; PRIME_COPRIME_EQ]);;
```

### Informal statement
For any modulus $d$, Dirichlet character $c$, prime $p$, and natural number $k$, if $c$ is a Dirichlet character modulo $d$ and $p$ is a prime divisor of $d$, then the sum of the character values over all divisors of $p^k$ equals 1:

$$\forall d, c, p, k.\; \text{dirichlet\_character}(d, c) \wedge \text{prime}(p) \wedge p \mid d \implies \sum_{m \mid p^k} c(m) = 1$$

### Informal proof
We prove that the sum of character values over all divisors of $p^k$ equals $c(1)$, which is 1 for any Dirichlet character.

First, we establish that $\sum_{m \mid p^k} c(m) = \sum_{m \in \{1\}} c(m)$, which is just $c(1)$:

- We use the fact that for any divisor $m$ of $p^k$ except 1, the character value $c(m)$ equals 0.
- This is because any divisor $m \neq 1$ of $p^k$ must be of the form $p^i$ for some $i > 0$.
- Since $p$ divides $d$, we have that $\gcd(p^i, d) \neq 1$.
- By the definition of a Dirichlet character, $c(m) = 0$ whenever $m$ is not coprime to $d$.
- Therefore, the only non-zero term in the sum is $c(1)$.

Then, by the properties of Dirichlet characters, specifically `DIRICHLET_CHARACTER_EQ_1`, we know that $c(1) = 1$.

Therefore, $\sum_{m \mid p^k} c(m) = c(1) = 1$.

### Mathematical insight
This theorem establishes a fundamental property of Dirichlet characters when evaluated on divisors of prime powers $p^k$ where the prime $p$ divides the modulus $d$. It shows that in such cases, the sum collapses to exactly 1.

This result is important in analytic number theory, particularly when studying Dirichlet L-functions and their properties. The theorem captures how Dirichlet characters behave on sets of divisors under specific conditions, which is crucial for various applications in multiplicative number theory.

The key insight is that when $p|d$, all divisors of $p^k$ except 1 are not coprime to $d$, so their character values are 0, leaving only $c(1) = 1$ in the sum.

### Dependencies
#### Theorems
- `DIRICHLET_CHARACTER_EQ_0`: Establishes that $c(n) = 0$ if and only if $n$ is not coprime to $d$.
- `DIRICHLET_CHARACTER_EQ_1`: Shows that $c(1) = 1$ for any Dirichlet character.

#### Definitions
- `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function $c$ satisfying periodicity ($c(n+d) = c(n)$), character values are 0 precisely when not coprime to modulus, and multiplicativity ($c(mn) = c(m)c(n)$).

### Porting notes
When porting this theorem:
- Ensure that the Dirichlet character is properly defined with all three key properties.
- Pay attention to how divisibility and coprimality are formalized in the target system.
- The proof relies on properties of prime numbers and divisibility, which should be available in most systems but might have different names.
- The handling of complex numbers might differ between systems.

---

## DIRICHLET_CHARACTER_REAL_CASES

### Name of formal statement
DIRICHLET_CHARACTER_REAL_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_REAL_CASES = prove
 (`!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> !n. c n = --Cx(&1) \/ c n = Cx(&0) \/ c n = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIRICHLET_CHARACTER_NORM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[REAL_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any modulus $d$ and function $c: \mathbb{N} \rightarrow \mathbb{C}$, if $c$ is a Dirichlet character modulo $d$ and $c(n)$ is real for all $n$, then for all $n$, we have $c(n) = -1$ or $c(n) = 0$ or $c(n) = 1$.

### Informal proof
The proof shows that a real-valued Dirichlet character can only take values from $\{-1, 0, 1\}$.

We start with an arbitrary modulus $d$, a Dirichlet character $c$ modulo $d$, and the condition that $c(n)$ is real for all $n$.

For any natural number $n$, we apply the theorem `DIRICHLET_CHARACTER_NORM` which tells us that:
- $\|c(n)\| = 1$ if $\gcd(d, n) = 1$
- $\|c(n)\| = 0$ if $\gcd(d, n) \neq 1$

Since $c(n)$ is real, we can write $c(n) = t$ for some real number $t$.

When we calculate the complex norm of this value:
- If $\|c(n)\| = 0$, then $c(n) = 0$
- If $\|c(n)\| = 1$, then $|t| = 1$, meaning $t = 1$ or $t = -1$

Therefore, $c(n)$ must be either $-1$, $0$, or $1$.

### Mathematical insight
This theorem characterizes real-valued Dirichlet characters by showing they can only take three possible values: $-1$, $0$, and $1$. This is a fundamental property that distinguishes real Dirichlet characters from complex-valued ones, which can take values on the entire unit circle.

The result follows from the general property that Dirichlet characters have values either equal to 0 (when $\gcd(n,d) \neq 1$) or with norm equal to 1 (when $\gcd(n,d) = 1$). When restricted to real values, this constrains the character values to $\{-1, 0, 1\}$.

This property is important for classification of Dirichlet characters and simplifies many calculations involving real Dirichlet characters.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_NORM`: States that the norm of a Dirichlet character $c(n)$ equals 1 if $n$ is coprime to $d$, and 0 otherwise.

- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character modulo $d$ as a function $c$ satisfying:
    - $c(n + d) = c(n)$ for all $n$ (periodic with period $d$)
    - $c(n) = 0$ if and only if $\gcd(n,d) \neq 1$
    - $c(m \cdot n) = c(m) \cdot c(n)$ for all $m, n$ (multiplicative)

### Porting notes
When porting this theorem:
- Ensure the definition of Dirichlet character matches HOL Light's definition
- The proof relies on properties of complex norms and real numbers, which should be available in most proof assistants
- Some systems may need explicit handling of complex numbers versus reals, particularly for the step where we deduce that a real number with absolute value 1 must be either 1 or -1

---

## DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS = prove
 (`!d c p k. dirichlet_character d c /\ (!n. real(c n)) /\ prime p
             ==> &0 <= Re(vsum {m | m divides (p EXP k)} c)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RE_VSUM; FINITE_DIVISORS; EXP_EQ_0; PRIME_IMP_NZ] THEN
  ASM_SIMP_TAC[DIVISORSUM_PRIMEPOW] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_POW th]) THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_REAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CX_POW; RE_CX; SUM_POS_LE_NUMSEG;
               REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(s = if EVEN k then &1 else &0) ==> &0 <= s`) THEN
  SPEC_TAC(`k:num`,`r:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[EVEN; SUM_CLAUSES_NUMSEG] THEN
  ASM_REWRITE_TAC[complex_pow; RE_CX; LE_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_POW_NEG; COMPLEX_POW_ONE; COMPLEX_MUL_LNEG;
                  COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG; COMPLEX_MUL_LID;
                  RE_NEG; RE_CX] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any modulus $d$, Dirichlet character $c$, prime number $p$, and positive integer $k$, if $c$ is real-valued (i.e., $\forall n. \text{real}(c(n))$), then the real part of the sum of the character values over all divisors of $p^k$ is non-negative:

$$\forall d, c, p, k. \text{dirichlet\_character}(d, c) \wedge (\forall n. \text{real}(c(n))) \wedge \text{prime}(p) \Rightarrow 0 \leq \text{Re}\left(\sum_{m \mid p^k} c(m)\right)$$

### Informal proof
We prove that the real part of the sum of character values over divisors of a prime power is non-negative.

* First, we use the fact that the real part of a sum is the sum of the real parts: $\text{Re}(\sum_{m \mid p^k} c(m)) = \sum_{m \mid p^k} \text{Re}(c(m))$.

* By `DIVISORSUM_PRIMEPOW`, we know that for a prime $p$, the sum over divisors of $p^k$ can be rewritten as a sum over powers of $p$:
  $$\sum_{m \mid p^k} c(m) = \sum_{i=0}^k c(p^i)$$

* For a Dirichlet character, we know $c(p^i) = c(p)^i$ by the multiplicative property (using `DIRICHLET_CHARACTER_POW`).

* Since $c$ is real-valued, by `DIRICHLET_CHARACTER_REAL_CASES`, we know that $c(p)$ must be one of three values: $-1$, $0$, or $1$.

* If $c(p) = 0$, then all terms in the sum except possibly $c(1) = 1$ are zero, so the sum is non-negative.

* If $c(p) = 1$, then all terms in the sum are $1$, which gives a positive sum.

* If $c(p) = -1$, then the sum becomes:
  $$\sum_{i=0}^k (-1)^i = \begin{cases} 
  1 & \text{if $k$ is even} \\
  0 & \text{if $k$ is odd}
  \end{cases}$$

* Therefore, in all cases, the sum is non-negative.

### Mathematical insight
This theorem establishes a non-negativity property for sums of real-valued Dirichlet characters over divisors of prime powers. This is important in analytic number theory, especially when studying properties of Dirichlet L-functions. 

The key insight is that the behavior of Dirichlet characters on prime powers is fully determined by their values at the prime, and for real-valued characters, these values are restricted to $\{-1, 0, 1\}$. When summing over all divisors of a prime power, even for characters that can take negative values, the sum remains non-negative due to the pattern of alternating signs when $c(p) = -1$.

This property is useful in establishing bounds and convergence results for Dirichlet series and in various applications related to the distribution of primes in arithmetic progressions.

### Dependencies
- Theorems:
  - `DIRICHLET_CHARACTER_POW`: For any Dirichlet character $c$, $c(m^n) = c(m)^n$.
  - `DIVISORSUM_PRIMEPOW`: For a prime $p$, the sum over divisors of $p^k$ equals the sum over powers of $p$ up to $k$.
  - `DIRICHLET_CHARACTER_REAL_CASES`: A real-valued Dirichlet character can only take values $-1$, $0$, or $1$.
- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character with modulus $d$ as a function satisfying periodicity, being zero exactly when not coprime to $d$, and multiplicativity.

### Porting notes
When porting this theorem:
1. Ensure that the definition of Dirichlet character is consistent with the standard mathematical definition.
2. The proof relies on specific lemmas about Dirichlet characters that should be ported first.
3. The sum over divisors might be represented differently in other proof assistants, so adjust accordingly.
4. The handling of the case analysis on the values of $c(p)$ and the parity of $k$ should be carefully implemented.

---

## DIRICHLET_CHARACTER_DIVISORSUM_POS

### DIRICHLET_CHARACTER_DIVISORSUM_POS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_POS = prove
 (`!d c n. dirichlet_character d c /\ (!n. real(c n)) /\ ~(n = 0)
           ==> &0 <= Re(vsum {m | m divides n} c)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 1 < n`))
  THENL
   [ASM_SIMP_TAC[DIVIDES_ONE; SING_GSPEC; VSUM_SING] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL_POS];
    ALL_TAC] THEN
  UNDISCH_TAC `1 < n` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS]] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m:num. Re(c m)` REAL_MULTIPLICATIVE_DIVISORSUM) THEN
  REWRITE_TAC[real_multiplicative] THEN ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL; CX_MUL];
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `b:num`] o CONJUNCT2) THEN
  ASM_SIMP_TAC[GSYM RE_VSUM; FINITE_DIVISORS; MULT_EQ_0;
               ARITH_RULE `1 < n ==> ~(n = 0)`; REAL_LE_MUL]]);;
```

### Informal statement
For any Dirichlet character $c$ modulo $d$ that is real-valued and any positive integer $n$, the sum of the character over all divisors of $n$ has non-negative real part:

$$\forall d, c, n. \text{dirichlet\_character}(d, c) \wedge (\forall n. \text{real}(c(n))) \wedge n \neq 0 \Rightarrow 0 \leq \text{Re}\left(\sum_{m \mid n} c(m)\right)$$

### Informal proof
We proceed by cases on the value of $n$.

1. First, if $n = 1$:
   - For $n = 1$, the only divisor is 1 itself
   - Therefore, $\sum_{m \mid 1} c(m) = c(1)$
   - By the property of a Dirichlet character, $c(1) = 1$ (complex)
   - So $\text{Re}(c(1)) = 1 \geq 0$

2. If $n > 1$:
   - We use strong induction on coprime factors
   - For the base case, we rely on the theorem `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS`, which states that for prime powers $p^k$, the sum of a real-valued Dirichlet character over the divisors has non-negative real part
   
   - For the inductive step, suppose $n = a \cdot b$ where $\gcd(a,b) = 1$:
     - From `REAL_MULTIPLICATIVE_DIVISORSUM`, we know that for a real multiplicative function $f$, the sum over divisors $\sum_{m \mid n} f(m)$ is also multiplicative
     - We apply this to the function $\text{Re}(c(m))$, which is real multiplicative because:
       * $\text{Re}(c(1)) = \text{Re}(1) = 1$
       * For coprime $m,n$: $\text{Re}(c(m \cdot n)) = \text{Re}(c(m) \cdot c(n)) = \text{Re}(c(m)) \cdot \text{Re}(c(n))$
         (since $c$ is multiplicative and real-valued)
     - Therefore, $\text{Re}(\sum_{m \mid a \cdot b} c(m)) = \text{Re}(\sum_{m \mid a} c(m)) \cdot \text{Re}(\sum_{m \mid b} c(m))$
     - By the induction hypothesis, both factors are non-negative
     - The product of non-negative numbers is non-negative, which completes the proof

### Mathematical insight
This theorem establishes an important non-negativity property for sums of Dirichlet characters over divisors of integers. It's a key result in analytic number theory with applications in the study of Dirichlet L-functions and character sums.

The proof relies on the multiplicative structure of Dirichlet characters and divisor sums. When a function is multiplicative, the sum over divisors inherits this multiplicative property for coprime arguments. This allows us to decompose the problem into more manageable pieces (prime powers).

The result is particularly useful in applications where positivity or non-negativity is crucial, such as certain convergence arguments involving Dirichlet series.

### Dependencies
- **Theorems:**
  - `REAL_MULTIPLICATIVE_DIVISORSUM`: If $f$ is real multiplicative, then so is the function $n \mapsto \sum_{d \mid n} f(d)$
  - `DIRICHLET_CHARACTER_MUL`: For a Dirichlet character $c$ modulo $d$, we have $c(m \cdot n) = c(m) \cdot c(n)$
  - `DIRICHLET_CHARACTER_EQ_1`: For any Dirichlet character $c$, we have $c(1) = 1$
  - `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS`: For a real-valued Dirichlet character $c$ and prime power $p^k$, the sum $\sum_{m \mid p^k} c(m)$ has non-negative real part

- **Definitions:**
  - `real_multiplicative`: A function $f: \mathbb{N} \to \mathbb{R}$ is multiplicative if $f(1) = 1$ and $f(m \cdot n) = f(m) \cdot f(n)$ whenever $\gcd(m,n) = 1$
  - `dirichlet_character`: A function $c: \mathbb{N} \to \mathbb{C}$ is a Dirichlet character modulo $d$ if it's periodic with period $d$, is zero exactly when $\gcd(n,d) > 1$, and is multiplicative

### Porting notes
When porting this theorem:
1. Ensure that your system has a proper definition of Dirichlet characters with the three key properties (periodicity, value at non-coprime arguments, and multiplicativity)
2. The proof relies on strong induction on coprime factors, which might require custom induction principles in some proof assistants
3. Be careful with the handling of sums over divisors, as different systems may have different notation or library support for such sums
4. The real part of complex numbers may be treated differently across systems

---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma = prove
 (`!x n. &0 <= x /\ x <= &1 ==> &1 - &n * x <= (&1 - x) pow n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - x) * (&1 - &n * x)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_SUB_LE; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= n * x * x ==> &1 - (n + &1) * x <= (&1 - x) * (&1 - n * x)`) THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_SQUARE]);;
```

### Informal statement
For all real numbers $x$ and natural numbers $n$, if $0 \leq x \leq 1$, then $1 - nx \leq (1 - x)^n$.

### Informal proof
The proof proceeds by induction on the natural number $n$.

**Base case:** When $n = 0$, we have $1 - 0 \cdot x \leq (1 - x)^0$, which simplifies to $1 \leq 1$. This is trivially true by arithmetic reasoning.

**Inductive step:** Assume the statement holds for some $n$, i.e., $1 - nx \leq (1 - x)^n$ when $0 \leq x \leq 1$.

We need to prove that $1 - (n+1)x \leq (1 - x)^{n+1}$.

Since $(1 - x)^{n+1} = (1 - x) \cdot (1 - x)^n$, we establish a transitive chain:
1. We claim that $1 - (n+1)x \leq (1 - x) \cdot (1 - nx)$
   - This is justified by algebraic manipulation: $(1 - x) \cdot (1 - nx) = 1 - x - nx + nx^2 = 1 - (n+1)x + nx^2$
   - Since $0 \leq nx^2$ (as both $n$ and $x^2$ are non-negative), we have $1 - (n+1)x \leq 1 - (n+1)x + nx^2 = (1 - x) \cdot (1 - nx)$
2. By the induction hypothesis, $(1 - nx) \leq (1 - x)^n$
3. Since $0 \leq x \leq 1$, we have $0 \leq 1 - x$, so $(1 - x) \cdot (1 - nx) \leq (1 - x) \cdot (1 - x)^n = (1 - x)^{n+1}$

By transitivity of $\leq$, we obtain $1 - (n+1)x \leq (1 - x)^{n+1}$, as required.

### Mathematical insight
This lemma establishes an inequality between the linear expression $1 - nx$ and the power $(1 - x)^n$ within the unit interval. Such inequalities are often useful in analysis, particularly when studying rates of convergence or providing bounds for sequences and series. 

The result can be interpreted as showing that $(1 - x)^n$ decreases more slowly than the linear function $1 - nx$ as $n$ increases, for any fixed $x$ in $[0,1]$.

This type of inequality is commonly used in probability theory, numerical analysis, and approximation theory.

### Dependencies
No explicit dependencies were provided, but the proof uses:
- Standard arithmetic operations and reasoning about real numbers
- Basic properties of powers of real numbers
- Induction on natural numbers

### Porting notes
When porting this theorem:
- The proof relies on arithmetic reasoning that should be straightforward in most systems
- The main challenge might be handling the notation for real numbers (HOL Light uses `&n` for numeric conversions)
- The induction principle used is standard induction on natural numbers
- The transitive reasoning pattern is common across most proof assistants

---

## LFUNCTION_NONZERO_REAL

### LFUNCTION_NONZERO_REAL

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LFUNCTION_NONZERO_REAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> ~(Lfunction c = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
   DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. norm(z) < &1
        ==> summable (from 1) (\n. c(n) * z pow n / (Cx(&1) - z pow n))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
     [MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `2` THEN
      MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC `\n:num. Cx(&0)` THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; SUMMABLE_0] THEN
      ASM_SIMP_TAC[COMPLEX_VEC_0; COMPLEX_POW_ZERO; IN_FROM;
                   ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\n. Cx(&2 * norm(z:complex) pow n)` THEN
    REWRITE_TAC[REAL_CX; RE_CX] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; NORM_POS_LE] THEN
    ASM_SIMP_TAC[CX_MUL; CX_POW; SUMMABLE_COMPLEX_LMUL; COMPLEX_NORM_CX;
                 REAL_ABS_NORM; SUMMABLE_GP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ABS_POS; REAL_LE_MUL] THEN
    REWRITE_TAC[TAUT `(p ==> (if q then x else T)) <=> p /\ q ==> x`] THEN
    MP_TAC(SPECL [`norm(z:complex)`; `&1 / &2`] REAL_ARCH_POW_INV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; REAL_ABS_NUM; REAL_ABS_POW] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN
    SUBST1_TAC(REAL_ARITH `&2 = inv(&1 / &2)`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(z) <= norm(w) - h ==> h <= norm(w - z)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:complex) pow N` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[summable; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:complex->complex` (LABEL_TAC "+")) THEN
  ABBREV_TAC `b = \z n. inv(Cx(&n) * (Cx(&1) - z)) -
                        z pow n / (Cx(&1) - z pow n)` THEN
  SUBGOAL_THEN
   `!z:complex. norm(z) < &1 ==> ((\n. c(n) * b z n) sums --(f z)) (from 1)`
   (LABEL_TAC "*")
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_SUB_LZERO] THEN
    MATCH_MP_TAC SERIES_SUB THEN ASM_SIMP_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    REWRITE_TAC[COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    SUBST1_TAC(COMPLEX_RING `Cx(&0) = Cx(&0) * inv(Cx(&1) - z)`) THEN
    MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION) THEN
    ASM_REWRITE_TAC[complex_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. norm(z) < &1
                    ==> ((\n. vsum {d | d divides n} (\d. c d) * z pow n) sums
                         f(z)) (from 1)`
  (LABEL_TAC "+") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS; LE_1] THEN
    REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN
    REWRITE_TAC[VSUM_GP; ARITH_RULE `n < 1 <=> n = 0`] THEN
    SIMP_TAC[DIV_EQ_0; LE_1] THEN SIMP_TAC[GSYM NOT_LE] THEN
    SUBGOAL_THEN `!k. 1 <= k ==> ~(z pow k = Cx(&1))` (fun th -> SIMP_TAC[th])
    THENL [ASM_MESON_TAC[COMPLEX_POW_EQ_1; LE_1; REAL_LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_1; complex_div] THEN
    REWRITE_TAC[COMPLEX_RING `(zx * i - (zx - w) * i) = w * i`] THEN
    SIMP_TAC[COMPLEX_POW_POW] THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. vsum (1..x)
                       (\n. z pow x * c n *
                            z pow (n - x MOD n) / (Cx(&1) - z pow n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `(zx * cn) * zn = cn * zx * zn`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN
      AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
      MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\x. Cx(norm(z) / (&1 - norm z)) * Cx(&x) * z pow x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
      REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                  REAL_ABS_DIV; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `a * &x * b = &x * a * b`] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_DIV; REAL_ABS_POS;
                   NORM_POS_LE; REAL_LE_MUL; REAL_MUL_LID; REAL_ABS_NORM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      SIMP_TAC[complex_div; real_div; COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[COMPLEX_NORM_POW] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
        MATCH_MP_TAC(ARITH_RULE `m < r ==> 1 <= r - m`) THEN
        ASM_SIMP_TAC[DIVISION; LE_1];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `&0 < abs(x - a) <=> ~(a = x)`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(w) = &1 /\ norm(z) < &1 /\ norm(zn) <= norm(z)
        ==> abs(&1 - norm(z)) <= norm(w - zn)`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NUM; COMPLEX_NORM_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN ASM_SIMP_TAC[LIM_N_TIMES_POWN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(bounded
       { (f:complex->complex)(t) | real t /\ &0 <= Re t /\ norm(t) < &1 })`
  MP_TAC THENL
   [REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; RE_CX; IMP_IMP] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x /\ abs x < &1 <=> &0 <= x /\ x < &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    X_CHOOSE_TAC `N:num` (SPEC `&2 * (B + &1)` REAL_ARCH_SIMPLE) THEN
    SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `t = &1 - inv(&(p EXP N)) / &2` THEN
    SUBGOAL_THEN `&0 <= t /\ t < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < y /\ y <= &1 ==> &0 <= &1 - y / &2 /\ &1 - y / &2 < &1`) THEN
      ASM_SIMP_TAC[REAL_INV_LE_1; REAL_LT_INV_EQ; REAL_OF_NUM_LE;
                           REAL_OF_NUM_LT; LE_1; EXP_EQ_0; PRIME_IMP_NZ];
      ALL_TAC] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `Cx t`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[SERIES_FROM; LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    SUBGOAL_THEN `?n. M <= n /\ 1 <= n /\ p EXP N <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `p EXP N + M + 1` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm (f (Cx t):complex) <= B` THEN
    MATCH_MP_TAC(NORM_ARITH
     `B + &1 <= norm(x) ==> norm(y) <= B ==> ~(dist(x,y) < &1)`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= Re z /\ abs(Re z) <= norm z ==> a <= norm z`) THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (\k. p EXP k) (0..N))
                    (\x. Re (vsum {d | d divides x} (\d. c d)) * t pow x)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; IN_DIFF; SUBSET; IN_ELIM_THM;
                  FORALL_IN_IMAGE] THEN
      MP_TAC(SPECL [`d:num`; `c:num->complex`]
        DIRICHLET_CHARACTER_DIVISORSUM_POS) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; LE_1; ETA_AX] THEN
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP N` THEN
      ASM_SIMP_TAC[LE_EXP; PRIME_IMP_NZ]] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EQ_EXP] THEN ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (0..N) (\k. &1 * &1 / &2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`d:num`; `c:num->complex`; `p:num`; `k:num`]
                DIRICHLET_CHARACTER_DIVISORSUM_EQ_1) THEN
      ASM_SIMP_TAC[ETA_AX; RE_CX; REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`inv(&(p EXP N)) / &2`; `p EXP k`] lemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_INV_MUL; REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; MULT_EQ_0; ARITH; PRIME_IMP_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= a ==> a <= x ==> b <= x`) THEN
    MATCH_MP_TAC(REAL_ARITH `x * y <= &1 ==> &1 / &2 <= &1 - x * y / &2`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
                 EXP_EQ_0; PRIME_IMP_NZ] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; LE_EXP] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_LFUNCTION_PARTIAL_SUMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MESON[] `(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)`] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 1 INTER (0..n)) (\k. c k * b (z:complex) k :complex)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; GSYM sums] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`c:num->complex`; `(b:complex->num->complex) z`;
                 `B:real`; `1`] SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    SUBGOAL_THEN `(b:complex->num->complex) z 1 = Cx(&1)` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      REWRITE_TAC[COMPLEX_POW_1; COMPLEX_INV_MUL; complex_div] THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_INV_1] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN REWRITE_TAC[COMPLEX_SUB_0] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `norm(Cx(&1)) < &1` THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_LT_REFL; REAL_ABS_NUM];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_NUM; REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` SUBST_ALL_TAC o
                GEN_REWRITE_RULE I [REAL_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; COMPLEX_NORM_CX]) THEN
  SUBGOAL_THEN `!n. &0 < sum(0..n) (\m. t pow m)` ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC[LE_0; SUM_CLAUSES_LEFT; real_pow] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    ASM_SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_POW_LE];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; GSYM CX_MUL;
              GSYM CX_INV; REAL_CX; RE_CX]
  THENL
   [ASM_SIMP_TAC[REAL_SUB_POW_L1; REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT;
                 LE_1; REAL_ARITH `abs t < &1 ==> &0 < &1 - t`] THEN
    ASM_SIMP_TAC[real_div; REAL_FIELD
     `abs(t) < &1 ==> (x * inv(&1 - t) * y) * (&1 - t) = x * y`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / y * &n = (&n * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n-1) (\m. t pow n)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_CONST_NUMSEG; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`;
                   SUB_0; REAL_LE_REFL];
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN REPEAT CONJ_TAC THEN
      TRY ASM_REAL_ARITH_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_POW_L1; ARITH_RULE `1 <= n + 1`] THEN
  REWRITE_TAC[ADD_SUB; REAL_INV_MUL; real_div] THEN
  REWRITE_TAC[REAL_ARITH `x * t - y * t * z <= u * t - v * t * w <=>
                          t * (v * w - y * z) <= t * (u - x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_FIELD
   `&0 < y /\ &0 < z ==> x / y - w / z = (x * z - w * y) / (y * z)`] THEN
  SUBGOAL_THEN `t pow n * sum (0..n) (\m. t pow m) -
                t pow (n + 1) * sum (0..n - 1) (\m. t pow m) = t pow n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(n + 1) + x = n + x + 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET); SUB_ADD; ADD_CLAUSES] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; GSYM SUM_LMUL; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[SUB_ADD; REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; GSYM REAL_OF_NUM_ADD;
               REAL_OF_NUM_LE;
       REAL_FIELD `&1 <= n ==> inv(n) - inv(n + &1) = inv(n * (n + &1))`] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
           CONJ_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ]) THEN
    ASM_SIMP_TAC[REAL_POW_LE; SUM_POS_LE_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `t:real`] AGM_SPECIAL) THEN
  MP_TAC(SPECL [`n - 1`; `t:real`] AGM_SPECIAL) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; REAL_SUB_ADD] THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
               LE_1; REAL_ARITH `&0 < &n + &1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c /\ d ==> e <=> b /\ d ==> a /\ c ==> e`]
   REAL_LE_MUL2)) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_ARITH `&0 <= &n + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> b <= x ==> a <= y`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2; real_div; REAL_INV_MUL; REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_MUL_AC];
    REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC]]);;
```

### Informal statement
For any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0$ modulo $d$, if $c(n)$ is real-valued for all $n$, then the L-function $L(c)$ is non-zero:
$$\forall d,c.\ \text{dirichlet\_character}(d,c) \land c \neq \chi_0(d) \land (\forall n.\ \text{real}(c(n))) \Rightarrow L(c) \neq 0$$

Here, $L(c)$ is the Dirichlet L-function defined by the infinite sum $\sum_{n=1}^{\infty} \frac{c(n)}{n}$.

### Informal proof
We'll prove that the L-function of a non-principal real-valued Dirichlet character cannot be zero.

First, let's establish some properties. For any Dirichlet character $c$ modulo $d$ that is not the principal character $\chi_0$, we know that $d > 1$ (by `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`).

Our proof strategy involves studying analytic properties of the function:
$$f(z) = \sum_{n=1}^{\infty} c(n) \cdot z^n$$

For $|z| < 1$, we will show:

1. This function has an analytic continuation to $z = 1$ with $f(1) = L(c)$
2. $f(z)$ cannot be bounded for real $z$ approaching 1 from below
3. If $L(c) = 0$, then $f(z)$ would be bounded near $z = 1$
4. This contradiction proves $L(c) \neq 0$

The key steps in the proof:

* For $|z| < 1$, we establish that $\sum_{n=1}^{\infty} c(n) \cdot \frac{z^n}{1-z^n}$ is summable.

* We use the identity $b(z,n) = \frac{1}{n(1-z)} - \frac{z^n}{1-z^n}$ and show that $\sum_{n=1}^{\infty} c(n) \cdot b(z,n) = -f(z)$.

* We prove that $f(z) = \sum_{n=1}^{\infty} \left(\sum_{d|n} c(d)\right) z^n$.

* Using properties of Dirichlet characters and special values of divisor sums, we demonstrate that $f(z)$ is unbounded as real $z \to 1^-$.

* However, if $L(c) = 0$, we would have boundedness of the partial sums $\sum_{n=1}^{N} c(n)$, which implies boundedness of $f(z)$ for real $z < 1$.

* This contradiction proves that $L(c) \neq 0$.

### Mathematical insight
This theorem is a special case of the non-vanishing of L-functions at $s=1$ for non-principal Dirichlet characters. It's significant in number theory because:

1. For real characters, it relates to class number formulas and properties of quadratic fields.
2. The non-vanishing of L-functions at $s=1$ is crucial in proving properties of prime numbers in arithmetic progressions.
3. It's a simpler case of the more general result that L-functions don't vanish on the line Re(s)=1, which is needed for the strongest form of the Prime Number Theorem for arithmetic progressions.

The proof uses techniques from complex analysis, particularly the theory of Dirichlet series, to establish the behavior of the L-function near the boundary of its region of absolute convergence.

### Dependencies
- Theorems:
  - `LIM_N_TIMES_POWN`: Limit property that $n \cdot z^n \to 0$ as $n \to \infty$ when $|z| < 1$
  - `VSUM_VSUM_DIVISORS`: Identity for reordering sums over divisors
  - `DIRICHLET_CHARACTER_NORM`: Characterizes norm values of Dirichlet characters
  - `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`: Non-principal characters have modulus $d > 1$
  - `BOUNDED_LFUNCTION_PARTIAL_SUMS`: Bounds on partial sums of non-principal characters
  - `LFUNCTION`: Definition of L-function as the sum $\sum_{n=1}^{\infty} \frac{c(n)}{n}$
  - `AGM_SPECIAL`: Special case of the arithmetic-geometric mean inequality
  - `DIRICHLET_CHARACTER_DIVISORSUM_EQ_1`: Sum of character values over divisors equals 1
  - `DIRICHLET_CHARACTER_DIVISORSUM_POS`: Sum of real character values over divisors is non-negative

- Definitions:
  - `dirichlet_character`: Defines Dirichlet character properties
  - `chi_0`: The principal Dirichlet character

### Porting notes
When porting this theorem:
1. The proof uses complex analysis and Dirichlet series techniques, which may require developing corresponding libraries in the target system.
2. The argument involves careful handling of convergence and bounding of various series, which requires appropriate analysis libraries.
3. Pay attention to how characters and L-functions are defined in the target system, as differences in formalization might require adapting the proof techniques.
4. The proof relies on properties of Dirichlet characters that would need to be established first, particularly those concerning character divisor sums.

---

## BOUNDED_DIFF_LOGMUL

### Name of formal statement
BOUNDED_DIFF_LOGMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIFF_LOGMUL = prove
 (`!f a. bounded {f x - Cx(log(&x)) * a | x IN (:num)}
         ==> (!x. &0 <= Re(f x)) ==> &0 <= Re a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `exp((B + &1) / --(Re a))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `abs(Re(f n - Cx(log(&n)) * a)) <= B` MP_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; RE_MUL_CX; REAL_NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `B < l * --a /\ &0 <= f ==> B < abs(f - l * a)`) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_NEG_GT0] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `log(exp((B + &1) / --Re a))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LOG_EXP; REAL_NEG_GT0; REAL_LT_DIV2_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]]);;
```

### Informal statement
For any complex-valued function $f$ and complex number $a$, if the set $\{f(x) - \log(x) \cdot a \mid x \in \mathbb{N}\}$ is bounded and $\text{Re}(f(x)) \geq 0$ for all $x$, then $\text{Re}(a) \geq 0$.

### Informal proof
Let's prove this by contradiction.

Suppose that the set $\{f(x) - \log(x) \cdot a \mid x \in \mathbb{N}\}$ is bounded, meaning there exists some real number $B > 0$ such that $|f(x) - \log(x) \cdot a| \leq B$ for all natural numbers $x$. We also assume that $\text{Re}(f(x)) \geq 0$ for all $x$.

Now, assume toward contradiction that $\text{Re}(a) < 0$. 

By the Archimedean property, there exists a natural number $n$ such that $n > \exp\left(\frac{B + 1}{-\text{Re}(a)}\right)$.

For this value of $n$, we know that $|\text{Re}(f(n) - \log(n) \cdot a)| \leq B$ since the absolute value of the real part is bounded by the norm of the complex number.

Looking at the real part: $\text{Re}(f(n) - \log(n) \cdot a) = \text{Re}(f(n)) - \log(n) \cdot \text{Re}(a)$

Since $\text{Re}(a) < 0$ and $\text{Re}(f(n)) \geq 0$, we have:
$\text{Re}(f(n)) - \log(n) \cdot \text{Re}(a) \geq 0 - \log(n) \cdot \text{Re}(a) = \log(n) \cdot (-\text{Re}(a))$

By our choice of $n$, we have:
$\log(n) > \frac{B + 1}{-\text{Re}(a)}$

Multiplying both sides by $-\text{Re}(a) > 0$, we get:
$\log(n) \cdot (-\text{Re}(a)) > B + 1$

Therefore:
$\text{Re}(f(n) - \log(n) \cdot a) > B + 1 > B$

This contradicts our assumption that $|\text{Re}(f(n) - \log(n) \cdot a)| \leq B$.

Hence, our initial assumption that $\text{Re}(a) < 0$ must be false, so $\text{Re}(a) \geq 0$.

### Mathematical insight
This theorem establishes an important constraint on the asymptotic behavior of complex-valued functions. Specifically, it shows that if a function $f$ stays within a bounded distance of $\log(x) \cdot a$ and maintains a non-negative real part, then $a$ must have a non-negative real part as well.

The key insight is that if $\text{Re}(a)$ were negative, the term $\log(x) \cdot a$ would grow increasingly negative as $x$ increases, forcing $f(x)$ to have increasingly negative real parts to maintain the bounded difference - which would contradict the constraint that $\text{Re}(f(x)) \geq 0$.

This result appears to be used in the context of analysis of characters in number theory, specifically for proving that non-principal characters do not vanish, as suggested by the comment.

### Dependencies
- **Theorems**:
  - `REAL_EXP_POS_LT`: $\forall x. 0 < \exp(x)$
  - `LOG_EXP`: $\forall x. \log(\exp(x)) = x$
  - `LOG_MONO_LE_IMP`: $\forall x\ y. 0 < x \land x \leq y \Rightarrow \log(x) \leq \log(y)$
- **Definitions**:
  - `exp`: $\exp(x) = \text{Re}(\text{cexp}(\text{Cx}(x)))$

### Porting notes
When porting this theorem:
1. Ensure your system has a well-defined complex logarithm function with appropriate domain restrictions.
2. The proof relies on the Archimedean property of real numbers, which might be formalized differently in other proof assistants.
3. Consider how your target system handles complex numbers, especially the real and imaginary parts.
4. The proof uses contradiction with careful manipulation of inequalities, which should translate well across most systems.

---

## LFUNCTION_NONZERO_NONPRINCIPAL

### Name of formal statement
LFUNCTION_NONZERO_NONPRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_NONZERO_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(Lfunction c = Cx(&0))`,
  let lemma = prove
   (`{a,b,c} SUBSET s
     ==> FINITE s
         ==> !f. sum s f = sum (s DIFF {a,b,c}) f + sum {a,b,c} f`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) in
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_0]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x c. vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) -
           Cx(log(&x)) *
           (if c = chi_0 d then Cx(&1)
            else if Lfunction c = Cx(&0) then --Cx(&1)
            else Cx(&0))`;
    `(:num)`;
    `{c | dirichlet_character d c}`]
   BOUNDED_SUMS_IMAGES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN
    ASM_CASES_TAC `c = chi_0 d` THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RID; BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL;
                 LE_1] THEN
    ASM_CASES_TAC `Lfunction c = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_RNEG; COMPLEX_MUL_RZERO;
                    COMPLEX_MUL_RID; COMPLEX_SUB_RNEG] THEN
    ASM_MESON_TAC[BOUNDED_DIRICHLET_MANGOLDT_ZERO;
                  BOUNDED_DIRICHLET_MANGOLDT_NONZERO; LE_1];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_SUB; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_DIFF_LOGMUL) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:num` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o funpow 2 rand o snd) THEN
    REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS;
             REAL_LE_DIV; REAL_POS; MANGOLDT_POS_LE];
    ALL_TAC] THEN
  SIMP_TAC[RE_VSUM; FINITE_DIRICHLET_CHARACTERS] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN DISCH_TAC THEN
  X_GEN_TAC `c:num->complex` THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LT]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{chi_0 d,c,(\n. cnj(c n))} SUBSET {c | dirichlet_character d c}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[DIRICHLET_CHARACTER_CHI_0; DIRICHLET_CHARACTER_CNJ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &0 /\ t < &0 ==> s + t < &0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_POS_LE THEN
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_DIFF] THEN
    SIMP_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; IN_INSERT; NOT_IN_EMPTY;
               FINITE_RULES] THEN
  SUBGOAL_THEN `~(chi_0 d = (\n. cnj (c n)))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(\c n:num. cnj(c n))`) THEN
    REWRITE_TAC[CNJ_CNJ; FUN_EQ_THM; CNJ_CHI_0] THEN
    ASM_REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = \n:num. cnj(c n))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM REAL_CNJ; FUN_EQ_THM] THEN
    ASM_MESON_TAC[LFUNCTION_NONZERO_REAL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_CNJ) THEN
  ASM_SIMP_TAC[CNJ_EQ_CX] THEN REAL_ARITH_TAC);;
```

### Informal statement
This theorem states that for any modulus $d$ and any non-principal Dirichlet character $c$, the associated $L$-function evaluated at 1 is non-zero:

$$\forall d,c.\ \text{dirichlet\_character}(d,c) \land c \neq \chi_0(d) \Rightarrow L(c) \neq 0$$

where:
- $\text{dirichlet\_character}(d,c)$ indicates that $c$ is a Dirichlet character modulo $d$
- $\chi_0(d)$ is the principal character modulo $d$ defined by $\chi_0(d, n) = 1$ if $\gcd(n,d)=1$ and $\chi_0(d, n) = 0$ otherwise
- $L(c)$ is the Dirichlet $L$-function associated with character $c$, evaluated at $s=1$

### Informal proof
The proof uses several key techniques from analytic number theory.

We begin by handling the special case where $d = 0$, which is resolved using the characterization of Dirichlet characters modulo 0.

For the general case, we apply a bounded sums argument on the set of Dirichlet characters modulo $d$. We consider the expression:

$$\sum_{n=1}^x c(n) \frac{\Lambda(n)}{n} - \log(x) \cdot \begin{cases}
1 & \text{if } c = \chi_0(d) \\
-1 & \text{if } L(c) = 0 \\
0 & \text{otherwise}
\end{cases}$$

where $\Lambda(n)$ is the von Mangoldt function.

For this expression, we establish:
1. The sum is bounded as $x$ varies over natural numbers, using different theorems depending on whether:
   - $c$ is the principal character $\chi_0(d)$ (using `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`)
   - $L(c) = 0$ (using `BOUNDED_DIRICHLET_MANGOLDT_ZERO`)
   - $L(c) \neq 0$ (using `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`)

2. We then use `BOUNDED_DIFF_LOGMUL` to show that the real part of the coefficient of $\log(x)$ must be non-negative, deriving a contradiction if we assume that $L(c) = 0$ for a non-principal character.

3. We further demonstrate that the sum over all characters is non-negative, using properties of the von Mangoldt function.

4. For the crucial step, we focus on three particular characters: the principal character $\chi_0(d)$, our target character $c$, and its complex conjugate $\overline{c}$. By analyzing the sum over these three characters, and using the fact that $L(\overline{c}) = \overline{L(c)}$ when $c$ is a non-principal character, we derive a contradiction if $L(c) = 0$.

The proof concludes by showing that our assumption that $L(c) = 0$ leads to a numerical inequality that cannot be satisfied, thus establishing that $L(c) \neq 0$.

### Mathematical insight
This theorem is a non-trivial result about the non-vanishing of Dirichlet L-functions at $s=1$ for non-principal characters. It's a key ingredient in the proof of Dirichlet's theorem on primes in arithmetic progressions, which states that for any two positive coprime integers $a$ and $d$, there are infinitely many primes of the form $a + nd$ where $n \geq 0$.

The non-vanishing of $L(c)$ when $c$ is a non-principal character is what ultimately allows us to show that primes are equidistributed among the reduced residue classes modulo $d$. If $L(c)$ could be zero, then there would be a bias in the distribution of primes among these residue classes.

The proof techniques used here are characteristic of analytic number theory, using properties of Dirichlet characters and L-functions, and a careful analysis of asymptotic behavior.

### Dependencies
- **Theorems**:
  - `MANGOLDT_POS_LE`: Establishes that the von Mangoldt function is non-negative
  - `DIRICHLET_CHARACTER_CHI_0`: Shows that the principal character is a Dirichlet character
  - `DIRICHLET_CHARACTER_0`: Characterizes Dirichlet characters modulo 0
  - `FINITE_DIRICHLET_CHARACTERS`: States that the set of Dirichlet characters modulo $d$ is finite
  - `DIRICHLET_CHARACTER_CNJ`: Shows that the complex conjugate of a Dirichlet character is also a Dirichlet character
  - `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS`: Result about positivity of character sums
  - `CNJ_CHI_0`: Shows that the complex conjugate of the principal character equals the principal character
  - `LFUNCTION_CNJ`: Relates L-function of conjugate character to conjugate of L-function
  - `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`: Boundedness result when L-function is non-zero
  - `BOUNDED_DIRICHLET_MANGOLDT_ZERO`: Boundedness result when L-function is zero
  - `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`: Boundedness result for principal character
  - `LFUNCTION_NONZERO_REAL`: Special case that L-function is non-zero for real characters
  - `BOUNDED_DIFF_LOGMUL`: Technical result about bounded difference of logarithmic sums
  
- **Definitions**:
  - `dirichlet_character`: Definition of a Dirichlet character
  - `chi_0`: Definition of the principal character

### Porting notes
When porting this theorem:
1. This proof relies heavily on complex analysis and analytical number theory results. Ensure that the necessary framework is in place.
2. The proof makes use of bounded sums and character properties that may need to be separately established in the target system.
3. The theorem involves a number of technical lemmas about boundedness of specific sums, which you'll need to port or develop equivalents for.
4. The von Mangoldt function $\Lambda(n)$ plays a key role, so ensure it's properly defined.
5. Pay attention to the handling of complex-valued character functions and their conjugates.

---

## BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_DIRICHLET_MANGOLDT_NONZERO THEN
  EXISTS_TAC `d:num` THEN
  ASM_MESON_TAC[LFUNCTION_NONZERO_NONPRINCIPAL]);;
```

### Informal statement
For all $d$ and $c$, if $c$ is a Dirichlet character modulo $d$ and $c$ is not the principal character $\chi_0$ modulo $d$, then the set 
$$\left\{ \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} : x \in \mathbb{N} \right\}$$
is bounded, where $\Lambda(n)$ is the Mangoldt function.

### Informal proof
We apply the theorem `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`, which states that for any Dirichlet character $c$ that is not the principal character and has a non-zero L-function value, the set in question is bounded.

To use this theorem, we need to show that a non-principal Dirichlet character has a non-zero L-function. This follows directly from the theorem `LFUNCTION_NONZERO_NONPRINCIPAL`, which states precisely that if $c$ is a Dirichlet character modulo $d$ and $c$ is not the principal character $\chi_0$ modulo $d$, then $L(c) \neq 0$.

Thus, given our assumptions that $c$ is a Dirichlet character and $c$ is not the principal character, we can conclude that the set is bounded.

### Mathematical insight
This theorem extends the boundedness result for partial sums of the Dirichlet series involving the Mangoldt function to all non-principal characters. The boundedness of these sums is crucial in analytic number theory, particularly in the study of the distribution of primes in arithmetic progressions.

The result is significant because it shows that the fluctuations in these partial sums remain controlled as the upper limit increases, which is a key property in proving results about the distribution of primes. This is in contrast to the principal character case, where the partial sums grow logarithmically.

The proof relies on the non-vanishing of the L-function for non-principal characters, which is a deep result in the theory of Dirichlet L-functions.

### Dependencies
- Theorems:
  - `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`: Shows boundedness for non-principal characters with non-zero L-function
  - `LFUNCTION_NONZERO_NONPRINCIPAL`: Proves that L-functions for non-principal characters are non-zero

- Definitions:
  - `dirichlet_character`: Defines a Dirichlet character modulo d
  - `chi_0`: Defines the principal Dirichlet character modulo d

### Porting notes
When porting this theorem, ensure that the Dirichlet character and the Mangoldt function are properly defined. The theorem relies heavily on properties of L-functions and their non-vanishing for non-principal characters, which might require substantial supporting theory in the target system.

---

## BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Name of formal statement
BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS = prove
 (`!d l. 1 <= d /\ coprime(l,d)
         ==> bounded { vsum {c | dirichlet_character d c}
                            (\c. c(l) *
                                 vsum(1..x) (\n. c n * Cx (mangoldt n / &n))) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. Cx(log(&x)) =
                        vsum {c | dirichlet_character d c}
                             (\c. if c = chi_0 d then Cx(log(&x)) else Cx(&0))`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
    REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0];
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_DIRICHLET_CHARACTERS] THEN
  MATCH_MP_TAC BOUNDED_SUMS_IMAGES THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `c = chi_0 d` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL) THEN
    ASM_REWRITE_TAC[chi_0; COMPLEX_MUL_LID];
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`]
      BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BOUNDED_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
For any positive integer $d$ and integer $l$ coprime to $d$, the set
$$\left\{\sum_{c \in C_d} c(l) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} - \log(x) \;\middle|\; x \in \mathbb{N}\right\}$$
is bounded, where $C_d = \{c \mid c \text{ is a Dirichlet character modulo } d\}$ and $\Lambda(n)$ is the von Mangoldt function.

Here, $c(n)$ represents a Dirichlet character modulo $d$, which satisfies:
- $c(n+d) = c(n)$ for all $n$ (periodicity)
- $c(n) = 0$ if and only if $\gcd(n,d) > 1$ (zeros at non-coprime values)
- $c(m \cdot n) = c(m) \cdot c(n)$ for all $m,n$ (multiplicativity)

### Informal proof

The proof proceeds as follows:

- First, we rewrite $\log(x)$ as a sum over Dirichlet characters:
  $$\log(x) = \sum_{c \in C_d} \begin{cases} 
  \log(x) & \text{if } c = \chi_0 \\
  0 & \text{otherwise}
  \end{cases}$$
  where $\chi_0$ is the principal character defined by:
  $$\chi_0(n) = \begin{cases} 
  1 & \text{if } \gcd(n,d) = 1 \\
  0 & \text{otherwise}
  \end{cases}$$

- Using this identity, we can express the original sum as:
  $$\sum_{c \in C_d} c(l) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} - \sum_{c \in C_d} \begin{cases}
  \log(x) & \text{if } c = \chi_0 \\
  0 & \text{otherwise}
  \end{cases}$$

- This can be rewritten as:
  $$\sum_{c \in C_d} \left(c(l) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} - \begin{cases}
  \log(x) & \text{if } c = \chi_0 \\
  0 & \text{otherwise}
  \end{cases}\right)$$

- To show that this sum is bounded, we apply the theorem about boundedness of sums over finite sets (`BOUNDED_SUMS_IMAGES`).

- For each character $c$, we consider two cases:
  1. When $c = \chi_0$ (the principal character):
     - We apply `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL` which states that 
       $$\left\{\sum_{n=1}^{x} \chi_0(n) \cdot \frac{\Lambda(n)}{n} - \log(x) \;\middle|\; x \in \mathbb{N}\right\}$$
       is bounded when $d \geq 1$.
     - Since $\chi_0(l) = 1$ for any $l$ coprime to $d$, we get the desired result.

  2. When $c \neq \chi_0$ (non-principal characters):
     - We apply `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL` which states that
       $$\left\{\sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n} \;\middle|\; x \in \mathbb{N}\right\}$$
       is bounded for any non-principal character $c$.
     - We note that $|c(l)| = 1$ when $\gcd(l,d) = 1$ (using `DIRICHLET_CHARACTER_NORM`).
     - By the properties of norms, $|c(l) \cdot \sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n}| = |c(l)| \cdot |\sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n}| \leq 1 \cdot |\sum_{n=1}^{x} c(n) \cdot \frac{\Lambda(n)}{n}|$
     - This establishes the boundedness for each term in the sum.

- Since the set of Dirichlet characters modulo $d$ is finite (by `FINITE_DIRICHLET_CHARACTERS`) and each term in the sum is bounded, the entire sum is bounded.

### Mathematical insight
This theorem represents an important result in analytic number theory related to Dirichlet characters and L-functions. It essentially shows that a certain weighted sum over Dirichlet characters of sums involving the von Mangoldt function (which counts prime powers) behaves asymptotically like $\log(x)$.

The result is significant because:

1. It connects the distribution of primes (via the von Mangoldt function) with Dirichlet characters
2. It provides a key step in understanding how primes are distributed in arithmetic progressions
3. The bounded error term indicates that this approximation becomes increasingly accurate as $x$ grows

This type of result is fundamental in the proof of the Prime Number Theorem for arithmetic progressions and other related theorems in analytic number theory.

### Dependencies
- Definitions:
  - `dirichlet_character`: Defines the properties of a Dirichlet character
  - `chi_0`: Defines the principal Dirichlet character

- Theorems:
  - `DIRICHLET_CHARACTER_NORM`: Establishes the norm of a Dirichlet character
  - `DIRICHLET_CHARACTER_CHI_0`: Shows that `chi_0 d` is a Dirichlet character modulo d
  - `FINITE_DIRICHLET_CHARACTERS`: Proves that the set of Dirichlet characters modulo d is finite
  - `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`: Shows boundedness of the sum with the principal character
  - `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL`: Shows boundedness of the sum with non-principal characters

### Porting notes
When porting this theorem:
1. Ensure the definition of Dirichlet characters matches the HOL Light version, particularly the three key properties (periodicity, zeros at non-coprime values, and multiplicativity)
2. The von Mangoldt function may be defined differently in other systems, so check for consistency
3. The proof heavily relies on boundedness properties of sums involving Dirichlet characters, which may need separate porting and verification
4. The handling of complex numbers and sums over sets might differ between proof assistants

---

## DIRICHLET_MANGOLDT

### DIRICHLET_MANGOLDT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_MANGOLDT = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> bounded { Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)}
                                           (\n. Cx(mangoldt n / &n)) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?l. (k * l == 1) (mod d)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[CONG_SOLVE]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `l:num`] BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(k * l == 1) (mod d)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(K ALL_TAC) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  MP_TAC(GSYM(SPEC `d:num` DIRICHLET_CHARACTER_MUL)) THEN
  SIMP_TAC[IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS] THEN
  SUBGOAL_THEN `(l * n == 1) (mod d) <=> (n == k) (mod d)` SUBST1_TAC THENL
   [UNDISCH_TAC `(k * l == 1) (mod d)` THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;
```

### Informal statement
For any positive integers $d$ and $k$ such that $\gcd(k,d) = 1$, the set
$$\left\{ \phi(d) \sum_{\substack{n \leq x \\ n \equiv k \pmod{d}}} \frac{\Lambda(n)}{n} - \log(x) \mid x \in \mathbb{N} \right\}$$
is bounded, where:
- $\phi(d)$ is Euler's totient function
- $\Lambda(n)$ is the von Mangoldt function
- The sum is over all $n \leq x$ such that $n \equiv k \pmod{d}$

### Informal proof
We prove that for strictly positive $d$ and $k$ coprime to $d$, the sequence of differences between $\phi(d)$ times the sum of normalized Mangoldt values in an arithmetic progression and $\log(x)$ is bounded.

The proof proceeds as follows:

1. First, since $\gcd(k,d) = 1$, we can find $l$ such that $kl \equiv 1 \pmod{d}$ (using the theorem `CONG_SOLVE`).

2. We apply `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS` with $d$ and $l$, which establishes that 
   $$\left\{ \sum_{c \text{ is a Dirichlet character} \mod d} c(l) \sum_{n=1}^x c(n)\frac{\Lambda(n)}{n} - \log(x) \mid x \in \mathbb{N} \right\}$$
   is bounded.

3. We then transform our target expression to match this result by:
   
   a. Expressing the sum over arithmetic progression as a sum involving Dirichlet characters:
      $$\phi(d) \sum_{\substack{n \leq x \\ n \equiv k \pmod{d}}} \frac{\Lambda(n)}{n} = \sum_{c \text{ is a Dirichlet character} \mod d} c(l) \sum_{n=1}^x c(n)\frac{\Lambda(n)}{n}$$
   
   b. This transformation uses the orthogonality relation of Dirichlet characters, specifically that:
      $$\sum_{c \text{ is a Dirichlet character} \mod d} c(m)c(n) = \begin{cases} 
      \phi(d) & \text{if } m \equiv n \pmod{d} \\
      0 & \text{otherwise}
      \end{cases}$$

4. The key insight is that $n \equiv k \pmod{d}$ if and only if $l \cdot n \equiv 1 \pmod{d}$ (since $kl \equiv 1 \pmod{d}$), which allows us to properly identify the arithmetic progression through the Dirichlet characters.

### Mathematical insight
This theorem is a form of the Prime Number Theorem for arithmetic progressions. It establishes that the distribution of primes in arithmetic progressions $n \equiv k \pmod{d}$ with $\gcd(k,d) = 1$ follows a specific asymptotic behavior. The von Mangoldt function $\Lambda(n)$ is weighted toward prime powers, and this theorem shows that these prime powers are distributed across the coprime residue classes modulo $d$ in a uniform way asymptotically.

The result is significant because it implies that the density of primes in each coprime residue class modulo $d$ is approximately $\frac{1}{\phi(d)}$ of all primes, which is a fundamental result in number theory known as Dirichlet's theorem on arithmetic progressions.

### Dependencies

#### Theorems:
- `CONG_SOLVE`: For any $a$, $b$, and $n$ where $\gcd(a,n) = 1$, there exists $x$ such that $ax \equiv b \pmod{n}$.
- `DIRICHLET_CHARACTER_MUL`: For a Dirichlet character $c$ modulo $d$, $c(mn) = c(m) \cdot c(n)$.
- `FINITE_DIRICHLET_CHARACTERS`: The set of Dirichlet characters modulo $d$ is finite.
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS`: If $d \geq 1$, then the sum of $c(n)$ over all Dirichlet characters $c$ modulo $d$ equals $\phi(d)$ if $n \equiv 1 \pmod{d}$, and 0 otherwise.
- `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS`: For $d \geq 1$ and $\gcd(l,d) = 1$, the set $\left\{ \sum_{c} c(l) \sum_{n=1}^x c(n)\frac{\Lambda(n)}{n} - \log(x) \mid x \in \mathbb{N} \right\}$ is bounded.

### Porting notes
When porting this theorem:
1. Ensure your system has the necessary number theory infrastructure for Dirichlet characters and the von Mangoldt function.
2. The proof relies heavily on orthogonality properties of Dirichlet characters, which might require specific setups in some proof assistants.
3. The manipulations involving modular congruences may need explicit justification in systems with stricter typing or less automated number theory reasoning.

---

## DIRICHLET_MANGOLDT_EXPLICIT

### Name of formal statement
DIRICHLET_MANGOLDT_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_MANGOLDT_EXPLICIT = prove
 (`!d k. 1 <= d /\ coprime (k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {n | n IN 1..x /\ (n == k) (mod d)}
                             (\n. mangoldt n / &n) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  SIMP_TAC[VSUM_CX; FINITE_RESTRICT; FINITE_NUMSEG;
           GSYM CX_SUB; GSYM CX_MUL; COMPLEX_NORM_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B / &(phi d)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; PHI_LOWERBOUND_1_STRONG;
               REAL_LE_RDIV_EQ] THEN
  X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL;
               LE_1; PHI_LOWERBOUND_1_STRONG; REAL_OF_NUM_EQ]);;
```

### Informal statement
For all positive integers $d$ and $k$ such that $\gcd(k,d) = 1$ (i.e., $k$ and $d$ are coprime), there exists a positive real number $B$ such that for all $x$:

$$\left|\sum_{\substack{n \in \{1,\ldots,x\} \\ n \equiv k \pmod{d}}} \frac{\Lambda(n)}{n} - \frac{\log(x)}{\phi(d)}\right| \leq B$$

where:
- $\Lambda(n)$ is the von Mangoldt function (denoted as `mangoldt n` in HOL Light)
- $\phi(d)$ is Euler's totient function
- The sum is taken over all integers $n$ from 1 to $x$ that are congruent to $k$ modulo $d$

### Informal proof
The proof proceeds by applying the previously established theorem `DIRICHLET_MANGOLDT` and transforming it into the explicit form required.

- We begin with integers $d$ and $k$ where $d \geq 1$ and $\gcd(k,d) = 1$.
- From the `DIRICHLET_MANGOLDT` theorem, we know that the set 
  $\{\phi(d) \cdot \sum_{n=1,\, n \equiv k \pmod{d}}^x \frac{\Lambda(n)}{n} - \log(x) \mid x \in \mathbb{N}\}$ 
  is bounded.
- This means there exists some bound $B > 0$ such that for all $x \in \mathbb{N}$, the complex norm satisfies:
  $|\phi(d) \cdot \sum_{n=1,\, n \equiv k \pmod{d}}^x \frac{\Lambda(n)}{n} - \log(x)| \leq B$
- The proof transforms this complex representation to the real domain using operations like `VSUM_CX`, `CX_SUB`, `CX_MUL`, and `COMPLEX_NORM_CX`.
- We then divide both sides by $\phi(d)$ to get:
  $|\sum_{n=1,\, n \equiv k \pmod{d}}^x \frac{\Lambda(n)}{n} - \frac{\log(x)}{\phi(d)}| \leq \frac{B}{\phi(d)}$
- Since $d \geq 1$, we know that $\phi(d) \geq 1$ (using `PHI_LOWERBOUND_1_STRONG`), so $\frac{B}{\phi(d)} > 0$.
- Thus, setting the new bound to $\frac{B}{\phi(d)}$ completes the proof.

### Mathematical insight
This theorem provides an explicit error bound for the distribution of prime logarithms in arithmetic progressions. It refines the Dirichlet-Mangoldt theorem by providing a concrete formula for the sum of the von Mangoldt function over integers in an arithmetic progression, showing that it approximates $\frac{\log(x)}{\phi(d)}$ with bounded error.

This result is significant in analytic number theory as it relates to:
1. The distribution of primes in arithmetic progressions
2. The behavior of Dirichlet $L$-functions
3. The asymptotic density of primes in residue classes

The theorem is a more concrete version of the broader Dirichlet theorem on primes in arithmetic progressions, giving specific approximation bounds rather than just asymptotic results.

### Dependencies
- **Theorems**:
  - `DIRICHLET_MANGOLDT`: States that the set of expressions $\phi(d) \cdot \sum_{n \equiv k \pmod{d}} \frac{\Lambda(n)}{n} - \log(x)$ is bounded
  - `BOUNDED_POS`: Characterization of bounded sets in terms of positive bounds
  - `PHI_LOWERBOUND_1_STRONG`: Lower bound for Euler's totient function, specifically that $\phi(d) \geq 1$ for $d \geq 1$
- **Tactical functions**:
  - SIMPLE_IMAGE, FORALL_IN_IMAGE, IN_UNIV, VSUM_CX, FINITE_RESTRICT, FINITE_NUMSEG, GSYM CX_SUB, GSYM CX_MUL, COMPLEX_NORM_CX

### Porting notes
When porting this theorem:
1. Ensure that the von Mangoldt function ($\Lambda(n)$) is correctly defined in your target system
2. Verify that Euler's totient function ($\phi(d)$) has the same properties as in HOL Light
3. The proof relies significantly on the transformation between complex and real domains, so make sure your target system has adequate support for handling these conversions
4. The theorem depends on `DIRICHLET_MANGOLDT`, so that result should be ported first

---

## DIRICHLET_STRONG

### DIRICHLET_STRONG
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_STRONG = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {p | p IN 1..x /\ prime p /\ (p == k) (mod d)}
                             (\p. log(&p) / &p) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_MANGOLDT_EXPLICIT) THEN
  EXISTS_TAC `B + &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) <= a ==> abs(x - z) <= b ==> abs(y - z) <= b + a`) THEN
  MP_TAC(SPECL [`x:num`; `{n | n IN 1..x /\ (n == k) (mod d)}`]
               MERTENS_MANGOLDT_VERSUS_LOG) THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CONJ_ACI]);;
```

### Informal statement
For all positive integers $d$ and $k$ such that $\gcd(k,d) = 1$ (i.e., $k$ and $d$ are coprime), there exists a positive real number $B$ such that for all real $x$:

$$\left|\sum_{\substack{p \leq x \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log(p)}{p} - \frac{\log(x)}{\phi(d)}\right| \leq B$$

where $\phi(d)$ is Euler's totient function.

### Informal proof
The proof follows these steps:

* We begin by applying the `DIRICHLET_MANGOLDT_EXPLICIT` theorem to our assumptions that $d \geq 1$ and $\gcd(k,d) = 1$.
* This gives us a positive real number $B$ such that for all $x$:
  $$\left|\sum_{\substack{n \leq x \\ n \equiv k \pmod{d}}} \frac{\Lambda(n)}{n} - \frac{\log(x)}{\phi(d)}\right| \leq B$$
  where $\Lambda(n)$ is the von Mangoldt function.

* We propose $B + 3$ as the bound for our theorem.
* For any given $x$, we apply the triangle inequality in the form:
  $$|y-z| \leq |x-y| + |x-z|$$
  
* We use `MERTENS_MANGOLDT_VERSUS_LOG` which states that for any subset $s$ of $\{1,2,...,n\}$:
  $$\left|\sum_{d \in s} \frac{\Lambda(d)}{d} - \sum_{\substack{p \in s \\ p \text{ prime}}} \frac{\log(p)}{p}\right| \leq 3$$
  
* Applying this to the set $\{n \in \{1,2,...,x\} | n \equiv k \pmod{d}\}$, we get:
  $$\left|\sum_{\substack{n \leq x \\ n \equiv k \pmod{d}}} \frac{\Lambda(n)}{n} - \sum_{\substack{p \leq x \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log(p)}{p}\right| \leq 3$$
  
* By combining these inequalities, we establish that:
  $$\left|\sum_{\substack{p \leq x \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log(p)}{p} - \frac{\log(x)}{\phi(d)}\right| \leq B + 3$$

### Mathematical insight
This theorem is a strong form of Dirichlet's theorem on primes in arithmetic progressions. While Dirichlet's theorem simply states that there are infinitely many primes in each arithmetic progression $\{k + nd | n \in \mathbb{N}\}$ where $\gcd(k,d) = 1$, this result provides quantitative information about how these primes are distributed.

The sum $\sum \frac{\log(p)}{p}$ is closely related to the density of primes, and this theorem tells us that this sum grows asymptotically like $\frac{\log(x)}{\phi(d)}$, with bounded error. This implies that the primes are approximately equally distributed among the $\phi(d)$ different residue classes modulo $d$ that are coprime to $d$.

This result is fundamental in analytic number theory and has many applications in understanding the distribution of prime numbers.

### Dependencies
- `DIRICHLET_MANGOLDT_EXPLICIT`: States that for coprime integers k and d with d ≥ 1, there exists a bound B such that the sum of the von Mangoldt function over integers congruent to k modulo d differs from log(x)/φ(d) by at most B.
- `MERTENS_MANGOLDT_VERSUS_LOG`: Provides a bound of 3 for the difference between sums involving the von Mangoldt function and sums involving only prime numbers.

### Porting notes
When porting this theorem:
1. Ensure that the von Mangoldt function $\Lambda(n)$ is correctly defined
2. The proof relies heavily on theorems about the distribution of primes in arithmetic progressions
3. The constant 3 in the bound comes from `MERTENS_MANGOLDT_VERSUS_LOG` and should be maintained
4. Be careful with notation for modular arithmetic - in HOL Light `(p == k) (mod d)` means p is congruent to k modulo d

---

## DIRICHLET

### Name of formal statement
DIRICHLET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> INFINITE {p | prime p /\ (p == k) (mod d)}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN MP_TAC(SPECL [`d:num`; `k:num`] DIRICHLET_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC
   `max (exp(&(phi d) *
            (&1 + B + sum {p | p IN 1..n /\ prime p /\ (p == k) (mod d)}
                          (\p. log(&p) / &p))))
        (max (&n) (&1))`
   REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_MAX_LE; REAL_OF_NUM_LE] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) <= b ==> y < &1 + b + x`)) THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LE_RDIV_EQ; PHI_LOWERBOUND_1_STRONG;
               REAL_OF_NUM_LT; LE_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LE_1] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x <= a ==> x = y ==> y <= a`)) THEN
  REPLICATE_TAC 4 AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;
```

### Informal statement
For any natural numbers $d$ and $k$ such that $1 \leq d$ and $\gcd(k,d) = 1$ (i.e., $k$ and $d$ are coprime), the set of prime numbers $p$ that are congruent to $k$ modulo $d$ (i.e., $p \equiv k \pmod{d}$) is infinite.

### Informal proof
This proof establishes Dirichlet's theorem on arithmetic progressions by using the strong version of Dirichlet's theorem about the distribution of primes in arithmetic progressions.

* First, we rewrite the goal using the definition of `INFINITE` and set up a proof by contradiction. We assume that the set $\{p \mid p \text{ is prime and } p \equiv k \pmod{d}\}$ is finite.

* If this set is finite, there exists an upper bound $n$ such that all primes in our arithmetic progression are less than or equal to $n$.

* We apply `DIRICHLET_STRONG` to $d$ and $k$, which gives us a positive constant $B$ such that:
  $$\left|\sum_{\substack{p \leq x \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log p}{p} - \frac{\log x}{\phi(d)}\right| \leq B$$
  for any $x$, where $\phi(d)$ is Euler's totient function.

* Using the Archimedean property of real numbers, we choose a value $m$ that is larger than both $n$ and:
  $$\exp\left(\phi(d) \cdot \left(1 + B + \sum_{\substack{p \leq n \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log p}{p}\right)\right)$$

* When we apply our inequality from `DIRICHLET_STRONG` with $x = m$, we get:
  $$\frac{\log m}{\phi(d)} < 1 + B + \sum_{\substack{p \leq n \\ p \text{ prime} \\ p \equiv k \pmod{d}}} \frac{\log p}{p}$$

* Since all primes in our arithmetic progression are at most $n$ (by our contradiction hypothesis), and $m > n$, the sum in the inequality remains the same if we replace $n$ with $m$. 

* Taking exponentials of both sides and applying the properties of logarithms, we arrive at a contradiction with our choice of $m$.

* Therefore, our initial assumption must be false, and the set of primes in the arithmetic progression must be infinite.

### Mathematical insight
Dirichlet's theorem is a foundational result in number theory, stating that there are infinitely many primes in any arithmetic progression where the first term and common difference are coprime. This generalizes Euclid's theorem on the infinitude of primes.

The proof uses analytic number theory techniques, particularly the asymptotic behavior of the sum $\sum \frac{\log p}{p}$ over primes in an arithmetic progression. The key insight is that this sum grows approximately as $\frac{\log x}{\phi(d)}$, where $x$ is the upper limit of summation and $\phi(d)$ is Euler's totient function.

Rather than constructing primes directly (as in Euclid's classic proof), this approach uses the distribution of primes to establish their infinitude, demonstrating the power of analytic methods in number theory.

### Dependencies
- `DIRICHLET_STRONG`: States that for coprime $k$ and $d$ with $1 \leq d$, there exists a positive constant $B$ such that the difference between the sum of $\frac{\log p}{p}$ over primes $p \leq x$ with $p \equiv k \pmod{d}$ and $\frac{\log x}{\phi(d)}$ is bounded by $B$ for all $x$.
- `UPPER_BOUND_FINITE_SET`: A general theorem about the existence of upper bounds for finite sets.
- `EXP_LOG`: States that $\exp(\log x) = x$ for positive real $x$.
- `REAL_EXP_MONO_LE`: States that $\exp(x) \leq \exp(y)$ if and only if $x \leq y$.
- `PHI_LOWERBOUND_1_STRONG`: States a lower bound for Euler's totient function $\phi(d)$.

### Porting notes
When porting this theorem:
1. You'll need a solid library for number theory, including Euler's totient function $\phi$ and the concept of congruence modulo $d$.
2. The proof relies crucially on `DIRICHLET_STRONG`, which is a deep result about the distribution of primes in arithmetic progressions. In other systems, you might need to port this result first or find an equivalent statement.
3. The exponential and logarithmic functions are used extensively in the proof, so make sure your system has good support for real analysis.
4. The proof uses a contradiction argument with the `INFINITE` predicate - ensure your system has an equivalent concept.
5. Some of the arithmetic reasoning might require specialized tactics in other proof assistants.

---

