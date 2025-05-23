# perfect.ml

## Overview

Number of statements: 18

The `perfect.ml` file formalizes theorems related to perfect numbers in number theory, building on the prime number theory developed in the `prime.ml` library. It likely contains the definition of perfect numbers (where a number equals the sum of its proper divisors) and proves key properties and characterizations of such numbers. The file probably includes results related to the Euclid-Euler theorem connecting even perfect numbers with Mersenne primes.

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
The function $\sigma(n)$ is defined as:

$$\sigma(n) = \begin{cases}
0 & \text{if}\ n = 0 \\
\sum_{d|n} d & \text{if}\ n \neq 0
\end{cases}$$

where the sum is taken over all divisors $d$ of $n$ (including 1 and $n$ itself).

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The sigma function, often denoted $\sigma(n)$, is a number-theoretic function that gives the sum of all positive divisors of a natural number $n$. This is a fundamental arithmetic function in number theory.

Some key properties and uses:
- For a prime number $p$, $\sigma(p) = p + 1$
- $\sigma$ is multiplicative for coprime arguments: if $\gcd(m,n) = 1$, then $\sigma(mn) = \sigma(m)\sigma(n)$
- It's closely related to perfect numbers: a number $n$ is perfect if $\sigma(n) = 2n$

The definition handles the edge case of $n = 0$ by setting $\sigma(0) = 0$, which is a conventional choice since the divisors of 0 are problematic to define in standard number theory.

### Dependencies
No dependencies are listed in the provided information.

### Porting notes
When porting this definition:
- Be careful with the handling of the special case for $n = 0$
- Ensure that the notion of divisibility is properly defined in the target system
- Check if the target system has a built-in sum operation over sets that can be used, or if you need to define such a summation explicitly

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
A number $n$ is **perfect** if and only if $n \neq 0$ and $\sigma(n) = 2n$, where $\sigma(n)$ represents the sum of all divisors of $n$ (including $n$ itself).

### Informal proof
This is a definition, not a theorem, so no proof is needed.

### Mathematical insight
A perfect number is a positive integer that equals the sum of its proper divisors (i.e., divisors excluding the number itself). The definition uses the sum-of-divisors function $\sigma(n)$, which includes $n$ itself, so a perfect number satisfies $\sigma(n) = 2n$.

Perfect numbers have been studied since ancient times and have connections to various areas of number theory. The first few perfect numbers are 6, 28, 496, and 8128. Euclid proved that if $2^p-1$ is prime (a Mersenne prime), then $2^{p-1}(2^p-1)$ is perfect. Euler later proved that all even perfect numbers must have this form.

It remains an open question whether any odd perfect numbers exist.

### Dependencies
This definition depends on the `sigma` function, which computes the sum of all divisors of a number.

### Porting notes
When porting this definition, ensure that:
1. The `sigma` function is correctly implemented as the sum of all divisors
2. The definition maintains the non-zero condition, which excludes 0 from being considered perfect

---

## ODD_POW2_MINUS1

### Name of formal statement
ODD_POW2_MINUS1

### Type of the formal statement
theorem

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
For all natural numbers $k$, if $k \neq 0$, then $2^k - 1$ is odd.

### Informal proof
To prove that $2^k - 1$ is odd when $k \neq 0$, we proceed as follows:

* First, we establish that $\text{EVEN}(2^k)$ if and only if $\text{EVEN}((2^k - 1) + 1)$.
  - This is true because $(2^k - 1) + 1 = 2^k$ when $k \neq 0$ (via `ARITH_RULE`).
  - The condition $k \neq 0$ ensures that $2^k \neq 0$, so the subtraction is valid.

* Then, we use the known fact that $2^k$ is always even when $k \neq 0$.
  - Therefore $(2^k - 1) + 1$ must be even.
  - By the parity properties of addition, if a number plus 1 is even, then the number itself must be odd.
  - Thus, $2^k - 1$ is odd.

The proof uses the relationship between even and odd numbers, specifically that:
- $\text{ODD}(n) \iff \lnot\text{EVEN}(n)$
- If $n+1$ is even, then $n$ is odd

### Mathematical insight
This is a fundamental property in number theory: numbers of the form $2^k - 1$ (when $k > 0$) are always odd. These numbers are of particular interest as they include the Mersenne numbers, some of which are prime (Mersenne primes). The property is also useful in many number-theoretic proofs and in computer science applications like binary representation and bit manipulation.

The key insight is that any power of 2 is always even (except $2^0 = 1$), and subtracting 1 from an even number always yields an odd number.

### Dependencies
#### Definitions
- `ODD`, `EVEN`: Predicates for odd and even numbers
- `EXP`: Exponentiation operator

#### Theorems
- `EVEN_EXP`: Theorem about evenness of exponentiation
- `EVEN_ADD`: Properties of even numbers under addition
- `NOT_EVEN`: Relationship between even and odd numbers
- `EXP_EQ_0`: Conditions for when exponentiation equals zero

### Porting notes
When porting this theorem:
- Ensure that the evenness and oddness predicates are properly defined in the target system
- The proof relies on arithmetic simplifications that might need different tactics in other systems
- The relationship between ODD and EVEN (as negation) should be established

---

## EVEN_ODD_DECOMP

### Name of formal statement
EVEN_ODD_DECOMP

### Type of the formal statement
theorem

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
    REWRITE_TAC[EXP; MULT_CLAUSES] THEN MESON_TAC[]]);;
```

### Informal statement
For any natural number $n \neq 0$, there exist natural numbers $r$ and $s$ such that $s$ is odd and $n = 2^r \cdot s$.

### Informal proof
This theorem establishes that any non-zero natural number can be uniquely decomposed into a power of 2 multiplied by an odd number.

The proof uses well-founded induction on natural numbers and proceeds by case analysis:

* We start with well-founded induction on $n$.
* For any natural number $n$, we know by `EVEN_OR_ODD` that $n$ is either even or odd.
* For the case where $n$ is even:
  * There exists $m$ such that $n = 2m$.
  * We apply the induction hypothesis to $m$, noting that $m < n$ (provided $m \neq 0$).
  * If $m = 0$, then $n = 0$, contradicting our assumption that $n \neq 0$.
  * Thus $m \neq 0$, and by induction, there exist $r'$ and $s$ such that $s$ is odd and $m = 2^{r'} \cdot s$.
  * We let $r = r' + 1$, giving $n = 2m = 2 \cdot 2^{r'} \cdot s = 2^r \cdot s$.

* For the case where $n$ is odd:
  * We choose $r = 0$ and $s = n$.
  * This gives $n = 2^0 \cdot s = 1 \cdot n = n$, and $s$ is odd as required.

### Mathematical insight
This theorem establishes the fundamental decomposition of natural numbers into a power of 2 multiplied by an odd number. This is known as the "odd-even decomposition" or sometimes the "2-adic valuation" of a number. It's a special case of the more general concept that any integer can be written uniquely as a product of a power of a prime and a number not divisible by that prime.

This decomposition is crucial in number theory and has applications in:
- Understanding divisibility properties of numbers
- Algorithms like the Fast Fourier Transform (FFT)
- Addressing binary representation of numbers
- Number-theoretic constructions and proofs

The result can be generalized to decompose a number as $p^r \cdot m$ where $p$ is a prime and $p$ does not divide $m$.

### Dependencies
#### Theorems
- `num_WF`: Well-founded induction principle for natural numbers
- `EVEN_OR_ODD`: Every natural number is either even or odd
- `EVEN_EXISTS`: Definition of evenness in terms of existence of a multiplier
- `ODD_EXISTS`: Definition of oddness in terms of existence of a multiplier
- `MULT_EQ_0`: Conditions for when a product equals zero
- `ARITH`: Various basic arithmetic facts
- `ARITH_RULE`: Tactics for arithmetic simplification

### Porting notes
When porting this proof:
- Ensure the target system has appropriate induction principles for natural numbers
- Check how the target system defines even/odd numbers
- The proof relies on rewriting and case analysis, which should be available in most systems
- The exponential notation `2 EXP r` in HOL Light corresponds to $2^r$ in standard notation

---

## FINITE_DIVISORS

### Name of formal statement
FINITE_DIVISORS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE]);;
```

### Informal statement
For any natural number $n \neq 0$, the set of divisors $\{d \mid d \text{ divides } n\}$ is finite.

### Informal proof
The proof shows that the set of divisors of $n$ is finite by demonstrating that it is a subset of a known finite set.

* We start with applying the theorem `FINITE_SUBSET`, which states that any subset of a finite set is finite.
* We choose $\{d \mid d \leq n\}$ as our finite superset, which is the set of all natural numbers less than or equal to $n$.
* The set $\{d \mid d \leq n\}$ is finite by the theorem `FINITE_NUMSEG_LE`.
* We then show that $\{d \mid d \text{ divides } n\}$ is a subset of $\{d \mid d \leq n\}$.
* This follows from the theorem `DIVIDES_LE`, which states that if $d$ divides $n$ and $n \neq 0$, then $d \leq n$.

Therefore, the set of divisors of any non-zero natural number $n$ is finite.

### Mathematical insight
This theorem establishes the basic number theory fact that any non-zero natural number has only finitely many divisors. This is foundational for many results in number theory and is essential for algorithms that need to enumerate or count divisors.

The finiteness property is critical for induction arguments on the divisors of a number and for proving theorems about arithmetic functions related to divisors (such as the divisor count function or the sum of divisors function).

The key insight is that all divisors of $n$ (except 0, which isn't a divisor of any number) are bounded above by $n$ itself, which immediately restricts them to a finite set.

### Dependencies
- `FINITE_SUBSET` - Theorem stating that any subset of a finite set is finite
- `FINITE_NUMSEG_LE` - Theorem stating that the set of numbers less than or equal to n is finite
- `DIVIDES_LE` - Theorem stating that if d divides n and n ≠ 0, then d ≤ n

### Porting notes
When porting this theorem:
- Ensure the target system has a well-defined divisibility relation
- The notion of finiteness should be defined for sets
- The theorem about subsets of finite sets being finite is typically available in most proof assistants
- Make sure the target system has a theorem corresponding to `DIVIDES_LE`, which is a basic property of divisibility

---

## MULT_EQ_COPRIME

### Name of formal statement
MULT_EQ_COPRIME

### Type of the formal statement
theorem

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
  REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For all natural numbers $a$, $b$, $x$, and $y$, if $a \cdot b = x \cdot y$ and $\gcd(a, x) = 1$ (i.e., $a$ and $x$ are coprime), then there exists a natural number $d$ such that $y = a \cdot d$ and $b = x \cdot d$.

### Informal proof
The proof proceeds as follows:

1. We apply `COPRIME_DIVPROD` with the instantiation $d=a$, $a=x$, $b=y$. This theorem states that if $d$ divides $a \cdot b$ and $\gcd(d, a) = 1$, then $d$ divides $b$.
   
2. We also apply `COPRIME_DIVPROD` with the instantiation $d=x$, $a=a$, $b=b$. 

3. For each application, we need to prove the antecedents:
   - We show that $a$ divides $x \cdot y$ and $\gcd(a, x) = 1$ using:
     * `DIVIDES_REFL`: $a$ divides $a$
     * `DIVIDES_RMUL`: If $d$ divides $a$, then $d$ divides $a \cdot x$
     * `COPRIME_SYM`: $\gcd(a, b) = 1 \Leftrightarrow \gcd(b, a) = 1$
     * The assumption that $a \cdot b = x \cdot y$, which implies $a$ divides $x \cdot y$
   
   - Similarly, we show that $x$ divides $a \cdot b$ and $\gcd(x, a) = 1$

4. After establishing that $a$ divides $y$ and $x$ divides $b$, we rewrite these division statements as:
   - $y = a \cdot u$ for some natural number $u$
   - $b = x \cdot v$ for some natural number $v$

5. Substituting these into the original equation $a \cdot b = x \cdot y$:
   - $a \cdot (x \cdot v) = x \cdot (a \cdot u)$
   - $(a \cdot x) \cdot v = (a \cdot x) \cdot u$

6. Since multiplication is commutative and $a \cdot x \neq 0$ (because $a$ and $x$ are coprime), we can cancel $a \cdot x$ from both sides to conclude that $u = v$.

7. Define $d = u = v$, and we have $y = a \cdot d$ and $b = x \cdot d$ as required.

### Mathematical insight
This theorem provides a fundamental property about factorizations of natural numbers when certain factors are coprime. It states that if two products $a \cdot b$ and $x \cdot y$ are equal, and the factors $a$ and $x$ are coprime, then there must be a common factor $d$ such that $y$ is divisible by $a$ with quotient $d$, and $b$ is divisible by $x$ with the same quotient $d$.

This result is useful in number theory and can be seen as a special case of the unique factorization property. It demonstrates how the coprimality condition forces a specific structure on the factorizations. The theorem is particularly relevant when analyzing divisibility relationships in Diophantine equations and other number-theoretic problems.

### Dependencies
- **Divisibility theorems**:
  - `DIVIDES_REFL`: For all $x$, $x$ divides $x$
  - `DIVIDES_RMUL`: For all $d$, $a$, $x$, if $d$ divides $a$, then $d$ divides $a \cdot x$
  
- **Coprimality theorems**:
  - `COPRIME_SYM`: For all $a$, $b$, $\gcd(a, b) = 1 \Leftrightarrow \gcd(b, a) = 1$
  - `COPRIME_DIVPROD`: For all $d$, $a$, $b$, if $d$ divides $a \cdot b$ and $\gcd(d, a) = 1$, then $d$ divides $b$

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate definitions for divisibility and coprimality.
2. The proof relies on the cancellation property for multiplication, which might need explicit handling in some proof assistants.
3. The commutative property of multiplication is used implicitly in the HOL Light proof and may need explicit application in other systems.
4. The proof uses quite a bit of automation through `ASM_MESON_TAC` - you may need to provide more explicit proof steps in systems with less powerful automation.

---

## COPRIME_ODD_POW2

### Name of formal statement
COPRIME_ODD_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COPRIME_ODD_POW2 = prove
 (`!k n. ODD(n) ==> coprime(2 EXP k,n)`,
  SIMP_TAC[coprime; PRIME_2; DIVIDES_PRIMEPOW] THEN REWRITE_TAC[divides] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ODD_MULT; ODD_EXP; ARITH]);;
```

### Informal statement
For all natural numbers $k$ and $n$, if $n$ is odd, then $2^k$ and $n$ are coprime.

Formally: $\forall k, n. \text{ODD}(n) \Rightarrow \text{coprime}(2^k, n)$

### Informal proof
The proof shows that any odd number $n$ is coprime to any power of 2.

- Begin by simplifying using the definition of coprime: two numbers are coprime if they have no common divisors other than 1.
- Using the fact that 2 is prime (`PRIME_2`) and a property of divisors of prime powers (`DIVIDES_PRIMEPOW`): if $p$ is prime, then $d$ divides $p^k$ if and only if $d = p^i$ for some $i \leq k$.
- Rewrite using the definition of "divides": $a$ divides $b$ means there exists some $c$ such that $b = a \times c$.
- For contradiction, assume that $n$ and $2^k$ have a common divisor $d > 1$. By the above properties, this divisor must be $2^i$ for some $i \leq k$.
- This implies $n = 2^i \cdot c$ for some $c$.
- But this contradicts the assumption that $n$ is odd, since:
  - Multiplication by an odd number preserves oddness/evenness (`ODD_MULT`)
  - Any power of 2 greater than $2^0$ is even (`ODD_EXP`)
  - Basic arithmetic facts (`ARITH`)

Therefore, $2^k$ and $n$ must be coprime when $n$ is odd.

### Mathematical insight
This theorem captures the fundamental property that powers of 2 share no common factors with odd numbers. This is because odd numbers, by definition, are not divisible by 2, while powers of 2 are divisible only by smaller powers of 2.

The result is particularly useful in number theory, particularly when dealing with congruences, as it guarantees that odd numbers are invertible modulo powers of 2. It's also relevant in algorithmic contexts like the Chinese remainder theorem and various cryptographic applications.

### Dependencies
#### Theorems
- `PRIME_2`: The number 2 is prime.
- `DIVIDES_PRIMEPOW`: For a prime number p and any divisor d, d divides p^k if and only if d = p^i for some i ≤ k.

#### Definitions used
- `coprime`: Two numbers are coprime if their greatest common divisor is 1.
- `ODD`: A number is odd if it leaves remainder 1 when divided by 2.
- `divides`: One number divides another if the remainder is 0.

### Porting notes
When porting this theorem to another proof assistant:
- The proof relies heavily on properties of odd numbers and powers of 2, which should be available in most standard libraries.
- The key insight is leveraging the primality of 2 and characterization of divisors of prime powers.
- Make sure the target system has appropriate automation for arithmetic reasoning, similar to HOL Light's `ARITH_TAC`.

---

## MULT_NSUM

I'll revise the documentation to make the informal statement more faithful to the formal content by removing the unnecessary restriction on the codomain of functions f and g.

### Name of formal statement
MULT_NSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULT_NSUM = prove
 (`!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))`,
  SIMP_TAC[GSYM NSUM_NSUM_PRODUCT; NSUM_LMUL; NSUM_RMUL]);;
```

### Informal statement
For finite sets $s$ and $t$, the product of the sum of a function $f$ over $s$ and the sum of a function $g$ over $t$ is equal to the sum of the product of $f(x)$ and $g(y)$ over all pairs $(x,y)$ where $x \in s$ and $y \in t$. Formally:

$$\forall s,t. \text{FINITE}(s) \land \text{FINITE}(t) \Rightarrow \sum_{x \in s}f(x) \cdot \sum_{y \in t}g(y) = \sum_{(x,y) \in \{(x,y) \mid x \in s \land y \in t\}}f(x) \cdot g(y)$$

where $f$ is a function from type $A$ to an appropriate numeric type that supports summation, and $g$ is a function from type $B$ to a compatible numeric type.

### Informal proof
The proof follows directly by applying three theorems:

1. First, we use `NSUM_NSUM_PRODUCT`, which relates the sum over a Cartesian product to iterated sums.
2. Then we use `NSUM_LMUL` and `NSUM_RMUL`, which are theorems about distributing multiplication over sums.

The simplification tactic `SIMP_TAC` applies these theorems to transform the left-hand side into the right-hand side of the equation.

### Mathematical insight
This theorem expresses a fundamental property of sums and products: the product of two sums can be rewritten as a sum of products over all pairs from the original sets. This is essentially a discrete version of Fubini's theorem, allowing us to interchange the order of summation.

This result is important for manipulating expressions involving sums and products in discrete mathematics, combinatorics, and probability theory. It's particularly useful when working with generating functions, counting problems, and expected value calculations.

### Dependencies
- `NSUM_NSUM_PRODUCT` - Theorem relating sums over Cartesian products to iterated sums
- `NSUM_LMUL` - Theorem about distributing multiplication on the left over a sum
- `NSUM_RMUL` - Theorem about distributing multiplication on the right over a sum

### Porting notes
When porting to other systems:
- Ensure the target system has appropriate definitions for finite sets and summation over finite sets.
- The theorem requires appropriate numeric types that support summation and multiplication.
- The representation of the Cartesian product might differ slightly between systems.

---

## SIGMA_0

### Name of formal statement
SIGMA_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_0 = prove
 (`sigma 0 = 0`,
  REWRITE_TAC[sigma]);;
```

### Informal statement
The summation of divisors function $\sigma$ applied to $0$ equals $0$, i.e., $\sigma(0) = 0$.

### Informal proof
The proof is straightforward by rewriting the definition of the $\sigma$ function.

In number theory, the $\sigma$ function (also known as the divisor function) is typically defined as the sum of all positive divisors of a natural number. However, for the special case of $0$, there are no positive divisors, so the sum is $0$ by convention.

The theorem is proven by directly expanding the definition of $\sigma$ and simplifying.

### Mathematical insight
This theorem establishes the base case for the $\sigma$ function. It's important to explicitly define $\sigma(0)$ since $0$ is a special case with no positive divisors. In number-theoretic functions, the behavior at $0$ often requires special handling.

The result is consistent with the general understanding of the divisor function in number theory, where $\sigma(0)$ is conventionally defined to be $0$ since $0$ has no positive divisors to sum.

### Dependencies
- `sigma` - Definition of the divisor summation function

### Porting notes
When porting to other proof assistants, ensure that the definition of the sigma function handles the case of $0$ properly. Different systems might have different conventions for this edge case, so it's worth checking how the sigma function is defined in the target system.

---

## SIGMA_1

### SIGMA_1
- `SIGMA_1`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SIGMA_1 = prove
 (`sigma(1) = 1`,
  REWRITE_TAC[sigma; DIVIDES_ONE; SET_RULE `{d | d = 1} = {1}`] THEN
  REWRITE_TAC[ARITH; NSUM_SING]);;
```

### Informal statement
The theorem states that $\sigma(1) = 1$, where $\sigma(n)$ is the sum-of-divisors function.

### Informal proof
The proof proceeds by:
- Using the definition of the sum-of-divisors function $\sigma$, which is the sum of all positive divisors of a number
- Applying the fact that the only divisor of 1 is itself, i.e., $\{d \mid d \text{ divides } 1\} = \{1\}$
- Computing the sum over the singleton set $\{1\}$, which is just 1

More specifically:
1. Rewrite using the definition of $\sigma$ and the fact that only 1 divides 1
2. Use set theory to express that $\{d \mid d = 1\} = \{1\}$
3. Apply arithmetic simplification and the property that the sum over a singleton set equals its only element

### Mathematical insight
This is a fundamental property of the sum-of-divisors function: $\sigma(1) = 1$ because 1 is the only divisor of 1. While simple, it serves as a base case when studying properties of this function. The sum-of-divisors function is important in number theory, particularly in the study of perfect numbers and divisibility properties.

### Dependencies
- Definitions:
  - `sigma` - the sum-of-divisors function
  - `DIVIDES_ONE` - theorem about divisors of 1
  - `SET_RULE` - set theory simplification
  - `ARITH` - arithmetic simplification
  - `NSUM_SING` - theorem about summation over singleton sets

---

## SIGMA_LBOUND

### SIGMA_LBOUND

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
    MESON_TAC[DIVIDES_1; DIVIDES_REFL]]);;
```

### Informal statement
For all natural numbers $n$, if $1 < n$, then $n + 1 \leq \sigma(n)$, where $\sigma(n)$ is the sum of all divisors of $n$.

### Informal proof
We prove that if $1 < n$, then $n + 1 \leq \sigma(n)$.

- First, we note that if $1 < n$, then $n \neq 0$.
- By definition, $\sigma(n)$ is the sum of all divisors of $n$.
- We use a transitive inequality by showing that $n + 1 \leq \sum_{i \in \{1,n\}} i \leq \sigma(n)$.
- For the first inequality:
  - $\sum_{i \in \{1,n\}} i = 1 + n$, so $n + 1 \leq \sum_{i \in \{1,n\}} i$ holds trivially.
- For the second inequality:
  - We show that $\{1,n\} \subseteq \text{divisors}(n)$ since:
    - $1$ divides $n$ (by `DIVIDES_1`)
    - $n$ divides $n$ (by `DIVIDES_REFL`)
  - Since all elements in the sum are positive, and $\{1,n\} \subseteq \text{divisors}(n)$, we have $\sum_{i \in \{1,n\}} i \leq \sum_{i \in \text{divisors}(n)} i = \sigma(n)$.
- Combining these inequalities, we get $n + 1 \leq \sigma(n)$.

### Mathematical insight
This theorem establishes a lower bound for the sum of divisors function $\sigma(n)$. The insight is that any number $n > 1$ has at least two divisors (1 and itself), and their sum is at least $n+1$. This is a fundamental property that helps establish the growth rate of the sigma function.

The result is tight for prime numbers, where $\sigma(p) = p + 1$ since a prime has exactly two divisors: 1 and itself. For composite numbers, the inequality is strict because there are additional divisors.

This lower bound is useful in number theory, particularly in studying arithmetic functions and their properties.

### Dependencies
#### Theorems
- `DIVIDES_1`: For all natural numbers $x$, $1$ divides $x$.
- `DIVIDES_REFL`: For all natural numbers $x$, $x$ divides $x$.

#### Other
- `sigma`: The definition of the sum of divisors function.
- Various arithmetic and set-theoretic tactics and theorems in HOL Light.

### Porting notes
When porting this theorem:
- Ensure the `sigma` function is properly defined as the sum of all divisors.
- The proof relies on basic properties of divisibility and finite sums.
- The transitivity of inequalities and subset reasoning are standard techniques that should be available in any proof assistant.

---

## SIGMA_MULT

### Name of formal statement
SIGMA_MULT

### Type of the formal statement
theorem

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
    MESON_TAC[DIVIDES_1; DIVIDES_REFL; DIVIDES_LMUL]]);;
```

### Informal statement
Let $a$ and $b$ be integers greater than 1. Then:

$$1 + b + a \cdot b \leq \sigma(a \cdot b)$$

where $\sigma(n)$ is the sum of all divisors of $n$.

### Informal proof
The proof establishes that for integers $a$ and $b$ where $a > 1$ and $b > 1$, the sum of certain divisors of $a \cdot b$ is at least $1 + b + a \cdot b$.

- First, we deduce that $a \neq 0$ and $b \neq 0$ from $a > 1$ and $b > 1$.

- We then establish that $1 + b + a \cdot b \leq \sum_{i \in \{1,b,a \cdot b\}} i$.
  * This is computed directly: $1 + b + a \cdot b = \sum_{i \in \{1,b,a \cdot b\}} i$, assuming the set contains distinct elements.
  * We confirm the elements are distinct:
    - $1 \neq b$ since $b > 1$
    - $1 \neq a \cdot b$ since $a \cdot b = 1 \cdot x$ would imply $a = 1$ (using $b \neq 0$), contradicting $a > 1$
    - $b \neq a \cdot b$ since this would imply $a = 1$, contradicting $a > 1$

- Next, we show that $\sum_{i \in \{1,b,a \cdot b\}} i \leq \sigma(a \cdot b)$.
  * We demonstrate that $\{1, b, a \cdot b\} \subseteq \{d : d \text{ divides } a \cdot b\}$:
    - $1$ divides $a \cdot b$ (using `DIVIDES_1`)
    - $b$ divides $a \cdot b$ (since $a \cdot b = b \cdot a$)
    - $a \cdot b$ divides $a \cdot b$ (using `DIVIDES_REFL`)
  * Since all elements in our set are divisors of $a \cdot b$, their sum is at most $\sigma(a \cdot b)$.

- By transitivity of $\leq$, we conclude that $1 + b + a \cdot b \leq \sigma(a \cdot b)$.

### Mathematical insight
This theorem provides a lower bound for the sum of divisors function $\sigma(n)$ when $n$ is a product of two integers greater than 1. The key insight is that we can identify certain specific divisors of $a \cdot b$ (namely 1, $b$, and $a \cdot b$ itself) and show that their sum provides a lower bound.

The sum of divisors function $\sigma(n)$ is important in number theory, particularly in the study of perfect numbers and related concepts. This specific inequality may be useful in establishing bounds or properties related to composite numbers.

### Dependencies
- Theorems:
  - `DIVIDES_1`: For all $x$, 1 divides $x$
  - `DIVIDES_REFL`: For all $x$, $x$ divides $x$

### Porting notes
When porting this theorem:
- Ensure that the sum of divisors function $\sigma(n)$ is properly defined in the target system.
- The proof relies on arithmetic simplification and basic properties of divisibility which should be available in most proof assistants.
- The subset reasoning with finite sets and summation may require different tactics in other systems, but the mathematical argument remains the same.

---

## SIGMA_PRIME

### Name of formal statement
SIGMA_PRIME

### Type of the formal statement
theorem

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
    ARITH_TAC]);;
```

### Informal statement
For any prime number $p$, the sum of divisors function satisfies $\sigma(p) = p + 1$.

### Informal proof
We prove that for any prime number $p$, $\sigma(p) = p + 1$.

1. First, we handle special cases:
   - If $p = 0$, then $p$ is not prime (by `PRIME_0`), making the implication trivially true.
   - If $p = 1$, then $p$ is not prime (by `PRIME_1`), making the implication trivially true.

2. For a prime number $p > 1$, we must show that $\sigma(p) = p + 1$:
   - By definition, $\sigma(p)$ is the sum of all divisors of $p$
   - For a prime number $p$, the only divisors are 1 and $p$ itself
   - Therefore, we need to show that $\sigma(p) = \sum_{i \in \{1,p\}} i = 1 + p$

3. We rewrite $\sigma(p)$ as $\sum_{i \in \{1,p\}} i$ by proving that the set of divisors of $p$ is exactly $\{1,p\}$:
   - We use the definition of primality: a number $p > 1$ is prime if its only divisors are 1 and itself
   - We use `DIVIDES_1` (stating that 1 divides any number) and `DIVIDES_REFL` (stating that any number divides itself)

4. Finally, we evaluate the sum $\sum_{i \in \{1,p\}} i = 1 + p$ using the properties of finite sums.

### Mathematical insight
This theorem captures a fundamental property of the sum of divisors function for prime numbers. It shows that for any prime $p$, $\sigma(p)$ is exactly $p + 1$ because a prime number has exactly two divisors: 1 and itself. This result is important in number theory and is used in the study of perfect numbers, abundant numbers, and deficient numbers. It also forms the basis for more complex results about the behavior of the $\sigma$ function for composite numbers through its multiplicative properties.

### Dependencies
#### Theorems
- `PRIME_0`: Establishes that 0 is not prime
- `PRIME_1`: Establishes that 1 is not prime
- `DIVIDES_1`: States that 1 divides every number
- `DIVIDES_REFL`: States that every number divides itself
- `SIGMA_0`: (Implied) Property of the sigma function at 0
- `SIGMA_1`: (Implied) Property of the sigma function at 1

#### Definitions
- `prime`: Definition of primality
- `sigma`: Sum of divisors function

### Porting notes
When porting this theorem:
1. Ensure that your system has a properly defined sum of divisors function ($\sigma$)
2. The proof relies on basic number theory facts about primes and divisibility
3. The set-theoretic approach used to represent divisors may need adaptation depending on how the target system models sets and sums over sets

---

## SIGMA_PRIME_EQ

### SIGMA_PRIME_EQ

### Type of the formal statement
- theorem

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
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ARITH_TAC);;
```

### Informal statement
The theorem states that a natural number $p$ is prime if and only if $\sigma(p) = p + 1$, where $\sigma(n)$ is the sum of all divisors of $n$ (including 1 and $n$ itself).

### Informal proof
The proof proceeds by establishing both directions of the equivalence:

* **($\Rightarrow$)**: If $p$ is prime, then $\sigma(p) = p + 1$.
  - This direction is directly handled by applying the theorem `SIGMA_PRIME`.

* **($\Leftarrow$)**: If $\sigma(p) = p + 1$, then $p$ is prime.
  - This direction is proven by contraposition: assume $p$ is not prime.
  - We rewrite the definition of primality and apply De Morgan's laws.
  - Case analysis:
    - Case $p = 1$: We have $\sigma(1) = 1 \neq 1 + 1$, so the property doesn't hold.
    - Case $p > 1$ and not prime: Then $p$ can be written as $p = a \cdot b$ for some $a, b$ where $1 < a < p$ and $1 < b < p$.
    - Using `SIGMA_MULT`, we have $\sigma(p) = \sigma(a \cdot b) = \sigma(a) \cdot \sigma(b)$.
    - Considering cases where $a = 0$ or $b = 0$, which are trivially handled.
    - For positive $a$ and $b$, we know that if $a \cdot b = p$ with $a, b > 1$, then $\sigma(a) \geq a + 1$ and $\sigma(b) \geq b + 1$.
    - This means $\sigma(p) = \sigma(a) \cdot \sigma(b) \geq (a + 1) \cdot (b + 1) = a \cdot b + a + b + 1 = p + a + b + 1 > p + 1$
    - Therefore, when $p$ is not prime, $\sigma(p) \neq p + 1$.

### Mathematical insight
This theorem provides a characterization of prime numbers in terms of the sum of divisors function $\sigma$. It effectively states that a number is prime precisely when the sum of all its divisors is exactly one more than the number itself.

The intuition is clear: for a prime number $p$, the only divisors are 1 and $p$ itself, so $\sigma(p) = 1 + p$. Conversely, if a number has any additional divisors beyond 1 and itself, the sum will necessarily exceed $p + 1$.

This is a classic number-theoretic result that connects the concept of primality with the arithmetic function $\sigma$, providing an alternate characterization of prime numbers.

### Dependencies
- `SIGMA_PRIME`: This theorem likely states that if $p$ is prime, then $\sigma(p) = p + 1$.
- `SIGMA_MULT`: This theorem likely states that $\sigma(a \cdot b) = \sigma(a) \cdot \sigma(b)$ when $a$ and $b$ are coprime.
- `SIGMA_0`: Likely states that $\sigma(0) = 0$.
- `SIGMA_1`: Likely states that $\sigma(1) = 1$.

### Porting notes
When porting this theorem:
1. Ensure your system has a definition of the sigma function that sums all divisors of a number.
2. Make sure the basic properties of $\sigma$ (like `SIGMA_MULT`, `SIGMA_0`, `SIGMA_1`) are already proven.
3. The case analysis approach used here is common across proof assistants, but the specific tactics may vary.
4. The arithmetic reasoning at the end might require different tactics in other systems.

---

## SIGMA_POW2

### Name of formal statement
SIGMA_POW2

### Type of formal statement
theorem

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
  REWRITE_TAC[EXP; EXP_ADD; ARITH] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $k$, the sum of all divisors of $2^k$ is equal to $2^{k+1} - 1$.

Formally:
$$\forall k \in \mathbb{N}, \sigma(2^k) = 2^{k+1} - 1$$

where $\sigma(n)$ represents the sum of all positive divisors of $n$.

### Informal proof
The proof starts by applying the definition of $\sigma$ and simplifying:

- First, we rewrite using the definition of $\sigma(n)$ as the sum of all divisors of $n$.
- Since $2$ is prime, we can use the theorem `DIVIDES_PRIMEPOW` which states that for a prime number $p$, the divisors of $p^k$ are exactly the powers $p^i$ for $0 \leq i \leq k$.
- Therefore, the divisors of $2^k$ are exactly $\{2^i \mid 0 \leq i \leq k\}$.
- So $\sigma(2^k) = \sum_{i=0}^{k} 2^i$.

The proof then proceeds to show that $\sum_{i=0}^{k} 2^i = 2^{k+1} - 1$ by induction on $k$:

- Base case ($k = 0$): $\sigma(2^0) = \sigma(1) = 1 = 2^{0+1} - 1 = 2 - 1 = 1$.
- Inductive step: Assume $\sum_{i=0}^{k} 2^i = 2^{k+1} - 1$.
  - We need to prove $\sum_{i=0}^{k+1} 2^i = 2^{(k+1)+1} - 1 = 2^{k+2} - 1$.
  - By splitting the sum: $\sum_{i=0}^{k+1} 2^i = \sum_{i=0}^{k} 2^i + 2^{k+1}$
  - Substituting the induction hypothesis: $\sum_{i=0}^{k+1} 2^i = (2^{k+1} - 1) + 2^{k+1} = 2 \cdot 2^{k+1} - 1 = 2^{k+2} - 1$

This completes the proof.

### Mathematical insight
This theorem gives a closed-form expression for the sum of divisors function $\sigma(n)$ when $n$ is a power of 2. The result is part of a more general pattern: for any prime $p$, $\sigma(p^k) = \frac{p^{k+1} - 1}{p - 1}$. In the special case where $p = 2$, this simplifies to $2^{k+1} - 1$.

The result is also related to geometric series, as the sum of divisors of $2^k$ equals the sum $1 + 2 + 2^2 + ... + 2^k$, which is a geometric series with first term $a = 1$ and common ratio $r = 2$. The closed form for this sum is $\frac{a(1-r^{n+1})}{1-r} = \frac{1-2^{k+1}}{1-2} = 2^{k+1} - 1$.

### Dependencies
#### Theorems
- `PRIME_2`: The theorem stating that 2 is a prime number
- `DIVIDES_PRIMEPOW`: For a prime $p$, $d$ divides $p^k$ if and only if $d = p^i$ for some $i \leq k$

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition of the sigma function ($\sigma$) as the sum of all divisors.
2. The proof relies on properties of geometric series and divisibility of prime powers, so ensure these are available.
3. The induction on $k$ is straightforward and should translate well to other proof assistants.

---

## SIGMA_MULTIPLICATIVE

### Name of formal statement
SIGMA_MULTIPLICATIVE

### Type of the formal statement
theorem

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
                DIVIDES_RMUL; DIVIDES_REFL; MULT_SYM]);;
```

### Informal statement
For any natural numbers $a$ and $b$, if $a$ and $b$ are coprime (i.e., their greatest common divisor is 1), then 
$$\sigma(a \cdot b) = \sigma(a) \cdot \sigma(b)$$

Here, $\sigma(n)$ is the sum of divisors function, which computes the sum of all positive divisors of $n$.

### Informal proof
The proof establishes that the sigma function is multiplicative when applied to coprime arguments. The key steps are:

- First, handle the edge cases where $a = 0$ or $b = 0$ using the fact that $\sigma(0) = 0$ and $0 \cdot x = 0$ for any $x$.

- For the main case where $a, b \neq 0$ and $\gcd(a,b) = 1$:
  * Expand the definition of $\sigma(a \cdot b)$ as the sum of all divisors of $a \cdot b$.
  * Rewrite the sum using the characterization of divisors of a product of coprime numbers.
  * Use the fact that any divisor $d$ of $a \cdot b$ can be uniquely written as $d = d_a \cdot d_b$ where $d_a|a$ and $d_b|b$.
  * This establishes a bijection between divisors of $a \cdot b$ and pairs of divisors $(d_a, d_b)$ where $d_a|a$ and $d_b|b$.
  * Show that each divisor $d$ in the sum for $\sigma(a \cdot b)$ corresponds uniquely to a product $d_a \cdot d_b$ where $d_a$ appears in $\sigma(a)$ and $d_b$ appears in $\sigma(b)$.
  * The bijection relies on the fact that for coprime numbers, if $d_1 \cdot d_2 = e_1 \cdot e_2$ where $d_1|a$, $d_2|b$, $e_1|a$, and $e_2|b$, then $d_1 = e_1$ and $d_2 = e_2$.
  * This uniqueness property follows from the coprime divisors theorem: if $a$ and $b$ are coprime, then any divisor of $a$ is coprime to any divisor of $b$.

- Therefore, $\sigma(a \cdot b) = \sum_{d|a}\sum_{e|b} d \cdot e = \left(\sum_{d|a} d\right) \cdot \left(\sum_{e|b} e\right) = \sigma(a) \cdot \sigma(b)$.

### Mathematical insight
The multiplicative property of the sigma function is one of its most significant properties in number theory. It states that for coprime numbers, the sum of divisors of their product equals the product of the sums of their divisors.

This property is crucial for calculating $\sigma$ values efficiently and is analogous to similar multiplicative properties of other number-theoretic functions like Euler's totient function or the number-of-divisors function. It allows us to compute $\sigma$ for any number once we know its prime factorization.

The proof essentially establishes a bijection between the divisors of $a \cdot b$ and pairs of divisors from $a$ and $b$ respectively, which is only guaranteed when $a$ and $b$ are coprime.

### Dependencies
- **Theorems**:
  - `DIVIDES_REFL`: For any $x$, $x$ divides $x$.
  - `DIVIDES_RMUL`: If $d$ divides $a$, then $d$ divides $a \cdot x$ for any $x$.
  - `COPRIME_SYM`: Coprimality is symmetric: $\gcd(a,b) = 1 \iff \gcd(b,a) = 1$.
  - `COPRIME_DIVPROD`: If $d$ divides $a \cdot b$ and $d$ is coprime to $a$, then $d$ divides $b$.
  - `COPRIME_DIVISORS`: If $d$ divides $a$, $e$ divides $b$, and $a,b$ are coprime, then $d,e$ are coprime.
  - `DIVISION_DECOMP`: If $a$ divides $b \cdot c$, then there exist $b'$ and $c'$ such that $a = b' \cdot c'$ with $b'$ dividing $b$ and $c'$ dividing $c$.

- **Definitions**:
  - `sigma`: The sum of divisors function.

### Porting notes
When porting this theorem:
1. Ensure your system has a compatible definition of the sigma function as the sum of all positive divisors.
2. The proof relies heavily on the properties of coprime numbers and divisibility, so these concepts should be well-developed.
3. The proof uses a bijection between divisor sets that might require different techniques in other proof assistants, especially those with different ways of handling finite sums or bijections.
4. The edge case handling for $a=0$ or $b=0$ should be carefully ported, as some systems might have different conventions for handling divisibility with zero.

---

## PERFECT_EUCLID

### PERFECT_EUCLID
- `PERFECT_EUCLID`

### Type of the formal statement
- theorem

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
  AP_TERM_TAC THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $k$, if $2^k - 1$ is prime, then $2^{k-1} \cdot (2^k - 1)$ is a perfect number.

Here, a perfect number is a positive integer that equals the sum of its proper divisors (i.e., all divisors excluding the number itself).

### Informal proof
The proof establishes Euclid's theorem on perfect numbers:

- First, we handle the base case: if $k = 0$, then $2^k - 1 = 0$, which is not prime (by `PRIME_0`), so the implication is vacuously true.

- For $k > 0$, we proceed as follows:
  
  - Show that $2^{k-1}$ and $2^k - 1$ are coprime:
    - This is proved by applying `COPRIME_ODD_POW2` and using the fact that $2^k - 1$ is odd (from `ODD_POW2_MINUS1`).
  
  - Apply properties of the $\sigma$ function (sum of divisors):
    - Use `SIGMA_MULTIPLICATIVE` to get $\sigma(2^{k-1} \cdot (2^k - 1)) = \sigma(2^{k-1}) \cdot \sigma(2^k - 1)$ since the two factors are coprime.
    - Use `SIGMA_PRIME` with the premise that $2^k - 1$ is prime, so $\sigma(2^k - 1) = 1 + (2^k - 1) = 2^k$.
    - Use `SIGMA_POW2` to get $\sigma(2^{k-1}) = 2^k - 1$.
  
  - Combine these results:
    - $\sigma(2^{k-1} \cdot (2^k - 1)) = \sigma(2^{k-1}) \cdot \sigma(2^k - 1) = (2^k - 1) \cdot 2^k$
    - Rearrange to show that $\sigma(2^{k-1} \cdot (2^k - 1)) = 2 \cdot 2^{k-1} \cdot (2^k - 1)$
    - This means $\sigma(n) = 2n$ where $n = 2^{k-1} \cdot (2^k - 1)$, which is exactly the condition for $n$ to be perfect.

### Mathematical insight
This theorem proves Euclid's famous result that numbers of the form $2^{k-1} \cdot (2^k - 1)$ are perfect whenever $2^k - 1$ is prime. Such primes are called Mersenne primes, and this connection between Mersenne primes and perfect numbers has been known since antiquity.

The theorem shows that every Mersenne prime generates a corresponding even perfect number. In fact, it was later proven by Euler that all even perfect numbers must have this form, establishing a one-to-one correspondence between Mersenne primes and even perfect numbers.

This result is foundational in number theory, particularly for the study of perfect numbers. To date, no odd perfect numbers have been discovered, and finding them (or proving their non-existence) remains an important open problem in mathematics.

### Dependencies
- Theorems:
  - `PRIME_0`: The number 0 is not prime
  - `COPRIME_ODD_POW2`: Relates to coprimality of powers of 2 and odd numbers
  - `ODD_POW2_MINUS1`: States that $2^k - 1$ is odd for any $k$
  - `SIGMA_MULTIPLICATIVE`: If $a$ and $b$ are coprime, then $\sigma(a \cdot b) = \sigma(a) \cdot \sigma(b)$
  - `SIGMA_PRIME`: For a prime $p$, $\sigma(p) = 1 + p$
  - `SIGMA_POW2`: Formula for the sum of divisors of powers of 2

### Porting notes
When porting this theorem:
- Ensure your system has a well-defined notion of the $\sigma$ function (sum of divisors)
- Verify that the definition of "perfect number" is consistent ($\sigma(n) = 2n$ or equivalently, sum of proper divisors equals the number)
- The proof relies heavily on properties of the $\sigma$ function with respect to prime numbers and powers of 2

---

## PERFECT_EULER

### PERFECT_EULER

### Type of formal statement
theorem

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
    REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC]);;
```

### Informal statement
For any even perfect number $n$, there exists a positive integer $k$ such that $2^k - 1$ is prime and $n = 2^{k-1} \cdot (2^k - 1)$.

### Informal proof
The proof establishes Euclid's characterization of even perfect numbers, showing that they must have the form $2^{k-1}(2^k-1)$ where $2^k-1$ is a Mersenne prime.

- First, we decompose the even number $n$ as $n = 2^r \cdot s$ where $s$ is odd.
- Since $n$ is perfect, we know that $\sigma(n) = 2n$, where $\sigma(n)$ is the sum of divisors function.
- Using the multiplicativity of $\sigma$ and the fact that $\sigma(2^r) = 2^{r+1} - 1$, we get:
  $$\sigma(n) = \sigma(2^r) \cdot \sigma(s) = (2^{r+1} - 1) \cdot \sigma(s) = 2n = 2 \cdot 2^r \cdot s = 2^{r+1} \cdot s$$
  
- This gives us the equation $(2^{r+1} - 1) \cdot \sigma(s) = 2^{r+1} \cdot s$
- Since $2^{r+1} - 1$ and $2^{r+1}$ are coprime (as one is odd and the other is even), we can infer that:
  - $2^{r+1} - 1$ divides $s$
  - $2^{r+1}$ divides $\sigma(s)$
  
- Let's write $s = (2^{r+1} - 1) \cdot d$ for some integer $d$
- Using the properties of $\sigma$ and substituting, we can determine that $d$ must equal 1
- Therefore, $s = 2^{r+1} - 1$ and $\sigma(s) = s + 1 = 2^{r+1}$
- The only way this happens is if $s$ is a prime number
- Setting $k = r + 1$, we get that $n = 2^{k-1} \cdot (2^k - 1)$ where $2^k - 1$ is prime

### Mathematical insight
This theorem establishes the famous result by Euclid (later completed by Euler) that characterizes even perfect numbers. A perfect number is one where the sum of its proper divisors equals the number itself.

This result shows that every even perfect number must have the form $2^{k-1}(2^k-1)$ where $2^k-1$ is prime (a Mersenne prime). Euler later proved the converse: all numbers of this form (where $2^k-1$ is prime) are perfect.

This is a fundamental result in number theory connecting perfect numbers with Mersenne primes. Even today, all known perfect numbers are even and have this exact form. Whether odd perfect numbers exist remains one of the oldest unsolved problems in mathematics.

### Dependencies
#### Theorems
- `COPRIME_SYM`: For any integers $a$ and $b$, $\text{coprime}(a,b) \iff \text{coprime}(b,a)$
- Other theorems used include `SIGMA_MULTIPLICATIVE`, `SIGMA_POW2`, `COPRIME_ODD_POW2`, `SIGMA_PRIME_EQ`, and various arithmetic properties

### Porting notes
When porting this proof, care should be taken with:
1. The definition of perfect numbers: a number whose sum of divisors equals twice the number
2. The properties of the sigma function (sum of divisors)
3. Number-theoretic properties about coprime numbers and the relationship between even and odd numbers

Most proof assistants would have similar theorems about divisibility and number theory, but the names and exact formulations may differ.

---

