# bernoulli.ml

## Overview

Number of statements: 16

This file formalizes Bernoulli numbers and Bernoulli polynomials, along with their properties and applications. It develops the theory needed for expressing and proving formulas for sums of powers of the form ∑(k^n) for natural numbers k. The implementation builds on binomial coefficients, analysis fundamentals, and transcendental functions. The file likely includes formulations of Faulhaber's formula and related results that connect Bernoulli numbers to power sums.

## SUM_DIFFS

### SUM_DIFFS
- `SUM_DIFFS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_DIFFS = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - a(m)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH; ADD_CLAUSES; REAL_SUB_REFL];
    SIMP_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ADD1] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; ARITH_RULE `~((n + 1) + 1 <= n + 1)`] THEN
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC]);;
```

### Informal statement
For all function $a$, and integers $m$ and $n$ such that $m \leq n + 1$, the sum of differences $\sum_{i=m}^{n} (a(i+1) - a(i))$ equals $a(n+1) - a(m)$.

Formally:
$$\forall a,m,n.\ m \leq n + 1 \Rightarrow \sum_{i=m}^{n} (a(i+1) - a(i)) = a(n+1) - a(m)$$

### Informal proof
The proof is by induction on $n$.

**Base case ($n = 0$)**: 
- When $n = 0$, we need to show $\sum_{i=m}^{0} (a(i+1) - a(i)) = a(1) - a(m)$ for $m \leq 1$
- Since $m \leq 1$, either $m = 0$ or $m = 1$:
  - If $m = 0$: $\sum_{i=0}^{0} (a(i+1) - a(i)) = a(1) - a(0)$, which is true by definition of sum
  - If $m = 1$: $\sum_{i=1}^{0} (a(i+1) - a(i))$ is an empty sum (since the range is invalid), which equals $0$, and $a(1) - a(1) = 0$ by `REAL_SUB_REFL`

**Inductive case**: 
- Assume the identity holds for $n$. We need to prove it for $n+1$
- We have two cases based on $m \leq (n+1) + 1$:
  - Case 1: $m \leq n + 1$ (using the induction hypothesis)
    - By the sum definition for number segments and arithmetic simplification, we get the result
  - Case 2: $m = (n+1) + 1$ (empty sum case)
    - In this case, $\sum_{i=m}^{n+1} (a(i+1) - a(i))$ is empty since $m > n+1$
    - Also, $a((n+1)+1) - a(m) = a(m) - a(m) = 0$ since $m = (n+1)+1$
    - The empty sum is handled by `SUM_TRIV_NUMSEG`

### Mathematical insight
This theorem is a formal expression of the telescoping sum principle. When we sum the differences of consecutive terms, most terms cancel out, leaving only the first and last terms. This is a fundamental result in calculus and discrete mathematics.

The theorem is useful in many applications, including computing partial sums of series, discrete integration, and difference equations. It's the discrete analog of the fundamental theorem of calculus, connecting differences (analogous to derivatives) to their summation (analogous to integration).

### Dependencies
**Theorems**:
- `REAL_SUB_REFL`: Proves that for any real number $x$, $x - x = 0$
- `sum`: Defines the behavior of summation, particularly the base case and recursive step

**Tactics Used**:
- `SUM_CLAUSES_NUMSEG`: Used to handle summation over number segments
- `SUM_TRIV_NUMSEG`: Used to handle empty sums over number segments
- `ARITH_RULE` and `REAL_ARITH_TAC`: Used for arithmetic simplification

### Porting notes
When porting this theorem:
1. Ensure your target system has a good definition of summation over ranges of integers
2. Verify how empty sums are handled in your target system
3. The telescoping sum argument is standard across systems, but the representation of ranges might differ
4. HOL Light uses `m..n` notation for ranges which may need to be translated appropriately

---

## DIFF_SUM

### Name of formal statement
DIFF_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIFF_SUM = prove
 (`!f f' a b.
        (!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x)
        ==> ((\x. sum(a..b) (f x)) diffl (sum(a..b) f')) x`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH; DIFF_CONST; SUM_TRIV_NUMSEG;
               ARITH_RULE `~(a <= SUC b) ==> b < a`] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ADD THEN
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `k <= b ==> k <= SUC b`]);;
```

### Informal statement
For all functions $f$, $f'$, and natural numbers $a$ and $b$, if for all $k$ such that $a \leq k \leq b$, the function $\lambda x. f(x)(k)$ is differentiable at point $x$ with derivative $f'(k)$, then the function $\lambda x. \sum_{k=a}^{b} f(x)(k)$ is differentiable at point $x$ with derivative $\sum_{k=a}^{b} f'(k)$.

In mathematical notation:
$$\forall f, f', a, b. \left(\forall k. a \leq k \land k \leq b \Rightarrow \left(\lambda x. f(x)(k)\right) \text{ diffl } f'(k)\right)(x) \Rightarrow \left(\lambda x. \sum_{k=a}^{b} f(x)(k) \text{ diffl } \sum_{k=a}^{b} f'(k)\right)(x)$$

where "diffl" denotes that the function is differentiable at a point with the specified derivative.

### Informal proof
This theorem is proven by induction on $b$:

**Base case**: When $b = a$
* We need to show that if $(\lambda x. f(x)(a))$ is differentiable at $x$ with derivative $f'(a)$, then $(\lambda x. \sum_{k=a}^{a} f(x)(k))$ is differentiable at $x$ with derivative $\sum_{k=a}^{a} f'(k)$.
* By the definition of `SUM_CLAUSES_NUMSEG`, when $a = b$, $\sum_{k=a}^{a} f(x)(k) = f(x)(a)$ and $\sum_{k=a}^{a} f'(k) = f'(a)$.
* So the statement follows directly from the assumption.

**Inductive case**: Assume the statement holds for $b$, and prove for $b+1$.
* Consider two cases:
  * Case 1: If $a > b+1$, then both sums are empty (by `SUM_CLAUSES_NUMSEG` and `SUM_TRIV_NUMSEG`), giving constant zero functions, which are differentiable with derivative zero (by `DIFF_CONST`).
  * Case 2: If $a \leq b+1$, then:
    * $\sum_{k=a}^{b+1} f(x)(k) = \sum_{k=a}^{b} f(x)(k) + f(x)(b+1)$ (by `SUM_CLAUSES_NUMSEG`)
    * By the induction hypothesis, $(\lambda x. \sum_{k=a}^{b} f(x)(k))$ is differentiable with derivative $\sum_{k=a}^{b} f'(k)$
    * By assumption, $(\lambda x. f(x)(b+1))$ is differentiable with derivative $f'(b+1)$
    * By the sum rule for derivatives (`DIFF_ADD`), the sum of these functions is differentiable with derivative $\sum_{k=a}^{b} f'(k) + f'(b+1) = \sum_{k=a}^{b+1} f'(k)$

The proof uses automation to handle the arithmetic and simplification steps, applying the key theorems about differentiability as needed.

### Mathematical insight
This theorem establishes that term-by-term differentiation of finite sums is valid - a fundamental result in calculus. It shows that if each term in a finite sum is differentiable, then the entire sum is differentiable, and the derivative of the sum equals the sum of the derivatives. 

This is a discrete analog of the more general theorem about the differentiability of infinite series, where additional convergence conditions are typically required. The finite case presented here is straightforward but essential for many applications in analysis and when working with polynomial functions or Taylor series approximations.

The theorem builds on the elementary rules of differentiation (particularly the sum rule) and extends them to finite sums, providing a bridge between basic calculus and more advanced analysis.

### Dependencies
- Theorems:
  - `sum`: Defines the recursive behavior of finite sums
  - `DIFF_CONST`: States that constant functions have zero derivatives
  - `DIFF_ADD`: The sum rule for derivatives
- Definitions:
  - `diffl`: Defines differentiability in terms of limits of difference quotients
- Required but not explicitly listed:
  - `SUM_CLAUSES_NUMSEG`: Likely provides recursive clauses for sums over numeric segments
  - `SUM_TRIV_NUMSEG`: Likely handles the case of empty sums

### Porting notes
When porting this result:
- Make sure your formal system has a suitable formalization of differentiability and finite sums first
- The induction is on the upper bound of the sum, which is a standard approach
- The treatment of the empty sum case (when a > b+1) may need special attention depending on how sums are defined in your target system
- This result should be relatively straightforward to port as it relies on standard differentiation rules and properties of finite sums

---

## bernoulli

### bernoulli
- `bernoulli`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let bernoulli = define
 `(bernoulli 0 = &1) /\
  (!n. bernoulli(SUC n) =
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))`;;
```

### Informal statement
This defines the Bernoulli numbers recursively as follows:
- $B_0 = 1$
- For all $n \geq 0$, $B_{n+1} = -\frac{1}{n+2}\sum_{j=0}^{n}\binom{n+2}{j}B_j$

where $B_n$ denotes `bernoulli n`, and $\binom{n}{k}$ denotes the binomial coefficient.

### Informal proof
No proof is provided as this is a definition. The Bernoulli numbers are defined recursively with the base case $B_0 = 1$ and a recurrence relation for subsequent terms.

### Mathematical insight
The Bernoulli numbers are a sequence of rational numbers that arise in many areas of mathematics, especially in number theory and analysis. They appear in various series expansions, such as the sum of powers formula, the Euler-Maclaurin formula, and the Taylor series expansion of many trigonometric and hyperbolic functions.

The recursive definition used here is one of several equivalent formulations. The recurrence relation can be derived from the generating function of the Bernoulli numbers:
$\frac{x}{e^x - 1} = \sum_{n=0}^{\infty} B_n \frac{x^n}{n!}$

These numbers have remarkable properties and applications:
- They are related to values of the Riemann zeta function at negative integers
- They appear in formulas for sums of powers of integers
- They are used in Euler-Maclaurin formula for approximating sums by integrals
- The odd-indexed Bernoulli numbers (except $B_1$) are zero
- The even-indexed Bernoulli numbers alternate in sign

### Dependencies
- Definitions:
  - `binom`: Binomial coefficient defined recursively as $\binom{n}{0} = 1$, $\binom{0}{k+1} = 0$, and $\binom{n+1}{k+1} = \binom{n}{k+1} + \binom{n}{k}$
- Theorems:
  - `sum`: Defines the sum operation where `sum(n,0) f = 0` and `sum(n,SUC m) f = sum(n,m) f + f(n + m)`

### Porting notes
When porting this definition:
1. Ensure that the target system has appropriate support for recursively defined functions
2. Be aware that in HOL Light, `&n` represents the conversion from a natural number to a real number
3. The negative sign in the recurrence relation is important, as is the normalization factor of $(n+2)$
4. Dependency on the specific definition of `sum` used in HOL Light, which sums from an initial value `n` up to `n+m`

---

## BERNOULLI

### Name of formal statement
BERNOULLI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BERNOULLI = prove
 (`!n. sum(0..n) (\j. &(binom(n + 1,j)) * bernoulli j) =
       if n = 0 then &1 else &0`,
  INDUCT_TAC THEN
  REWRITE_TAC[bernoulli; SUM_CLAUSES_NUMSEG; GSYM ADD1; ADD_CLAUSES; binom;
              REAL_MUL_LID; LE_0; NOT_SUC] THEN
  SIMP_TAC[BINOM_LT; ARITH_RULE `n < SUC n`; BINOM_REFL; REAL_ADD_LID] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  MATCH_MP_TAC(REAL_FIELD `x = &n + &2 ==> s + x * --s / (&n + &2) = &0`) THEN
  REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL; ARITH_RULE `~(n = n + 1)`] THEN
  REWRITE_TAC[BINOM_REFL] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$:
$$\sum_{j=0}^{n} \binom{n+1}{j} \cdot \text{bernoulli}(j) = \begin{cases} 1 & \text{if } n = 0 \\ 0 & \text{otherwise} \end{cases}$$

where $\binom{n+1}{j}$ represents the binomial coefficient, and $\text{bernoulli}(j)$ represents the $j$-th Bernoulli number.

### Informal proof
The proof proceeds by induction on $n$:

**Base case** ($n = 0$):
- We need to show $\sum_{j=0}^{0} \binom{1}{j} \cdot \text{bernoulli}(j) = 1$
- This simplifies to $\binom{1}{0} \cdot \text{bernoulli}(0) = 1 \cdot 1 = 1$
- Since $\binom{1}{0} = 1$ and $\text{bernoulli}(0) = 1$

**Inductive case** ($n = \text{SUC}(m)$):
- We need to show $\sum_{j=0}^{\text{SUC}(m)} \binom{\text{SUC}(m)+1}{j} \cdot \text{bernoulli}(j) = 0$
- The sum expands as:
  - $\sum_{j=0}^{\text{SUC}(m)} \binom{m+2}{j} \cdot \text{bernoulli}(j)$
- The theorem is proven by applying the binomial coefficient recurrence relation:
  $\binom{n+1}{k} = \frac{n+1}{n+1-k} \cdot \binom{n}{k}$ when $k \neq n+1$
- After algebraic manipulation and using the induction hypothesis, the sum equals 0

### Mathematical insight
This theorem presents a fundamental recurrence relation for Bernoulli numbers, which are important in number theory and analysis. The identity shows how Bernoulli numbers satisfy a specific linear combination with binomial coefficients.

This is actually a variant of the Bernoulli number recurrence relation, presented in a particularly elegant form. The standard recurrence relation is often written with explicit summation terms, but this version uses the binomial coefficients to capture the same relationship more concisely.

The result is canonical in the study of Bernoulli numbers and has applications in power series expansions, numeric analysis, and the computation of various special sums.

### Dependencies
- Theorems:
  - `BINOM_LT`: States that if $n < k$, then $\binom{n}{k} = 0$
  - `BINOM_REFL`: States that $\binom{n}{n} = 1$ for all $n$
  - `BINOM_TOP_STEP_REAL`: Provides a recurrence relation for binomial coefficients
  - `sum`: Defines the behavior of summation

- Definitions:
  - `binom`: Defines the binomial coefficient recursively

### Porting notes
When implementing this in another system, you'll need to:
1. Ensure the Bernoulli numbers are defined correctly
2. Make sure the binomial coefficient function is available
3. Have appropriate support for summation over integer ranges
4. Be careful about the treatment of real numbers vs. integers in the calculations

---

## bernpoly

### Name of formal statement
bernpoly

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let bernpoly = new_definition
 `bernpoly n x = sum(0..n) (\k. &(binom(n,k)) * bernoulli k * x pow (n - k))`;;
```

### Informal statement
The Bernoulli polynomial $B_n(x)$ of degree $n$ is defined as:

$$B_n(x) = \sum_{k=0}^{n} \binom{n}{k} B_k \cdot x^{n-k}$$

where:
- $\binom{n}{k}$ is the binomial coefficient
- $B_k$ is the $k$-th Bernoulli number
- $x$ is the variable of the polynomial

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
Bernoulli polynomials are a sequence of polynomials that appear in various areas of mathematics, especially in number theory, analysis, and combinatorics. They have several important properties:

1. They are related to Bernoulli numbers by $B_n(0) = B_n$, where $B_n$ is the $n$-th Bernoulli number.
2. They satisfy the identity $\frac{d}{dx}B_n(x) = n \cdot B_{n-1}(x)$
3. They are used in the Euler-Maclaurin formula, which connects sums and integrals.
4. They appear in the closed-form expressions for sums of powers of consecutive integers.
5. The definition provided here is the explicit representation of Bernoulli polynomials in terms of Bernoulli numbers and binomial coefficients.

Bernoulli polynomials serve as a bridge between discrete and continuous mathematics, making them fundamental in various mathematical applications.

### Dependencies
- Definitions:
  - `binom`: The binomial coefficient function defined recursively
  - `bernoulli`: The Bernoulli numbers (not explicitly shown in dependencies but referenced)
  - `sum`: Function for computing finite sums

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the Bernoulli numbers (`bernoulli`) are already defined in the target system.
2. Make sure the binomial coefficient function has the same behavior as HOL Light's `binom`.
3. Pay attention to the representation of natural numbers and real numbers in the target system, as the Bernoulli polynomials involve both.
4. In some systems, it may be more natural to define Bernoulli polynomials using their generating function or their differential equation rather than this explicit sum.

---

## DIFF_BERNPOLY

### Name of formal statement
DIFF_BERNPOLY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIFF_BERNPOLY = prove
 (`!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[bernpoly; SUM_CLAUSES_NUMSEG; LE_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC[SUB_REFL; real_pow; DIFF_CONST] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC DIFF_SUM THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL] THEN
  DIFF_TAC THEN ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> (n + 1) - k - 1 = n - k`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `k <= n ==> k <= n + 1`] THEN
  UNDISCH_TAC `k <= n:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_LE] THEN
  ABBREV_TAC `z = x pow (n - k)` THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $n$ and all real numbers $x$, the Bernoulli polynomial $\operatorname{bernpoly}(n+1)$ is differentiable at $x$, with derivative equal to $(n+1) \cdot \operatorname{bernpoly}(n)(x)$.

Formally, this states:
$$\forall n \in \mathbb{N}, x \in \mathbb{R}. (\operatorname{bernpoly}(n+1) \, \textrm{diffl} \, ((n+1) \cdot \operatorname{bernpoly}(n)(x)))(x)$$

where "diffl" denotes that the function is differentiable at the point with the given derivative value.

### Informal proof
The proof establishes the derivative relation for Bernoulli polynomials through these steps:

* Start by applying the eta-conversion (using `ETA_AX`) to properly handle the function.
* Unfold the definition of Bernoulli polynomials, which are defined as:
  $$\operatorname{bernpoly}(n)(x) = \sum_{k=0}^{n} \binom{n}{k} B_{n-k} \cdot x^k$$
  where $B_i$ are the Bernoulli numbers.
* Separate the sum into the $k=0$ term and the rest (using `SUM_CLAUSES_NUMSEG`).
* Rewrite the expression to have the form of a sum of two functions.
* Apply the theorem `DIFF_ADD` to differentiate this sum.
* The constant term (when $k=0$) differentiates to 0 via `DIFF_CONST`.
* For the remaining terms, we use `DIFF_SUM` to differentiate each term in the summation.
* Apply the binomial coefficient identity: $\binom{n+1}{k} = \frac{n+1}{n+1-k} \cdot \binom{n}{k}$ when $k \neq n+1$.
* Perform differentiation of power terms using `DIFF_TAC`.
* Apply algebraic manipulations and simplifications to show that the derivative equals $(n+1) \cdot \operatorname{bernpoly}(n)(x)$.
* The final steps involve arithmetic operations and field properties to complete the proof.

### Mathematical insight
This theorem establishes a key recurrence relation for the derivatives of Bernoulli polynomials: the derivative of the $(n+1)$-th Bernoulli polynomial is proportional to the $n$-th Bernoulli polynomial, with the proportionality constant being $(n+1)$.

This is a fundamental property of Bernoulli polynomials and allows for efficient calculation of higher-order derivatives. This recurrence relation is particularly useful in numerical analysis, approximation theory, and the study of special functions.

The result is also connected to the generating function of Bernoulli polynomials and plays an important role in various applications including the Euler-Maclaurin formula for approximating sums.

### Dependencies
#### Theorems
- `BINOM_TOP_STEP_REAL`: Identity for binomial coefficients with real number conversion
- `REAL_MUL_LZERO`: Multiplication by zero gives zero
- `DIFF_CONST`: The derivative of a constant function is zero
- `DIFF_ADD`: The derivative of a sum is the sum of derivatives

#### Definitions
- `diffl`: Defines differentiability at a point with a specific derivative value

### Porting notes
When porting this theorem:
- Ensure that your system has the Bernoulli polynomials properly defined
- Check how derivatives are represented in your target system
- The proof heavily relies on algebraic manipulations and field properties, which might require different tactics in other proof assistants
- Special attention should be given to how summations and binomial coefficients are handled in the target system

---

## INTEGRALS_EQ

### INTEGRALS_EQ
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INTEGRALS_EQ = prove
 (`!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - g(x)`; `x:real`; `&0`] DIFF_ISCONST_ALL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
```

### Informal statement
Let $f$ and $g$ be real-valued functions. If the derivative of their difference $f(x) - g(x)$ is zero at all points (i.e., $\forall x. ((f(x) - g(x))' = 0)$), and if $f(0) = g(0)$, then $f(x) = g(x)$ for all $x$.

In other words, if two functions have the same derivative everywhere and agree at a single point, then they must be equal everywhere.

### Informal proof
The proof uses the fact that a function with zero derivative everywhere must be constant.

Let's define $h(x) = f(x) - g(x)$. We are given that:
1. $h'(x) = 0$ for all $x$
2. $h(0) = f(0) - g(0) = 0$

We apply `DIFF_ISCONST_ALL` theorem, which states that if a function's derivative is zero everywhere, then the function is constant. Thus, for any $x$ and $0$, we have $h(x) = h(0)$.

Since $h(0) = 0$, we conclude that $h(x) = 0$ for all $x$, which means $f(x) - g(x) = 0$, or equivalently, $f(x) = g(x)$ for all $x$.

### Mathematical insight
This theorem establishes a foundational result in calculus: two functions with identical derivatives differ at most by a constant. If we additionally know they agree at a single point, then they must be identical everywhere.

This result is essential for the fundamental theorem of calculus and for establishing the uniqueness of antiderivatives up to a constant. In formal mathematics, it provides a powerful method for proving function equality by showing equal derivatives and agreement at a point, rather than proving equality at every point directly.

### Dependencies
- `DIFF_ISCONST_ALL`: If a function has zero derivative everywhere, then it is constant
- `diffl`: Definition of derivative in HOL Light, where `(f diffl l)(x)` means that the derivative of f at point x is l

### Porting notes
When porting this theorem:
- Ensure your target system has a corresponding theorem about functions with zero derivatives being constant
- Be aware of how derivatives are defined in your target system, as notation may differ
- The proof relies on the fact that two functions are equal if their difference is zero everywhere

---

## RECURRENCE_BERNPOLY

### Name of formal statement
RECURRENCE_BERNPOLY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RECURRENCE_BERNPOLY = prove
 (`!n x. bernpoly n (x + &1) - bernpoly n x = &n * x pow (n - 1)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[bernpoly; SUM_SING_NUMSEG; REAL_SUB_REFL; SUB_REFL;
                real_pow; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRALS_EQ THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(*) (&(SUC n))`) THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REPEAT(MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC) THEN
    SIMP_TAC[SUC_SUB1; DIFF_CMUL; DIFF_POW; DIFF_BERNPOLY; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CHAIN THEN REWRITE_TAC[DIFF_BERNPOLY] THEN
    DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bernpoly; GSYM SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_POW_ONE; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUB_REFL; real_pow] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REWRITE_TAC[BERNOULLI; ADD1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH; real_pow; REAL_MUL_LID] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN
  ASM_REWRITE_TAC[ADD_SUB]);;
```

### Informal statement
For all natural numbers $n$ and real numbers $x$, the Bernoulli polynomials satisfy the recurrence relation:

$$\text{bernpoly}(n, x + 1) - \text{bernpoly}(n, x) = n \cdot x^{n-1}$$

This is a key functional equation relating Bernoulli polynomials at shifted arguments.

### Informal proof
The proof proceeds by induction on $n$.

**Base case ($n = 0$)**:
- When $n = 0$, we need to show $\text{bernpoly}(0, x + 1) - \text{bernpoly}(0, x) = 0$
- This simplifies using the definition of Bernoulli polynomials, the fact that $\text{bernpoly}(0, x) = 1$, and properties of subtraction and multiplication by zero.

**Inductive step**:
- Assume the result holds for $n$, we need to prove it for $n+1$.
- The proof applies the `INTEGRALS_EQ` theorem, which requires showing:
  1. The derivatives of both sides are equal
  2. The functions are equal at some point

For the derivative equality:
- Take the derivative of both sides of the equation for $n+1$
- The left side requires the chain rule and the derivative of Bernoulli polynomials
- Using the induction hypothesis $(n+1) \cdot (\text{bernpoly}(n, x+1) - \text{bernpoly}(n, x)) = (n+1) \cdot n \cdot x^{n-1}$
- Manipulating using properties of real arithmetic yields the desired equality

For the function equality:
- We expand the definition of Bernoulli polynomials
- Use properties of summation and manipulate the terms algebraically
- Apply the definition of Bernoulli numbers
- Complete the proof through careful case analysis and algebraic manipulation

### Mathematical insight
This recurrence relation is a fundamental property of Bernoulli polynomials that connects values at consecutive integers. It's equivalent to the statement that Bernoulli polynomials are the unique polynomials satisfying:
1. $B_n'(x) = n B_{n-1}(x)$
2. $\int_0^1 B_n(x) dx = 0$ for $n \geq 1$
3. $B_n(0) = B_n(1)$ for $n \neq 1$

The identity proved here is particularly important for number theory, especially in the study of zeta functions and in the Euler-Maclaurin summation formula. It shows that Bernoulli polynomials behave similarly to power functions under discrete differences.

### Dependencies
**Theorems:**
- `REAL_MUL_RID`: $\forall x. x \cdot 1 = x$
- `REAL_MUL_LZERO`: $\forall x. 0 \cdot x = 0$
- `REAL_MUL_RZERO`: $\forall x. x \cdot 0 = 0$
- `REAL_SUB_REFL`: $\forall x. x - x = 0$
- `REAL_SUB_0`: $\forall x y. (x - y = 0) \Leftrightarrow (x = y)$
- `REAL_SUB_LDISTRIB`: $\forall x y z. x \cdot (y - z) = (x \cdot y) - (x \cdot z)$
- `REAL_SUB_RZERO`: $\forall x. x - 0 = x$
- `DIFF_CMUL`: Derivative of constant multiple
- `DIFF_SUB`: Derivative of difference
- `DIFF_CHAIN`: Chain rule for derivatives
- `DIFF_POW`: Derivative of power function
- `DIFF_BERNPOLY`: Derivative of Bernoulli polynomial
- `INTEGRALS_EQ`: Equality of functions with equal derivatives and equal at a point

**Definitions and Functions:**
- `bernpoly`: Bernoulli polynomial function
- `BERNOULLI`: Bernoulli number

### Porting notes
When porting this theorem:
1. Ensure your system has properly defined Bernoulli polynomials and numbers with their standard properties.
2. The induction structure may need adaptation based on how induction is formalized in your target system.
3. The proof relies on differentiability and integration properties, so ensure your target system has appropriate calculus libraries.
4. Pay attention to how the proof combines algebraic manipulations with calculus theorems.

---

## SUM_OF_POWERS

### Name of formal statement
SUM_OF_POWERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_OF_POWERS = prove
 (`!n. sum(0..n) (\k. &k pow m) =
        (bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)) / (&m + &1)`,
  GEN_TAC THEN ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum(0..n) (\i. bernpoly (SUC m) (&(i + 1)) - bernpoly (SUC m) (&i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RECURRENCE_BERNPOLY; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; SUC_SUB1];
    SIMP_TAC[SUM_DIFFS; LE_0] THEN REWRITE_TAC[REAL_OF_NUM_ADD]]);;
```

### Informal statement
For any natural number $n$, the sum of $k^m$ for $k$ ranging from $0$ to $n$ is given by:

$$\sum_{k=0}^{n} k^m = \frac{B_{m+1}(n+1) - B_{m+1}(0)}{m+1}$$

where $B_{m+1}$ represents the Bernoulli polynomial of degree $m+1$.

### Informal proof
The proof proceeds as follows:

- Start with a goal transformation using the equality of divisions: for a positive number $n+1$, we have $a = \frac{b}{c}$ if and only if $a \cdot c = b$.
- Rewrite the goal by moving $(m+1)$ to the left side of the equation using commutativity of multiplication.
- Use the property of sums with constant factors: $\sum_{i=0}^{n} (m+1) \cdot i^m = (m+1) \cdot \sum_{i=0}^{n} i^m$
- The key step is to use the recurrence relation for Bernoulli polynomials, specifically:
  $$B_{m+1}'(x) = (m+1) \cdot x^m$$
- This allows us to rewrite $\sum_{i=0}^{n} (m+1) \cdot i^m$ as $\sum_{i=0}^{n} (B_{m+1}(i+1) - B_{m+1}(i))$
- The sum of differences telescopes to $B_{m+1}(n+1) - B_{m+1}(0)$, completing the proof.

### Mathematical insight
This theorem provides a closed-form expression for the sum of powers using Bernoulli polynomials. This is a classical result in number theory and combinatorics. The Bernoulli polynomials appear naturally in the study of power sums and have connections to various areas of mathematics.

The formula gives an efficient way to compute sums of powers without having to add each term individually. It generalizes the well-known formulas for the sum of the first $n$ natural numbers ($\sum_{k=1}^{n} k = \frac{n(n+1)}{2}$), sum of squares, and other power sums.

The result can also be seen as a discrete analogue of integration, where we're finding a "discrete antiderivative" for the function $f(k) = k^m$.

### Dependencies
- `sum`: Defines sum(n,m) f recursively: sum(n,0) f = 0 and sum(n,SUC m) f = sum(n,m) f + f(n + m)
- `RECURRENCE_BERNPOLY`: (Implied) A theorem stating the recurrence relation for Bernoulli polynomials
- `SUM_DIFFS`: (Implied) A theorem about the telescoping property of summing differences
- `bernpoly`: (Implied) The Bernoulli polynomial function

### Porting notes
When porting this theorem:
- Ensure that Bernoulli polynomials are correctly defined in the target system
- The proof relies on the telescoping property of sums, which should be available or provable in most proof assistants
- The representation of natural numbers and reals might differ between systems; adjust accordingly
- The recurrence relation of Bernoulli polynomials is crucial for this proof

---

## SUM_CONV

### Name of formal statement
SUM_CONV

### Type of the formal statement
Conversion function

### Formal Content
```ocaml
let SUM_CONV =
  let pth = prove
   (`sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)`,
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0]) in
  let econv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and econv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec sconv tm =
    (econv_0 ORELSEC
     (LAND_CONV(RAND_CONV num_CONV) THENC econv_1 THENC
      COMB2_CONV (RAND_CONV sconv) (RAND_CONV NUM_SUC_CONV))) tm in
  sconv;;
```

### Informal statement
`SUM_CONV` is a conversion function that evaluates summations of the form $\sum_{i=0}^{n} f(i)$ when applied to a term of the form `sum(0..n) f` where `n` is a numeral. It recursively applies the following rules:
- $\sum_{i=0}^{0} f(i) = f(0)$
- $\sum_{i=0}^{n+1} f(i) = \sum_{i=0}^{n} f(i) + f(n+1)$

### Informal proof
The implementation creates a conversion that evaluates summations over ranges starting at 0:

- First, two basic equivalences are proved:
  - $\sum_{i=0}^{0} f(i) = f(0)$
  - $\sum_{i=0}^{n+1} f(i) = \sum_{i=0}^{n} f(i) + f(n+1)$
  
- These are proven using `SUM_CLAUSES_NUMSEG` and `LE_0`. The former provides the general rules for summing over segments, and the latter ensures that $0 \leq 0$ is true.

- The conversion then works recursively:
  - For `sum(0..0) f`, it directly applies the first rule.
  - For `sum(0..SUC n) f`, it:
    1. Converts the numeral to successor form
    2. Applies the second rule
    3. Recursively evaluates the `sum(0..n) f` part
    4. Evaluates the `SUC n` in the second term

- This implementation allows computation of explicit numeric sums by repeatedly applying these transformations.

### Mathematical insight
This conversion is an automation tool that implements the standard recursive evaluation of finite sums. It's a computational utility rather than a theorem, enabling automatic evaluation of concrete summations within the HOL Light system.

The key insight is converting the abstract mathematical recursive definition of summation into an effective computation procedure. This follows the typical pattern of defining computational conversions in HOL Light - first establishing the mathematical rules, then implementing a recursive procedure that applies those rules to simplify expressions.

This is particularly useful when working with concrete calculations involving sums, as it can automatically reduce summation expressions to their evaluated form.

### Dependencies
- **Theorems**:
  - `sum`: The recursive definition of summation
  - `SUM_CLAUSES_NUMSEG`: Rules for summing over numeric segments
  - `LE_0`: The fact that 0 ≤ 0

- **Conversions**:
  - `GEN_REWRITE_CONV`: For applying rewrite rules
  - `LAND_CONV`, `RAND_CONV`: For applying conversions to specific parts of terms
  - `COMB2_CONV`: For combining conversions
  - `num_CONV`: For converting numerals
  - `NUM_SUC_CONV`: For converting successor expressions

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has a similar concept of "conversions" or term rewriting tactics
2. The implementation relies on HOL Light's specific combinators for manipulating terms - you'll need equivalent operations in the target system
3. The recursive structure might need adjustment depending on how the target system handles recursion in tactic scripts
4. Consider whether the target system has built-in automation for finite sums that might be more efficient

---

## BINOM_CONV

### Name of formal statement
BINOM_CONV

### Type of the formal statement
Conversion function definition

### Formal Content
```ocaml
let BINOM_CONV =
  let pth = prove
   (`a * b * x = FACT c ==> x = (FACT c) DIV (a * b)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[LT_NZ; MULT_ASSOC; MULT_CLAUSES] THEN
      MESON_TAC[LT_NZ; FACT_LT]]) in
  let match_pth = MATCH_MP pth
  and binom_tm = `binom` in
  fun tm ->
    let bop,lr = dest_comb tm in
    if bop <> binom_tm then failwith "BINOM_CONV" else
    let l,r = dest_pair lr in
    let n = dest_numeral l and k = dest_numeral r in
    if n </ k then
      let th = SPECL [l;r] BINOM_LT in
      MP th (EQT_ELIM(NUM_LT_CONV(lhand(concl th))))
    else
      let d = n -/ k in
      let th1 = match_pth(SPECL [mk_numeral d; r] BINOM_FACT) in
      CONV_RULE NUM_REDUCE_CONV th1;;
```

### Informal statement
`BINOM_CONV` is a conversion function that evaluates binomial coefficients of the form `binom(n,k)` where `n` and `k` are numeric literals, returning a theorem that states the evaluated result. It converts expressions of the form `binom(n,k)` into their numerical values.

### Informal proof
The conversion implementation has two main cases:

- **Case 1**: When $n < k$, it applies the theorem `BINOM_LT` which states that $\binom{n}{k} = 0$ when $n < k$.

- **Case 2**: When $n \geq k$, it uses the formula derived from `BINOM_FACT`:
  
  The theorem `BINOM_FACT` states that $n! \cdot k! \cdot \binom{n+k}{k} = (n+k)!$
  
  From this, we can derive:
  * Let $d = n-k$, then $n = d+k$
  * Substituting, we get $d! \cdot k! \cdot \binom{d+k}{k} = (d+k)!$ 
  * Therefore, $\binom{n}{k} = \binom{d+k}{k} = \frac{(d+k)!}{d! \cdot k!} = \frac{n!}{(n-k)! \cdot k!}$

The implementation includes:
* A helper theorem `pth` that proves if $a \cdot b \cdot x = c!$ then $x = \frac{c!}{a \cdot b}$
* Extraction of the numeric literals `n` and `k` from the input term
* Logic to handle both cases of the computation

### Mathematical insight
Binomial coefficients appear frequently in combinatorics and many other areas of mathematics. This conversion provides an efficient computational mechanism to evaluate binomial coefficients with concrete numeric values directly within the proof assistant.

The implementation cleverly uses the relationship between binomial coefficients and factorials to perform the calculation, applying the identity $\binom{n}{k} = \frac{n!}{k!(n-k)!}$ after handling the special case where $n < k$.

This conversion is particularly useful in simplifying expressions involving binomial coefficients where the arguments are known constants, allowing for concrete calculations during theorem proving.

### Dependencies
- Theorems:
  - `BINOM_LT`: Establishes that $\binom{n}{k} = 0$ when $n < k$
  - `BINOM_FACT`: Relates binomial coefficients to factorials via $n! \cdot k! \cdot \binom{n+k}{k} = (n+k)!$
- Definitions:
  - `binom`: The binomial coefficient function defined recursively

### Porting notes
When porting this conversion to other systems:
- Ensure the target proof assistant has a way to represent conversion functions (functions that transform terms into theorems)
- Consider how numeric literals are represented in the target system
- Check if the target system has built-in support for binomial coefficients that might be more efficient
- This conversion relies on the recursive definition of binomial coefficients rather than the factorial formula directly, which might affect how it should be implemented in systems with different definitions

---

## BERNOULLIS

### BERNOULLIS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let BERNOULLIS =
  let th_0,th_1 = CONJ_PAIR bernoulli
  and b_tm = `bernoulli` in
  let conv_1 = GEN_REWRITE_CONV I [th_1] in
  let rec bconv n =
    if n <= 0 then [th_0] else
    let bths = bconv (n - 1)
    and tm = mk_comb(b_tm,mk_small_numeral n) in
    (RAND_CONV num_CONV THENC conv_1 THENC
     LAND_CONV(RAND_CONV SUM_CONV) THENC
     ONCE_DEPTH_CONV BETA_CONV THENC
     DEPTH_CONV(NUM_RED_CONV ORELSEC BINOM_CONV) THENC
     GEN_REWRITE_CONV ONCE_DEPTH_CONV bths THENC
     REAL_RAT_REDUCE_CONV) tm :: bths in
  bconv;;
```

### Informal statement
`BERNOULLIS` is a function that computes a list of theorems about Bernoulli numbers. Given a natural number `n`, it returns a list of theorems of the form:
```
bernoulli 0 = 1, bernoulli 1 = -1/2, bernoulli 2 = 1/6, ..., bernoulli n = value
```

The function recursively builds this list by applying a sequence of term rewriting and evaluation steps to calculate each Bernoulli number from previously computed values using the recurrence relation defined in the `bernoulli` definition.

### Informal proof
This is not a theorem but a function definition that creates a computational procedure for deriving theorems about Bernoulli numbers. The function works as follows:

1. It starts by extracting two theorems from the `bernoulli` definition:
   - `th_0`: This corresponds to the base case `bernoulli 0 = 1`
   - `th_1`: This corresponds to the recursive definition for `n > 0`

2. It then defines a recursive function `bconv` that:
   - Returns `[th_0]` for n ≤ 0 (just the base case theorem)
   - For n > 0, it:
     - Recursively computes the theorems for Bernoulli numbers up to n-1
     - Creates a term for `bernoulli n`
     - Applies a series of conversions that:
       - Apply the recursive definition from `th_1`
       - Evaluate the summation using `SUM_CONV`
       - Perform beta-reduction and simplify numerical expressions
       - Substitute previously proven Bernoulli values using the recursive results
       - Simplify the rational number result
     - Adds this new theorem to the list of previous results

3. The function returns the result of calling `bconv` with the provided argument.

### Mathematical insight
Bernoulli numbers are a sequence of rational numbers with important applications in number theory and analysis. They appear in the Taylor series expansions of trigonometric functions and are connected to special values of the Riemann zeta function.

The `BERNOULLIS` function implements an efficient computational method for deriving exact values of Bernoulli numbers based on their recursive definition. This approach is particularly valuable in a theorem prover, where we want to have precise, formally verified values rather than numerical approximations.

The function illustrates a common pattern in HOL Light: building derived theorems programmatically by applying a sequence of conversions and rewriting operations to automate what would otherwise be tedious manual proofs.

### Dependencies
- `bernoulli`: The definition of Bernoulli numbers
- `CONJ_PAIR`: Theorem that extracts both parts of a conjunction
- `GEN_REWRITE_CONV`: Conversion for general rewriting
- `RAND_CONV`: Conversion that applies to the right side of an application
- `LAND_CONV`: Conversion that applies to the left side of an application
- `SUM_CONV`: Conversion for evaluating summations
- `BETA_CONV`: Beta-reduction conversion
- `NUM_RED_CONV`: Conversion for numerical reduction
- `BINOM_CONV`: Conversion for binomial coefficients
- `REAL_RAT_REDUCE_CONV`: Conversion for simplifying rational expressions

### Porting notes
When porting this function to another proof assistant:
1. Ensure the target system has a definition for Bernoulli numbers with a similar recursive structure
2. Create equivalent conversions or tactics for each step in the computation
3. Pay attention to how summations and binomial coefficients are handled in the target system
4. Consider whether the target system handles rational number computations differently
5. This function is primarily a computational tool, so focus on reproducing its functionality rather than its exact implementation details

---

## BERNOULLI_CONV

### Name of formal statement
BERNOULLI_CONV

### Type of the formal statement
Conversion function (OCaml function that transforms terms)

### Formal Content
```ocaml
let BERNOULLI_CONV =
  let b_tm = `bernoulli` in
  fun tm -> let op,n = dest_comb tm in
            if op <> b_tm || not(is_numeral n) then failwith "BERNOULLI_CONV"
            else hd(BERNOULLIS(dest_small_numeral n));;
```

### Informal statement
`BERNOULLI_CONV` is a conversion function that evaluates Bernoulli numbers. Given a term of the form `bernoulli n` where `n` is a numeral, it returns the exact rational value of the Bernoulli number $B_n$.

The function works by:
1. Checking that the input term is of the form `bernoulli n` where `n` is a numeral
2. Using the `BERNOULLIS` function to compute the first `n+1` Bernoulli numbers
3. Extracting the `n`-th Bernoulli number from this list

If the input term is not of the required form, the function fails with the message "BERNOULLI_CONV".

### Informal proof
This is not a theorem but a conversion function implementation. The function:

- Takes a term `tm` as input
- Decomposes `tm` into an operator `op` and an argument `n` using `dest_comb`
- Checks if `op` is the `bernoulli` function and if `n` is a numeral
- If the checks pass, it:
  - Converts `n` to an OCaml integer using `dest_small_numeral`
  - Calls `BERNOULLIS` with this integer to generate Bernoulli numbers
  - Takes the first element of the resulting list using `hd`
- Otherwise, it fails with an error message

### Mathematical insight
Bernoulli numbers are a sequence of rational numbers with significant importance in number theory and analysis. They appear in the Taylor series expansions of trigonometric and hyperbolic functions, and in formulas for sums of powers.

This conversion provides an efficient way to compute exact values of Bernoulli numbers within the HOL Light theorem prover, which is crucial for formalizing results in number theory and analysis that depend on these numbers.

The implementation likely relies on an efficient algorithm for computing Bernoulli numbers, such as a recurrence relation or generating function approach, encapsulated in the `BERNOULLIS` function.

### Dependencies
- Functions:
  - `bernoulli`: The function representing Bernoulli numbers
  - `BERNOULLIS`: Function that computes a list of Bernoulli numbers
  - `dest_comb`: HOL Light function to decompose a combination term
  - `dest_small_numeral`: HOL Light function to convert a numeral term to an OCaml integer
  - `is_numeral`: HOL Light function to check if a term is a numeral

### Porting notes
When porting this to another system:
1. Ensure a suitable representation of Bernoulli numbers exists in the target system
2. Implement or find an efficient algorithm for computing Bernoulli numbers
3. Create a similar conversion function that maps symbolic requests for Bernoulli numbers to their exact rational values
4. Consider performance implications for large indices, as Bernoulli numbers grow rapidly in complexity

Different proof assistants may have different approaches to representing rational numbers and implementing numerical algorithms, so adjustments may be needed based on the target system's capabilities.

---

## BERNPOLY_CONV

### Name of formal statement
BERNPOLY_CONV

### Type of the formal statement
conversion function

### Formal Content
```ocaml
let BERNPOLY_CONV =
  let conv_1 =
    REWR_CONV bernpoly THENC SUM_CONV THENC
    TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV
  and conv_3 =
    ONCE_DEPTH_CONV BINOM_CONV THENC REAL_POLY_CONV in
  fun tm ->
    let n = dest_small_numeral(lhand tm) in
    let conv_2 = GEN_REWRITE_CONV ONCE_DEPTH_CONV (BERNOULLIS n) in
    (conv_1 THENC conv_2 THENC conv_3) tm;;
```

### Informal statement
`BERNPOLY_CONV` is a conversion function that computes symbolic expressions for Bernoulli polynomials. When applied to a term of the form `bernpoly n x`, where `n` is a specific numeral, it returns the explicit polynomial expression in `x` for the nth Bernoulli polynomial.

### Informal proof
The conversion works through a sequential composition of multiple conversions:

1. First applies `REWR_CONV bernpoly` to rewrite using the definition of Bernoulli polynomials.
2. Then uses `SUM_CONV` to expand the sum in the definition.
3. Applies `TOP_DEPTH_CONV BETA_CONV` to perform beta-reduction throughout the term.
4. Uses `NUM_REDUCE_CONV` to simplify numerical expressions.
5. Extracts the numeric value `n` from the term using `dest_small_numeral`.
6. Applies the specific Bernoulli number theorem for that value of `n` using `GEN_REWRITE_CONV ONCE_DEPTH_CONV (BERNOULLIS n)`.
7. Finally, applies conversions to:
   - Expand binomial coefficients using `ONCE_DEPTH_CONV BINOM_CONV`
   - Simplify the resulting polynomial expression using `REAL_POLY_CONV`

The composition of these conversions yields the final simplified polynomial expression.

### Mathematical insight
This conversion function is a computational tool that enables automatically deriving explicit forms of Bernoulli polynomials. Bernoulli polynomials are important in various areas of mathematics, including number theory, analysis, and special functions.

The key insight is that Bernoulli polynomials can be expressed as:

$$B_n(x) = \sum_{k=0}^{n} \binom{n}{k} B_{n-k} x^k$$

where $B_j$ are the Bernoulli numbers. This conversion leverages precomputed Bernoulli numbers (through the `BERNOULLIS` theorems) and performs symbolic manipulations to derive the explicit polynomial form.

This function is particularly useful for automatic simplification in proofs involving Bernoulli polynomials, allowing the system to work with their explicit polynomial forms rather than the recursive definition.

### Dependencies
- **Definitions**:
  - `bernpoly`: Definition of Bernoulli polynomials
- **Theorems**:
  - `BERNOULLIS`: Theorems giving exact values of Bernoulli numbers
- **Conversions**:
  - `REWR_CONV`, `SUM_CONV`, `TOP_DEPTH_CONV`, `BETA_CONV`, `NUM_REDUCE_CONV`
  - `ONCE_DEPTH_CONV`, `BINOM_CONV`, `REAL_POLY_CONV`
  - `GEN_REWRITE_CONV`

### Porting notes
When porting to other systems:
1. Ensure the target system has a definition of Bernoulli polynomials that matches HOL Light's definition.
2. The implementation requires precomputed Bernoulli numbers, so these would need to be defined or ported as well.
3. Consider if the target system has similar conversion/rewriting tools, or if you need to implement custom tactics.
4. The implementation heavily relies on HOL Light's specific conversion combinators - you may need to adapt to the rewriting strategy of the target system.
5. In systems with more powerful arithmetic reasoning, parts of this conversion might be replaced by built-in simplification procedures.

---

## SOP_CONV

### Name of formal statement
SOP_CONV

### Type of the formal statement
Conversion function (not a definition, theorem, or axiom)

### Formal Content
```ocaml
let SOP_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow m) =
        (\p. (p(&n + &1) - p(&0)) / (&m + &1))
        (\x. bernpoly (SUC m) x)`,
    REWRITE_TAC[SUM_OF_POWERS]) in
  let conv_0 = REWR_CONV pth in
  REWR_CONV pth THENC
  RAND_CONV(ABS_CONV(LAND_CONV NUM_SUC_CONV THENC BERNPOLY_CONV)) THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  REAL_POLY_CONV;;
```

### Informal statement
`SOP_CONV` is a conversion function that transforms expressions of the form
$$\sum_{k=0}^{n} k^m$$
to a closed-form expression using Bernoulli polynomials. Specifically, it uses the formula:
$$\sum_{k=0}^{n} k^m = \frac{B_{m+1}(n+1) - B_{m+1}(0)}{m+1}$$
where $B_{m+1}(x)$ is the $(m+1)$-th Bernoulli polynomial.

### Informal proof
The implementation of `SOP_CONV` consists of several steps:

1. First, it uses the theorem `SUM_OF_POWERS` which provides the formula:
   $$\sum_{k=0}^{n} k^m = \frac{p(n+1) - p(0)}{m+1}$$
   where $p(x) = B_{m+1}(x)$ is the $(m+1)$-th Bernoulli polynomial.

2. It creates a conversion sequence that:
   - Applies the `SUM_OF_POWERS` theorem using `REWR_CONV`
   - Transforms the right-hand side by:
     - Converting `SUC m` to `m + 1` for the Bernoulli polynomial index
     - Computing the explicit form of the Bernoulli polynomial using `BERNPOLY_CONV`
   - Performs beta-reduction with `BETA_CONV`
   - Finally applies `REAL_POLY_CONV` to simplify the resulting real polynomial expression

The conversion thus transforms the sum of powers into a closed-form polynomial expression.

### Mathematical insight
Sums of powers ($\sum_{k=0}^{n} k^m$) appear frequently in mathematics and computer science. This conversion function implements the well-known formula relating these sums to Bernoulli polynomials, which provides a closed-form expression for such sums.

The key insight is that Bernoulli polynomials provide a systematic way to express these sums in closed form, avoiding the need for explicit summation. This is important for symbolic computation and for proving properties of sums of powers.

This conversion allows HOL Light to automatically compute and reason about sums of powers, which is useful in many mathematical contexts, including number theory, combinatorics, and calculus.

### Dependencies
- Theorems:
  - `sum`: Basic properties of summation
  - `SUM_OF_POWERS`: The main theorem relating sums of powers to Bernoulli polynomials
- Conversions:
  - `BERNPOLY_CONV`: Conversion for computing Bernoulli polynomials
  - `REAL_POLY_CONV`: Conversion for simplifying real polynomial expressions
  - `NUM_SUC_CONV`: Conversion for successor of natural numbers
  - Various tactical conversions: `REWR_CONV`, `RAND_CONV`, `ABS_CONV`, `LAND_CONV`, `TOP_DEPTH_CONV`, `BETA_CONV`

### Porting notes
When porting this to other proof assistants:
1. Ensure the target system has a theory of Bernoulli polynomials
2. Implement or port the `SUM_OF_POWERS` theorem
3. The conversion is essentially a rewriting strategy, so adapt it to the rewriting mechanisms of the target system
4. Be aware that other systems might handle real numbers and polynomials differently, so the simplification steps may need adjustment

---

## SOP_NUM_CONV

### Name of formal statement
SOP_NUM_CONV

### Type of the formal statement
Conversion function (implementation)

### Formal Content
```ocaml
let SOP_NUM_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow p) = &m ==> nsum(0..n) (\k. k EXP p) = m`,
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUM_NUMSEG;
                REAL_OF_NUM_EQ]) in
  let rule_1 = PART_MATCH (lhs o rand) pth in
  fun tm ->
    let th1 = rule_1 tm in
    let th2 = SOP_CONV(lhs(lhand(concl th1))) in
    MATCH_MP th1 th2;;
```

### Informal statement
`SOP_NUM_CONV` is a conversion function that transforms expressions of the form `nsum(0..n) (λk. k EXP p)` to their closed-form expressions, where:
- `nsum(0..n)` represents a sum over natural numbers from 0 to n
- `k EXP p` represents k raised to the power p in the natural number domain

The conversion uses the relation between natural number sums (`nsum`) and real number sums (`sum`) along with the existing conversion function `SOP_CONV` that handles real number sums of powers.

### Informal proof
The implementation works as follows:

1. First, a theorem is proven that establishes the connection between real and natural number sums of powers:
   ```
   sum(0..n) (λk. &k pow p) = &m ==> nsum(0..n) (λk. k EXP p) = m
   ```
   where:
   - `&k` represents the injection from natural numbers to real numbers
   - `pow` is real exponentiation
   - `EXP` is natural number exponentiation
   - `&m` is the real number equivalent of natural number m

2. The proof of this theorem uses:
   - `REAL_OF_NUM_POW` (converting natural number exponentiation to real exponentiation)
   - `REAL_OF_NUM_SUM_NUMSEG` (relating sums over natural numbers to real sums)
   - `REAL_OF_NUM_EQ` (injection from naturals to reals preserves equality)

3. The conversion function then:
   - Uses `PART_MATCH` to match the input term with the left-hand-side of the theorem's conclusion
   - Applies `SOP_CONV` to compute the closed form for the real number sum of powers
   - Uses `MATCH_MP` to combine these results and produce the final theorem

### Mathematical insight
This conversion function bridges the gap between real-valued sums of powers (which are handled by `SOP_CONV`) and natural number sums of powers. It provides a way to compute closed-form expressions for sums of the form $\sum_{k=0}^{n} k^p$ in the natural number domain.

The key insight is that computing closed forms for sums of powers can be done more conveniently in the real number domain (using `SOP_CONV`), and then the results can be transferred back to the natural number domain using the embedding of naturals into reals.

### Dependencies
- **Theorems**:
  - `sum`: Recursive definition of summation over natural numbers
  - `REAL_OF_NUM_POW`: Relates real and natural number exponentiation
  - `REAL_OF_NUM_SUM_NUMSEG`: Relates real and natural number summation over intervals
  - `REAL_OF_NUM_EQ`: Equality preservation under natural-to-real embedding
- **Conversions**:
  - `SOP_CONV`: Conversion for sums of powers in the real domain

### Porting notes
When porting this conversion:
1. Ensure the target system has equivalent functionality to `SOP_CONV` for real-valued sums
2. Be careful with the different types for natural and real exponentiation
3. The ported implementation should handle the type conversion between naturals and reals appropriately, which might require different tactics depending on how the target system handles type coercions

---

