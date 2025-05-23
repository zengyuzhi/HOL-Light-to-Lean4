# fourier.ml

## Overview

Number of statements: 145

This file formalizes square integrable functions from the real line to real numbers and develops the basic theory of Fourier series in HOL Light. It builds upon the more general theory of L^p spaces established in `lpspaces.ml`, specializing to L^2 functions and introducing fundamental concepts needed for Fourier analysis. The file likely includes definitions of trigonometric functions as orthogonal bases, Fourier coefficients, and convergence results for Fourier series.

## SUM_NUMBERS

### SUM_NUMBERS
- `SUM_NUMBERS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_NUMBERS = prove
 (`!n. sum(0..n) (\r. &r) = (&n * (&n + &1)) / &2`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
This theorem states that for any natural number $n$, the sum of all integers from $0$ to $n$ is equal to $\frac{n(n+1)}{2}$. Formally:

$$\forall n \in \mathbb{N}. \sum_{r=0}^{n} r = \frac{n(n+1)}{2}$$

### Informal proof
The proof proceeds by induction on the natural number $n$:

- **Base case** ($n = 0$): 
  The sum $\sum_{r=0}^{0} r = 0$, and $\frac{0 \cdot (0+1)}{2} = 0$, so the equation holds.

- **Induction step**: Assume the equation holds for some $n$, that is, $\sum_{r=0}^{n} r = \frac{n(n+1)}{2}$.
  
  We need to show it holds for $n+1$:
  
  $$\sum_{r=0}^{n+1} r = \sum_{r=0}^{n} r + (n+1) = \frac{n(n+1)}{2} + (n+1)$$
  
  Using the induction hypothesis and applying real arithmetic:
  
  $$\frac{n(n+1)}{2} + (n+1) = \frac{n(n+1) + 2(n+1)}{2} = \frac{(n+1)(n+2)}{2} = \frac{(n+1)((n+1)+1)}{2}$$
  
  Which is exactly what we needed to prove.

The implementation uses `INDUCT_TAC` to set up the induction, followed by rewriting with sum properties over numerical segments (`SUM_CLAUSES_NUMSEG`), and finishes with real arithmetic simplifications.

### Mathematical insight
This theorem establishes the well-known formula for the sum of the first $n$ natural numbers. It's a fundamental result in discrete mathematics with many applications in combinatorics, probability, and algorithm analysis.

The formula's derivation is commonly attributed to Carl Friedrich Gauss, who supposedly discovered it as a schoolboy. The formula can also be understood geometrically: if we arrange $n$ rows of dots, with $r$ dots in the $r$-th row, we get a triangular pattern containing $\sum_{r=1}^{n} r$ dots. Two such triangles can be arranged to form a rectangle with $n$ rows and $n+1$ columns, containing $n(n+1)$ dots, so each triangle contains $\frac{n(n+1)}{2}$ dots.

### Dependencies
- **Theorems**:
  - `SUM_CLAUSES_NUMSEG`: Provides properties for manipulating sums over numerical segments
  - `LE_0`: Comparison property for natural numbers
  - `GSYM REAL_OF_NUM_SUC`: Relates the successor function to real numbers
  - `REAL_ARITH_TAC`: Automated tactics for real arithmetic

### Porting notes
This theorem should be straightforward to port to other proof assistants. The proof relies on induction and basic arithmetic, which are well-supported in most systems. In Lean or Coq, the property might already exist in the standard library as part of the theory of arithmetic sequences or summations.

---

## REAL_INTEGRABLE_REFLECT_AND_ADD

### Name of formal statement
REAL_INTEGRABLE_REFLECT_AND_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> f real_integrable_on real_interval[&0,a] /\
             (\x. f(--x)) real_integrable_on real_interval[&0,a] /\
             (\x. f x + f(--x)) real_integrable_on real_interval[&0,a]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX];
    SIMP_TAC[REAL_INTEGRABLE_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] REAL_INTEGRABLE_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any real-valued function $f$ and real number $a$, if $f$ is integrable on the interval $[-a,a]$, then:
1. $f$ is integrable on the interval $[0,a]$
2. The function $x \mapsto f(-x)$ is integrable on the interval $[0,a]$
3. The function $x \mapsto f(x) + f(-x)$ is integrable on the interval $[0,a]$

### Informal proof
The proof proceeds in three main steps:

1. First, we show that $f$ is integrable on $[0,a]$. This follows directly from the integrability of $f$ on $[-a,a]$, since $[0,a]$ is a subinterval of $[-a,a]$. This uses the theorem `REAL_INTEGRABLE_SUBINTERVAL`.

2. Next, we show that $x \mapsto f(-x)$ is integrable on $[0,a]$. This is achieved by applying the reflection property of integrability (`REAL_INTEGRABLE_REFLECT`). The proof also uses the fact that $-(-x) = x$ and applies the eta-conversion rule to simplify expressions.

3. Finally, we show that $x \mapsto f(x) + f(-x)$ is integrable on $[0,a]$. This follows from the integrability of both $f$ and $x \mapsto f(-x)$ on $[0,a]$ (which we proved in steps 1 and 2), and the fact that the sum of integrable functions is integrable (`REAL_INTEGRABLE_ADD`).

The proof completes by verifying that $[0,a] \subseteq [-a,a]$, which is a straightforward arithmetic fact.

### Mathematical insight
This theorem establishes important closure properties regarding the integrability of functions under reflection and addition. It shows how integrability on a symmetric interval $[-a,a]$ relates to integrability on the half-interval $[0,a]$, which is useful when dealing with even and odd functions or when decomposing integrals.

The result is particularly useful in real analysis when decomposing integrals over symmetric intervals. For instance, it allows us to split the integral of a function over $[-a,a]$ into components involving $f(x)$ and $f(-x)$ over $[0,a]$, which is a common technique for evaluating integrals of even and odd functions.

### Dependencies
- `REAL_INTEGRABLE_SUBINTERVAL`: States that if a function is integrable on an interval, it is also integrable on any subinterval.
- `REAL_INTEGRABLE_REFLECT`: Relates the integrability of a function to the integrability of its reflection.
- `REAL_INTEGRABLE_ADD`: States that the sum of two integrable functions is integrable.
- `REAL_NEG_NEG`: States that $-(-x) = x$ for real numbers.
- `ETA_AX`: Eta-conversion rule for simplifying function expressions.

### Porting notes
When porting this theorem to other proof assistants, ensure that the system has corresponding theorems for:
1. Integrability of a function on a subinterval
2. Integrability of a reflected function
3. Integrability of the sum of two integrable functions

Additionally, be aware of how different systems handle intervals and subsets of real numbers. The notation and representation may vary significantly across different proof assistants.

---

## REAL_INTEGRAL_REFLECT_AND_ADD

### Name of formal statement
REAL_INTEGRAL_REFLECT_AND_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> real_integral (real_interval[--a,a]) f =
             real_integral (real_interval[&0,a])
                           (\x. f x + f(--x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= a` THENL
   [MP_TAC(SPECL [`f:real->real`; `--a:real`; `a:real`; `&0:real`]
        REAL_INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_REFLECT_AND_ADD] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX; REAL_NEG_0; REAL_ADD_AC];
    ASM_SIMP_TAC[REAL_INTEGRAL_NULL;
                 REAL_ARITH `~(&0 <= a) ==> a <= --a /\ a <= &0`]]);;
```

### Informal statement
For any real-valued function $f$ and real number $a$, if $f$ is integrable on the interval $[-a,a]$, then:

$$\int_{-a}^{a} f(x) \, dx = \int_{0}^{a} (f(x) + f(-x)) \, dx$$

### Informal proof
The proof considers two cases based on whether $a \geq 0$ or $a < 0$.

Case 1: When $a \geq 0$:
- We apply the theorem `REAL_INTEGRAL_COMBINE` to split the integral at $0$:
  $$\int_{-a}^{a} f(x) \, dx = \int_{-a}^{0} f(x) \, dx + \int_{0}^{a} f(x) \, dx$$
- From `REAL_INTEGRABLE_REFLECT_AND_ADD`, we know $f$ is integrable on $[0,a]$ and so is $x \mapsto f(-x)$
- We also use the reflection property of integrals (`REAL_INTEGRAL_REFLECT`):
  $$\int_{-a}^{0} f(x) \, dx = \int_{0}^{a} f(-x) \, dx$$
- Substituting this into our earlier equation:
  $$\int_{-a}^{a} f(x) \, dx = \int_{0}^{a} f(-x) \, dx + \int_{0}^{a} f(x) \, dx = \int_{0}^{a} (f(x) + f(-x)) \, dx$$

Case 2: When $a < 0$:
- If $a < 0$, then $-a > 0$ and the interval $[-a,a]$ has $a$ as its lower bound and $-a$ as its upper bound
- Since $a < -a$, this means the interval is empty or has zero measure 
- Therefore, $\int_{-a}^{a} f(x) \, dx = 0$
- Similarly, the interval $[0,a]$ has negative length, so $\int_{0}^{a} (f(x) + f(-x)) \, dx = 0$
- Thus, the equality holds trivially in this case

### Mathematical insight
This theorem expresses an integral over a symmetric interval $[-a,a]$ in terms of an integral over half the interval $[0,a]$ with a symmetric function. It's a useful transformation for evaluating integrals of functions with specific symmetry properties:

1. For even functions (where $f(-x) = f(x)$), this reduces to $\int_{-a}^{a} f(x) \, dx = 2\int_{0}^{a} f(x) \, dx$
2. For odd functions (where $f(-x) = -f(x)$), this shows that $\int_{-a}^{a} f(x) \, dx = 0$

The theorem is particularly useful in Fourier analysis, where integrals over symmetric intervals frequently appear.

### Dependencies
#### Theorems:
- `REAL_INTEGRAL_COMBINE`: Combines integrals over adjacent intervals
- `REAL_INTEGRAL_ADD`: The integral of a sum equals the sum of integrals
- `REAL_INTEGRAL_REFLECT`: Relates the integral of $f$ over $[a,b]$ to the integral of $f(-x)$ over $[-b,-a]$
- `REAL_INTEGRABLE_REFLECT_AND_ADD`: Shows that if $f$ is integrable on $[-a,a]$, then $f$, $f(-x)$, and $f(x)+f(-x)$ are all integrable on $[0,a]$
- `REAL_INTEGRAL_NULL`: States that the integral over an empty or zero-measure interval is zero

### Porting notes
- Systems with strong automation for real arithmetic may handle the case analysis more directly
- The reflection property of integrals might need to be established separately in other systems
- The handling of improper intervals (where the lower bound exceeds the upper bound) might differ between systems, so the case when $a < 0$ might need special attention

---

## l2product

### Name of formal statement
l2product

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let l2product = new_definition
 `l2product s f g = real_integral s (\x. f(x) * g(x))`;;
```

### Informal statement
The L2 inner product of two functions $f$ and $g$ over a set $s$ is defined as the real integral of their pointwise product:

$$\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$$

where the integral is the real integral over the set $s$.

### Informal proof
This is a definition, not a theorem, so there is no proof to translate.

### Mathematical insight
This definition introduces the L2 inner product (also known as the standard inner product) for square-integrable functions. The L2 inner product is a fundamental concept in functional analysis and forms the basis for the Hilbert space of square-integrable functions.

The inner product gives a way to define:
1. The notion of "length" or norm of a function: $\|f\|_2 = \sqrt{\langle f, f \rangle}$
2. The concept of orthogonality between functions (when the inner product is zero)
3. A foundation for Fourier analysis, where functions are decomposed into orthogonal components

From the context, it's clear this definition is part of the development of the theory of square-integrable functions (L2 space), which is evidenced by the subsequent definitions and theorems about `square_integrable_on` and properties of functions in this space.

### Dependencies
- Definitions:
  - `real_integral`: Integration of real-valued functions

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the target system has a suitable definition of the real integral
2. Be aware that some systems might have different conventions for handling the domain of integration
3. In systems with dependent types, the domain might need to be part of the type of the functions rather than an explicit parameter

---

## l2norm

### Name of formal statement
l2norm

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let l2norm = new_definition
 `l2norm s f = sqrt(l2product s f f)`;;
```

### Informal statement
The $L^2$ norm of a function $f$ over a set $s$ is defined as:

$$\|f\|_{L^2(s)} = \sqrt{\int_s f(x) \cdot f(x) \, dx}$$

where the integral is the real integral over the set $s$.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The $L^2$ norm is a fundamental concept in functional analysis and represents the "size" of a function in terms of its squared values integrated over a domain. It corresponds to the notion of Euclidean distance extended to function spaces.

The $L^2$ norm gives rise to the $L^2$ space, which consists of square-integrable functions (functions whose square has a finite integral). This space is particularly important because:

1. It forms a Hilbert space when equipped with the inner product defined by `l2product`
2. It provides a natural setting for Fourier analysis
3. It connects to the theory of square-integrable random variables in probability

The definition builds upon the `l2product`, which defines the inner product in the $L^2$ space as $\langle f, g \rangle = \int_s f(x)g(x)\,dx$. The norm is then defined as $\|f\| = \sqrt{\langle f, f \rangle}$, following the standard pattern of deriving a norm from an inner product.

### Dependencies
- **Definitions**:
  - `l2product`: Defines the $L^2$ inner product of two functions over a set as the integral of their product
  - `sqrt`: Square root function
  - `real_integral`: Real integral over a set

### Porting notes
When porting this definition:
- Ensure that the underlying integral theory is compatible
- Check how the target system handles partial functions (since the square root is only defined for non-negative numbers)
- Verify that the target system's type system can properly handle function types in the context of integration

---

## L2NORM_LNORM

### Name of formal statement
L2NORM_LNORM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_LNORM = prove
 (`!f s. f square_integrable_on s
         ==> l2norm s f = lnorm (IMAGE lift s) (&2) (lift o f o drop)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[l2norm; lnorm; l2product] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[square_integrable_on]) THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_INTEGRAL] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; RPOW_POW] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(GSYM RPOW_SQRT) THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; REAL_LE_POW_2] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REAL_INTEGRABLE_ON] o CONJUNCT2) THEN
  REWRITE_TAC[o_DEF]);;
```

### Informal statement
For any real-valued function $f$ and set $s$, if $f$ is square-integrable on $s$, then the $L^2$-norm of $f$ on $s$ equals the $L^2$-norm of the corresponding lifted function on the lifted set:

$$\forall f, s. \, f \text{ square_integrable_on } s \Rightarrow \text{l2norm}(s, f) = \text{lnorm}(\text{IMAGE lift } s, 2, \text{lift} \circ f \circ \text{drop})$$

Where:
- $\text{l2norm}(s, f)$ is the $L^2$-norm defined as $\sqrt{\int_s f(x)^2 \, dx}$
- $\text{lnorm}(s, p, f)$ is the general $L^p$-norm defined as $(\int_s \|f(x)\|^p \, dx)^{1/p}$
- $\text{lift}$ is a function that maps a real number to a 1-dimensional vector
- $\text{drop}$ is a function that maps a 1-dimensional vector to a real number

### Informal proof
We need to prove that the $L^2$-norm of $f$ on $s$ equals the $L^2$-norm of $\text{lift} \circ f \circ \text{drop}$ on $\text{IMAGE lift } s$.

- Start by expanding the definitions of $\text{l2norm}$, $\text{lnorm}$, and $\text{l2product}$:
  - $\text{l2norm}(s, f) = \sqrt{\text{l2product}(s, f, f)} = \sqrt{\int_s f(x) \cdot f(x) \, dx}$
  - $\text{lnorm}(\text{IMAGE lift } s, 2, \text{lift} \circ f \circ \text{drop}) = (\int_{\text{IMAGE lift } s} \|(\text{lift} \circ f \circ \text{drop})(x)\|^2 \, dx)^{1/2}$

- From the assumption that $f$ is square-integrable on $s$, we know that $f$ is measurable on $s$ and $f(x)^2$ is integrable on $s$.

- For the right-hand side, we use the fact that $\text{REAL_INTEGRAL}$ relates the integral over a set to the integral over the lifted image of that set.

- We simplify using:
  - $\text{NORM_REAL}$: For a real number lifted to a 1D vector, the norm equals the absolute value
  - $\text{REAL_POW2_ABS}$: $|x|^2 = x^2$
  - $\text{RPOW_POW}$: Relates real power to integer power
  - $\text{RPOW_SQRT}$: $(x^{1/2})^2 = x$ for non-negative $x$

- The integral of $f(x)^2$ over $s$ is non-negative because $f(x)^2 \geq 0$ for all $x$, which justifies the application of $\text{RPOW_SQRT}$.

- Finally, we verify that the integrability conditions are satisfied, using the assumption that $f$ is square-integrable.

### Mathematical insight
This theorem establishes the equivalence between two different representations of the $L^2$-norm: one defined directly using real integrals, and the other using the more general $L^p$-norm framework with $p=2$. This connection is important because:

1. It allows us to leverage results from the general $L^p$ theory when working specifically with $L^2$ functions.
2. The $L^2$ space has special properties (it forms a Hilbert space) that other $L^p$ spaces don't have.
3. This equivalence is particularly useful for building a unified theory of function spaces where functions can be treated both as real-valued and as vector-valued, depending on the context.

The theorem essentially shows that the embedding of real functions into the vector space of functions doesn't change their $L^2$-norm, which is a key property for maintaining consistency between different formalizations.

### Dependencies
#### Definitions
- `lnorm`: The $L^p$-norm of a function, defined as $(\int_s \|f(x)\|^p \, dx)^{1/p}$
- `square_integrable_on`: A function is square-integrable on a set if it is measurable and its square is integrable
- `l2product`: The inner product of two functions in $L^2$, defined as $\int_s f(x) \cdot g(x) \, dx$
- `l2norm`: The $L^2$-norm of a function, defined as $\sqrt{\text{l2product}(s, f, f)}$

### Porting notes
When porting this theorem:
- Ensure that the target system has appropriate definitions for $L^p$ norms and $L^2$ inner products.
- Pay attention to the handling of real vs. vector-valued functions, and how the lifting/embedding between them is defined.
- The proof relies on several properties of real powers and integrals, so verify that similar lemmas exist in the target system.
- Functions operating between reals and vectors (lift/drop) will need to be properly defined in the target system, with their key properties established.

---

## L2PRODUCT_SYM

### L2PRODUCT_SYM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2PRODUCT_SYM = prove
 (`!s f g. l2product s f g = l2product s g f`,
  REWRITE_TAC[l2product; REAL_MUL_SYM]);;
```

### Informal statement
For any set $s$ and functions $f$ and $g$, the $L^2$ product is symmetric:

$$\forall s, f, g. \text{l2product}(s, f, g) = \text{l2product}(s, g, f)$$

where $\text{l2product}(s, f, g)$ is defined as the real integral $\int_s f(x) \cdot g(x) \, dx$.

### Informal proof
The proof directly applies the symmetry of multiplication of real numbers. 

By definition, $\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$. Using the symmetry of real multiplication (i.e., $a \cdot b = b \cdot a$ for real numbers $a$ and $b$), we have $f(x) \cdot g(x) = g(x) \cdot f(x)$ for all $x$. 

Therefore:
$$\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx = \int_s g(x) \cdot f(x) \, dx = \text{l2product}(s, g, f)$$

### Mathematical insight
This theorem establishes the symmetry of the $L^2$ inner product, which is one of the fundamental properties of inner products. In functional analysis, the $L^2$ inner product is defined on the space of square-integrable functions and forms a Hilbert space structure on this function space.

The symmetry property is one of the axioms that an inner product must satisfy. The other axioms include linearity in the first argument, conjugate symmetry (which reduces to symmetry for real functions), and positive definiteness.

This symmetry property is essential for numerous results in functional analysis, including orthogonality relations, the Cauchy-Schwarz inequality, and projection theorems.

### Dependencies
#### Definitions
- `l2product`: Defines the $L^2$ product of two functions over a set as the integral of their pointwise product.

#### Theorems
- `REAL_MUL_SYM`: Establishes the symmetry of real multiplication: $\forall a, b. a \cdot b = b \cdot a$.

### Porting notes
When porting this theorem to other proof assistants, ensure that:
1. The definition of the $L^2$ product is properly established.
2. The underlying real integration theory is available.
3. The symmetry of real multiplication is available or proven.

This theorem should be straightforward to port as it relies only on basic properties of real multiplication and the definition of the $L^2$ product.

---

## L2PRODUCT_POS_LE

### Name of formal statement
L2PRODUCT_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2product s f f`,
  REWRITE_TAC[square_integrable_on; l2product] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REWRITE_TAC[GSYM REAL_POW_2]);;
```

### Informal statement
For any set $s$ and function $f$, if $f$ is square integrable on $s$, then the L2 product of $f$ with itself is non-negative:

$$\forall s,f.\ f \text{ square_integrable_on } s \Rightarrow 0 \leq \text{l2product}(s, f, f)$$

Where:
- A function $f$ is square integrable on $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$.
- The L2 product is defined as $\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$

### Informal proof
The proof shows that the L2 product of a function with itself is non-negative by using properties of real integrals:

1. We start by expanding the definitions of `square_integrable_on` and `l2product`:
   - $f$ is square integrable on $s$ means $f$ is measurable on $s$ and $f^2$ is integrable on $s$
   - $\text{l2product}(s,f,f) = \int_s f(x) \cdot f(x) \, dx = \int_s f(x)^2 \, dx$

2. After applying these definitions, we need to show that $\int_s f(x)^2 \, dx \geq 0$

3. We apply the theorem `REAL_INTEGRAL_POS`, which states that if a function is non-negative everywhere and integrable, then its integral is non-negative.

4. Since $f(x)^2 \geq 0$ for all real values (proved by `REAL_LE_SQUARE`), we know that the integrand is non-negative.

5. We rewrite $f(x) \cdot f(x)$ as $f(x)^2$ using the power definition, which completes the proof.

### Mathematical insight
This theorem establishes a fundamental property of the L2 inner product: when applied to a function with itself, it produces a non-negative value. This is one of the key properties of inner products in general.

In functional analysis, the L2 product forms the basis for the L2 norm and the L2 space of square-integrable functions. This non-negativity property is essential for defining a proper inner product space, which requires that the inner product of an element with itself is always non-negative and equals zero if and only if the element is zero.

The result is intuitive since the L2 product of a function with itself is the integral of the square of the function, and squares of real numbers are always non-negative.

### Dependencies
- **Definitions:**
  - `square_integrable_on`: A function is square integrable on a set if it is measurable and its square is integrable.
  - `l2product`: The L2 inner product of two functions over a set.
- **Theorems used in the proof:**
  - `REAL_INTEGRAL_POS`: If a function is non-negative and integrable, its integral is non-negative.
  - `REAL_LE_SQUARE`: For any real number, its square is non-negative.
  - `GSYM REAL_POW_2`: Relates multiplication of a value with itself to the power notation.

### Porting notes
When porting to other systems:
- Ensure the target system has a well-defined notion of measure theory and real integration.
- In some systems, the definitions of "square integrable" might include additional requirements or use different terminology (e.g., "L2 functions").
- Check how the target system handles the positivity of integrals; some systems may require more explicit reasoning about measurability.

---

## L2NORM_POW_2

### L2NORM_POW_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_POW_2 = prove
 (`!s f. f square_integrable_on s ==> (l2norm s f) pow 2 = l2product s f f`,
  SIMP_TAC[l2norm; SQRT_POW_2; L2PRODUCT_POS_LE]);;
```

### Informal statement
For any set $s$ and function $f$, if $f$ is square integrable on $s$, then the square of the L2-norm of $f$ on $s$ equals the L2-inner product of $f$ with itself on $s$. Formally:

$$\forall s, f. \, f \text{ square integrable on } s \Rightarrow (\text{l2norm } s \, f)^2 = \text{l2product } s \, f \, f$$

### Informal proof
Given a set $s$ and a function $f$ that is square integrable on $s$, we need to prove that $(l2norm \, s \, f)^2 = l2product \, s \, f \, f$.

By the definition of `l2norm`, we have $l2norm \, s \, f = \sqrt{l2product \, s \, f \, f}$.

Therefore, $(l2norm \, s \, f)^2 = (\sqrt{l2product \, s \, f \, f})^2$.

Using the property that $(\sqrt{x})^2 = x$ for any $x \geq 0$, and since `L2PRODUCT_POS_LE` tells us that $l2product \, s \, f \, f \geq 0$ when $f$ is square integrable on $s$, we can conclude that:

$(l2norm \, s \, f)^2 = l2product \, s \, f \, f$

### Mathematical insight
This theorem establishes the fundamental relationship between the L2-norm and the L2-inner product, which is that the square of the L2-norm equals the inner product of a function with itself. This is analogous to the relation in finite-dimensional vector spaces where the square of the Euclidean norm of a vector equals the dot product of the vector with itself.

This property is crucial in functional analysis and is used in the study of Hilbert spaces, where the L2 space is an important example of a Hilbert space. It's also fundamental in applications such as Fourier analysis, partial differential equations, and quantum mechanics.

### Dependencies
- **Theorems:**
  - `L2PRODUCT_POS_LE`: Establishes that for a square integrable function $f$ on a set $s$, the L2-inner product of $f$ with itself is non-negative.
  - `SQRT_POW_2`: A basic property that $(\sqrt{x})^2 = x$ for $x \geq 0$.

- **Definitions:**
  - `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is real measurable on $s$ and the function $x \mapsto f(x)^2$ is real integrable on $s$.
  - `l2product`: The L2-inner product of functions $f$ and $g$ on a set $s$ is defined as the real integral of their pointwise product over $s$.
  - `l2norm`: The L2-norm of a function $f$ on a set $s$ is defined as the square root of the L2-inner product of $f$ with itself.

### Porting notes
When porting this theorem, ensure that:
1. The definitions of square integrability, L2-product, and L2-norm are consistent with those in HOL Light.
2. The target system has appropriate support for real analysis concepts like integrals and measurability.
3. The theorem about the square of a square root being the original number (for non-negative reals) is available in the target system.

---

## L2NORM_POS_LE

### Name of formal statement
L2NORM_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2norm s f`,
  SIMP_TAC[l2norm; SQRT_POS_LE; L2PRODUCT_POS_LE]);;
```

### Informal statement
For any set $s$ and function $f$, if $f$ is square integrable on $s$, then the $L^2$ norm of $f$ on $s$ is non-negative, i.e., $0 \leq \|f\|_{L^2(s)}$.

Formally, $\forall s, f. f \text{ square_integrable_on } s \Rightarrow 0 \leq \text{l2norm } s \ f$

### Informal proof
The theorem is proved by simplifying the definition of `l2norm` and applying appropriate theorems:

- By definition, $\|f\|_{L^2(s)} = \sqrt{\langle f, f \rangle}$, where $\langle f, f \rangle$ is the $L^2$ inner product of $f$ with itself.
- By theorem `L2PRODUCT_POS_LE`, we know that $0 \leq \langle f, f \rangle$ when $f$ is square integrable on $s$.
- By theorem `SQRT_POS_LE`, for any $x \geq 0$, we have $0 \leq \sqrt{x}$.
- Combining these facts, we get $0 \leq \sqrt{\langle f, f \rangle} = \|f\|_{L^2(s)}$.

### Mathematical insight
This theorem establishes the non-negativity of the $L^2$ norm, which is a fundamental property of norms in functional analysis. The $L^2$ norm measures the "size" of a function in the $L^2$ space, and like all norms, it must be non-negative. This property is essential for the $L^2$ space to satisfy the axioms of a normed vector space.

The result follows directly from the definition of the $L^2$ norm as the square root of the $L^2$ inner product of a function with itself, and the fact that this inner product is non-negative for square integrable functions.

### Dependencies
- Theorems:
  - `L2PRODUCT_POS_LE`: The $L^2$ inner product of a function with itself is non-negative for square integrable functions
  - `SQRT_POS_LE`: For any non-negative real number, its square root is also non-negative
- Definitions:
  - `l2norm`: Defines the $L^2$ norm of a function as the square root of its $L^2$ inner product with itself
  - `square_integrable_on`: Defines when a function is square integrable on a set

### Porting notes
This theorem should be straightforward to port to other proof assistants that have libraries for functional analysis or measure theory. The proof relies on basic properties of square roots and inner products, which are typically available in standard libraries. The main requirement is having appropriate definitions for square integrability and the $L^2$ norm.

---

## L2NORM_LE

### L2NORM_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_LE = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f <= l2norm s g <=>
                l2product s f f <= l2product s g g)`,
  SIMP_TAC[SQRT_MONO_LE_EQ; l2norm; SQRT_MONO_LE_EQ; L2PRODUCT_POS_LE]);;
```

### Informal statement
For any set $s$ and functions $f$ and $g$, if both $f$ and $g$ are square integrable on $s$, then the $L^2$ norm of $f$ is less than or equal to the $L^2$ norm of $g$ if and only if the $L^2$ inner product of $f$ with itself is less than or equal to the $L^2$ inner product of $g$ with itself. 

Formally, for any $s$, $f$, and $g$ where $f$ is square integrable on $s$ and $g$ is square integrable on $s$:
$$\|f\|_{L^2(s)} \leq \|g\|_{L^2(s)} \iff \langle f,f \rangle_{L^2(s)} \leq \langle g,g \rangle_{L^2(s)}$$

where $\|f\|_{L^2(s)} = \sqrt{\langle f,f \rangle_{L^2(s)}}$ and $\langle f,g \rangle_{L^2(s)} = \int_s f(x)g(x) dx$.

### Informal proof
This theorem follows directly from the monotonicity of the square root function.

Given that $f$ and $g$ are square integrable on $s$, we know from the theorem `L2PRODUCT_POS_LE` that $\langle f,f \rangle_{L^2(s)} \geq 0$. Since the $L^2$ norm is defined as $\|f\|_{L^2(s)} = \sqrt{\langle f,f \rangle_{L^2(s)}}$, we can apply the theorem `SQRT_MONO_LE_EQ`, which states that for non-negative real numbers $a$ and $b$, $\sqrt{a} \leq \sqrt{b} \iff a \leq b$.

Therefore, 
$$\|f\|_{L^2(s)} \leq \|g\|_{L^2(s)} \iff \sqrt{\langle f,f \rangle_{L^2(s)}} \leq \sqrt{\langle g,g \rangle_{L^2(s)}} \iff \langle f,f \rangle_{L^2(s)} \leq \langle g,g \rangle_{L^2(s)}$$

### Mathematical insight
This theorem establishes the equivalence between comparing $L^2$ norms of functions and comparing the inner products of these functions with themselves. It's a straightforward but important result that allows us to work with squared norms (inner products) instead of the norms themselves, which can be more convenient in many analytical contexts.

The result is a direct consequence of the monotonicity of the square root function and the fact that inner products are non-negative for square integrable functions. This property is often used in functional analysis, particularly in the theory of Hilbert spaces where $L^2$ spaces serve as important examples.

### Dependencies
- **Theorems**:
  - `L2PRODUCT_POS_LE`: For any set $s$ and function $f$ that is square integrable on $s$, the $L^2$ inner product $\langle f,f \rangle_{L^2(s)}$ is greater than or equal to 0.
  - `SQRT_MONO_LE_EQ`: For non-negative real numbers, the square root function is monotonic, i.e., $\sqrt{a} \leq \sqrt{b} \iff a \leq b$ for $a, b \geq 0$.

- **Definitions**:
  - `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$.
  - `l2product`: The $L^2$ inner product of functions $f$ and $g$ on a set $s$ is defined as $\langle f,g \rangle_{L^2(s)} = \int_s f(x)g(x) dx$.
  - `l2norm`: The $L^2$ norm of a function $f$ on a set $s$ is defined as $\|f\|_{L^2(s)} = \sqrt{\langle f,f \rangle_{L^2(s)}}$.

### Porting notes
When porting this theorem to other systems, ensure that the definitions of square integrable functions, $L^2$ inner products, and $L^2$ norms are consistent with those in HOL Light. The proof relies on basic properties of the square root function and should transfer straightforwardly to other systems with appropriate libraries for real analysis.

---

## L2NORM_EQ

### L2NORM_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let L2NORM_EQ = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f = l2norm s g <=>
                l2product s f f = l2product s g g)`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; L2NORM_LE]);;
```

### Informal statement
For any set $s$ and functions $f$ and $g$, if $f$ and $g$ are square integrable on $s$, then the L2-norms of $f$ and $g$ on $s$ are equal if and only if their L2 inner products with themselves are equal. Formally:

$$\forall s\,f\,g.\ f \text{ square\_integrable\_on } s \land g \text{ square\_integrable\_on } s \implies (||f||_2 = ||g||_2 \iff \langle f,f \rangle = \langle g,g \rangle)$$

where $||f||_2 = \sqrt{\langle f,f \rangle}$ is the L2-norm and $\langle f,g \rangle = \int_s f(x)g(x)\,dx$ is the L2 inner product.

### Informal proof
The proof leverages the antisymmetry property of the $\leq$ relation on real numbers, which states that $a = b \iff (a \leq b \land b \leq a)$.

Let $s$ be a set and $f$, $g$ be square integrable functions on $s$. We need to show that $||f||_2 = ||g||_2$ if and only if $\langle f,f \rangle = \langle g,g \rangle$.

By the antisymmetry of $\leq$, we have:
$$||f||_2 = ||g||_2 \iff (||f||_2 \leq ||g||_2 \land ||g||_2 \leq ||f||_2)$$

According to `L2NORM_LE`, for square integrable functions, we have:
$$||f||_2 \leq ||g||_2 \iff \langle f,f \rangle \leq \langle g,g \rangle$$

Similarly:
$$||g||_2 \leq ||f||_2 \iff \langle g,g \rangle \leq \langle f,f \rangle$$

Therefore:
$$||f||_2 = ||g||_2 \iff (\langle f,f \rangle \leq \langle g,g \rangle \land \langle g,g \rangle \leq \langle f,f \rangle) \iff \langle f,f \rangle = \langle g,g \rangle$$

This completes the proof.

### Mathematical insight
This theorem establishes a fundamental property of L2 norms - that equality of norms is equivalent to equality of the inner products of functions with themselves. This is a direct consequence of the fact that the L2 norm is defined as the square root of the inner product of a function with itself.

The result is particularly important in functional analysis and L2 space theory, as it connects the metric structure (given by the norm) with the inner product structure. It's a special case of a more general principle that in Hilbert spaces, the norm is induced by the inner product.

### Dependencies

#### Theorems
- `L2NORM_LE`: States that for square integrable functions $f$ and $g$ on a set $s$, $||f||_2 \leq ||g||_2$ if and only if $\langle f,f \rangle \leq \langle g,g \rangle$
- `REAL_LE_ANTISYM`: The antisymmetry property of $\leq$ for real numbers: $a \leq b \land b \leq a \iff a = b$

#### Definitions
- `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$
- `l2product`: The L2 inner product, defined as $\langle f,g \rangle = \int_s f(x)g(x)\,dx$
- `l2norm`: The L2 norm, defined as $||f||_2 = \sqrt{\langle f,f \rangle}$

---

## SCHWARTZ_INEQUALITY_STRONG

### Name of formal statement
SCHWARTZ_INEQUALITY_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY_STRONG = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s (\x. abs(f x)) (\x. abs(g x))
               <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] HOELDER_INEQUALITY) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; GSYM L2NORM_LNORM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  REWRITE_TAC[l2product] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; REAL_LE_REFL]);;
```

### Informal statement
For any real-valued functions $f$ and $g$ that are square-integrable on a set $s$, the following inequality holds:
$$\int_s |f(x)| \cdot |g(x)| \, dx \leq \sqrt{\int_s f(x)^2 \, dx} \cdot \sqrt{\int_s g(x)^2 \, dx}$$

This is the Cauchy-Schwarz inequality in the $L^2$ space (or Schwartz inequality), expressed using the $L^2$ inner product and norm.

### Informal proof
The proof applies Hölder's inequality in the $L^2$ space and uses the properties of square integrable functions.

* First, we apply Hölder's inequality with $p = q = 2$ to the functions $f$ and $g$ lifted to the appropriate space.
* The Hölder inequality with equal exponents becomes the Cauchy-Schwarz inequality.
* We use `SQUARE_INTEGRABLE_LSPACE` to convert between the square-integrable property and membership in the $L^2$ space.
* Similarly, we use `L2NORM_LNORM` to relate the $L^2$ norm to the general $L^p$ norm with $p = 2$.
* We then apply transitivity of inequalities, and use the fact that the $L^2$ product of absolute values equals the integral of the product of absolute values.
* Finally, we verify that square-integrability is preserved by taking absolute values (`SQUARE_INTEGRABLE_ABS`) and that the product of square-integrable functions is integrable (`SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`).

The key insight is mapping the problem from the real-valued function space to the $L^p$ space framework, applying the Hölder inequality there, and then mapping the result back.

### Mathematical insight
The Cauchy-Schwarz inequality is a fundamental inequality in functional analysis and plays a crucial role in the theory of Hilbert spaces. This theorem provides a strong version of the inequality for the $L^2$ space, working with absolute values of functions.

The inequality can be interpreted geometrically as showing that the "angle" between two square-integrable functions is at most 90 degrees in the $L^2$ space, mirroring the dot product inequality in finite-dimensional vector spaces.

This form with absolute values is particularly useful because it relates the integral of the product of the magnitudes of two functions to the product of their $L^2$ norms, providing a powerful tool for estimation in analysis.

### Dependencies
- **Theorems**:
  - `HOELDER_INEQUALITY`: General Hölder inequality for $L^p$ spaces
  - `SQUARE_INTEGRABLE_LSPACE`: Equivalence between square integrability and membership in $L^2$
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: Product of square-integrable functions is integrable
  - `SQUARE_INTEGRABLE_ABS`: Square integrability is preserved under absolute value
  - `L2NORM_LNORM`: Relation between the $L^2$ norm and the general $L^p$ norm

- **Definitions**:
  - `square_integrable_on`: Property that a function is measurable and its square is integrable
  - `l2product`: The $L^2$ inner product as an integral of the product
  - `l2norm`: The $L^2$ norm as the square root of the self inner product

### Porting notes
When porting this theorem:
1. Ensure that the $L^2$ space and square integrability concepts are properly defined in your target system
2. The most challenging part might be the handling of embedding functions between real numbers and 1D vectors (the `lift` and `drop` operations)
3. Verify that your implementation of Hölder's inequality handles the case $p = q = 2$ correctly

---

## SCHWARTZ_INEQUALITY_ABS

### SCHWARTZ_INEQUALITY_ABS
- The exact name of the formal item is `SCHWARTZ_INEQUALITY_ABS`.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY_ABS = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> abs(l2product s f g) <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `l2product s (\x. abs(f x)) (\x. abs(g x))` THEN
  ASM_SIMP_TAC[SCHWARTZ_INEQUALITY_STRONG] THEN REWRITE_TAC[l2product] THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_LE_REFL]);;
```

### Informal statement
For any real-valued functions $f$ and $g$ that are square integrable on a set $s$, the absolute value of their $L^2$ inner product is bounded by the product of their $L^2$ norms:

$$\forall f,g,s. \text{if } f \text{ is square integrable on } s \text{ and } g \text{ is square integrable on } s \text{ then } |\langle f, g \rangle_{L^2(s)}| \leq \|f\|_{L^2(s)} \cdot \|g\|_{L^2(s)}$$

where:
- $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) \, dx$ is the $L^2$ inner product
- $\|f\|_{L^2(s)} = \sqrt{\langle f, f \rangle_{L^2(s)}} = \sqrt{\int_s f(x)^2 \, dx}$ is the $L^2$ norm

### Informal proof
The proof uses the strong version of Schwartz inequality and properties of real integrals:

1. We first establish the transitive inequality chain:
   $$|⟨f, g⟩_{L^2(s)}| \leq ⟨|f|, |g|⟩_{L^2(s)} \leq \|f\|_{L^2(s)} \cdot \|g\|_{L^2(s)}$$

2. For the first inequality:
   * We use the fact that $|\int_s f(x)g(x) \, dx| \leq \int_s |f(x)g(x)| \, dx$ (property of absolute value of integrals)
   * Since $|f(x)g(x)| = |f(x)||g(x)|$, we have $|\int_s f(x)g(x) \, dx| \leq \int_s |f(x)||g(x)| \, dx$
   * This gives us $|⟨f, g⟩_{L^2(s)}| \leq ⟨|f|, |g|⟩_{L^2(s)}$

3. For the second inequality:
   * Apply the strong Schwartz inequality which states:
     $⟨|f|, |g|⟩_{L^2(s)} \leq \|f\|_{L^2(s)} \cdot \|g\|_{L^2(s)}$

4. The proof uses the fact that if functions are square integrable, then their absolute values are also square integrable, and the product of square integrable functions is integrable.

### Mathematical insight
The Schwartz inequality (also known as Cauchy-Schwarz inequality) is one of the most fundamental inequalities in functional analysis and the theory of inner product spaces. This version specifically addresses the $L^2$ space of square-integrable functions.

The inequality establishes a relationship between the inner product of two functions and their norms, effectively showing that the correlation between functions (represented by their inner product) is bounded by the product of their individual "sizes" (represented by their norms).

This inequality is crucial in many areas of mathematics and physics:
- It provides a foundation for defining distances in function spaces
- It's essential for proving completeness of $L^2$ spaces
- It's used extensively in Fourier analysis, PDEs, and quantum mechanics

The absolute value in this version makes it particularly useful in applications where the sign of the inner product doesn't matter.

### Dependencies
- **Theorems**:
  - `SCHWARTZ_INEQUALITY_STRONG`: The strong form of the Schwartz inequality
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: Square integrable functions have integrable products
  - `SQUARE_INTEGRABLE_ABS`: A function is square integrable implies its absolute value is square integrable
  - `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`: Bounds on absolute value of integrals

- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set
  - `l2product`: The $L^2$ inner product of two functions
  - `l2norm`: The $L^2$ norm of a function

### Porting notes
When porting to other proof assistants:
1. Ensure that the target system has a well-defined theory of integration, particularly Lebesgue integration
2. Pay attention to how the target system handles measurability conditions
3. The definition of square_integrable_on requires both measurability and integrability of the squared function
4. The inequality relies on basic properties of absolute values and integrals that should be available in most systems, but the exact form may vary

---

## SCHWARTZ_INEQUALITY

### Name of formal statement
SCHWARTZ_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s f g <= l2norm s f * l2norm s g`,
  MESON_TAC[SCHWARTZ_INEQUALITY_ABS;
            REAL_ARITH `abs x <= a ==> x <= a`]);;
```

### Informal statement
For all functions $f$ and $g$ and a set $s$, if $f$ and $g$ are square integrable on $s$, then the L2 product of $f$ and $g$ over $s$ is bounded by the product of their L2 norms:
$$\forall f,g,s. \text{ if } f \text{ square\_integrable\_on } s \land g \text{ square\_integrable\_on } s \text{ then } l2product(s,f,g) \leq l2norm(s,f) \cdot l2norm(s,g)$$

where:
- $f$ is square integrable on $s$ means $f$ is measurable on $s$ and $f^2$ is integrable on $s$
- $l2product(s,f,g) = \int_s f(x)g(x)dx$
- $l2norm(s,f) = \sqrt{l2product(s,f,f)} = \sqrt{\int_s f(x)^2 dx}$

### Informal proof
This theorem is proved by applying the absolute version of Schwartz inequality (SCHWARTZ_INEQUALITY_ABS) and a basic fact from real arithmetic.

The proof proceeds as follows:
- From SCHWARTZ_INEQUALITY_ABS, we have $|l2product(s,f,g)| \leq l2norm(s,f) \cdot l2norm(s,g)$.
- By a basic arithmetic fact, if $|x| \leq a$, then $x \leq a$.
- Therefore, $l2product(s,f,g) \leq l2norm(s,f) \cdot l2norm(s,g)$.

This proof uses MESON_TAC to automate the reasoning, applying SCHWARTZ_INEQUALITY_ABS and the arithmetic property to establish the result.

### Mathematical insight
The Schwartz inequality (also known as Cauchy-Schwarz inequality in L2 spaces) is a fundamental result in functional analysis. It establishes the relationship between the inner product of two functions and their norms, providing an upper bound for the inner product.

This theorem is critical in various applications including:
- Function approximation in Hilbert spaces
- Error estimation in numerical analysis
- Signal processing applications
- Proving the triangle inequality for L2 spaces

The inequality is part of the broader family of Hölder inequalities and is a cornerstone result for working with L2 spaces. This specific formulation provides the non-absolute version, which is often more directly applicable when the L2 product is known to be non-negative or when the direction of the inequality matters.

### Dependencies
- Theorems:
  - `SCHWARTZ_INEQUALITY_ABS`: The absolute version of Schwartz inequality, stating that $|l2product(s,f,g)| \leq l2norm(s,f) \cdot l2norm(s,g)$
  - `REAL_ARITH`: Used with the fact that if $|x| \leq a$ then $x \leq a$

- Definitions:
  - `square_integrable_on`: Defines when a function is square integrable on a set
  - `l2product`: Defines the L2 inner product of two functions over a set
  - `l2norm`: Defines the L2 norm of a function over a set

### Porting notes
When porting this theorem:
1. Ensure that the definitions of square_integrable_on, l2product, and l2norm are properly implemented first.
2. The absolute version (SCHWARTZ_INEQUALITY_ABS) must be proved before this theorem.
3. In systems with well-developed functional analysis libraries, similar results may already exist and can be leveraged.
4. In some systems, you might need to handle the arithmetic fact separately if automation like REAL_ARITH is not available.

---

## L2NORM_TRIANGLE

### L2NORM_TRIANGLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2NORM_TRIANGLE = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2norm s (\x. f x + g x) <= l2norm s f + l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] LNORM_TRIANGLE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; L2NORM_LNORM;
               SQUARE_INTEGRABLE_ADD] THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;
```

### Informal statement
For any real-valued functions $f,g$ and set $s$, if $f$ and $g$ are square-integrable on $s$, then
$$\|f + g\|_{L^2(s)} \leq \|f\|_{L^2(s)} + \|g\|_{L^2(s)}$$

where $\|f\|_{L^2(s)}$ denotes the $L^2$ norm of $f$ on $s$, defined as $\sqrt{\int_s |f(x)|^2 \, dx}$.

### Informal proof
This theorem is essentially the triangle inequality for the $L^2$ norm. The proof proceeds as follows:

- We apply the more general result `LNORM_TRIANGLE` for $L^p$ spaces with $p = 2$.
- The `LNORM_TRIANGLE` theorem states that for functions in an $L^p$ space where $p \geq 1$, the triangle inequality holds: $\|f + g\|_p \leq \|f\|_p + \|g\|_p$.
- We apply this to the image of set $s$ lifted to the real vector space, and to the composition of functions $f$ and $g$ with lift and drop operations.
- We use `SQUARE_INTEGRABLE_LSPACE` to convert between the "square integrable" predicate and membership in the $L^2$ space.
- We use `L2NORM_LNORM` to show that the $L^2$ norm equals the $L^2$ space norm for the lifted functions.
- Finally, we use `SQUARE_INTEGRABLE_ADD` to show that the sum of square integrable functions is square integrable.

### Mathematical insight
The triangle inequality for the $L^2$ norm is a fundamental property that establishes the $L^2$ space of square-integrable functions as a normed vector space. This is a specific case of the Minkowski inequality for $L^p$ spaces.

This property is essential for analysis in Hilbert spaces, particularly when working with Fourier analysis, function approximation, and various applications in physics and engineering where the $L^2$ norm corresponds to energy or power.

The theorem confirms that the distance function induced by the $L^2$ norm satisfies the triangle inequality, making the space of square-integrable functions a metric space.

### Dependencies
- `LNORM_TRIANGLE`: The triangle inequality for general $L^p$ norms with $p \geq 1$
- `SQUARE_INTEGRABLE_LSPACE`: Equivalence between square-integrable functions and $L^2$ space membership
- `SQUARE_INTEGRABLE_ADD`: Sum of square-integrable functions is square-integrable
- `L2NORM_LNORM`: Connection between $L^2$ norm and the general $L^p$ norm with $p = 2$

### Porting notes
When porting to another system, ensure that:
1. The underlying theory of measurable functions and $L^p$ spaces is available
2. The lift/drop operations for converting between real values and 1-dimensional vectors are properly handled
3. The connection between the square-integrable predicate and $L^2$ space membership is established

---

## L2PRODUCT_LADD

### Name of formal statement
L2PRODUCT_LADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x + g x) h =
            l2product s f h + l2product s g h`,
  SIMP_TAC[l2product; REAL_ADD_RDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```

### Informal statement
For any set $s$ and functions $f$, $g$, and $h$, if $f$, $g$, and $h$ are all square integrable on $s$, then the L2 product of the sum $(f + g)$ with $h$ equals the sum of their individual L2 products:

$$\text{l2product}(s, f + g, h) = \text{l2product}(s, f, h) + \text{l2product}(s, g, h)$$

where $\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$ is the inner product in the $L^2$ space.

### Informal proof
The proof uses the linearity property of integration and the distributive property of multiplication over addition.

Given that $f$, $g$, and $h$ are all square integrable on $s$, we have:

$$\begin{align}
\text{l2product}(s, f + g, h) &= \int_s (f(x) + g(x)) \cdot h(x) \, dx \\
&= \int_s (f(x) \cdot h(x) + g(x) \cdot h(x)) \, dx \\
&= \int_s f(x) \cdot h(x) \, dx + \int_s g(x) \cdot h(x) \, dx \\
&= \text{l2product}(s, f, h) + \text{l2product}(s, g, h)
\end{align}$$

The second step uses the distributive property of multiplication over addition (`REAL_ADD_RDISTRIB`). The third step uses the additivity of integration (`REAL_INTEGRAL_ADD`), which is applicable because the products $f \cdot h$ and $g \cdot h$ are both integrable. The integrability follows from `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`, which guarantees that the product of two square integrable functions is integrable.

### Mathematical insight
This theorem establishes the linearity of the L2 inner product in its first argument, which is a fundamental property of inner product spaces. This property, together with similar ones like conjugate symmetry and positive definiteness, defines the structure of an inner product space, which is crucial in functional analysis and the study of Hilbert spaces.

The L2 inner product is particularly important in Fourier analysis, quantum mechanics, and signal processing, where functions are represented as elements of function spaces and their properties are studied through inner products.

### Dependencies
- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it is measurable and its square is integrable.
  - `l2product`: The L2 product (inner product) of two functions on a set, defined as the integral of their product.

- **Theorems**:
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: If two functions are square integrable, then their product is integrable.
  - `REAL_ADD_RDISTRIB`: Distributive property of multiplication over addition for real numbers.
  - `REAL_INTEGRAL_ADD`: The integral of a sum equals the sum of integrals (additivity of integration).

### Porting notes
When porting this theorem:
1. Ensure that the definition of square integrability includes both measurability and integrability of the square.
2. Verify that the target system has established that products of square integrable functions are integrable.
3. The proof relies on standard properties of real integrals (additivity and compatibility with multiplication), which should be available in most systems, but may have different names.

---

## L2PRODUCT_RADD

### Name of formal statement
L2PRODUCT_RADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x + h x) =
            l2product s f g + l2product s f h`,
  SIMP_TAC[l2product; REAL_ADD_LDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```

### Informal statement
For any set $s$ and functions $f$, $g$, and $h$, if $f$, $g$, and $h$ are all square integrable on $s$, then:
$$\langle f, g + h \rangle_s = \langle f, g \rangle_s + \langle f, h \rangle_s$$

where $\langle f, g \rangle_s$ denotes the $L^2$ inner product of $f$ and $g$ on $s$, defined as $\langle f, g \rangle_s = \int_s f(x)g(x) \, dx$.

### Informal proof
We need to prove that $\langle f, g + h \rangle_s = \langle f, g \rangle_s + \langle f, h \rangle_s$ when $f$, $g$, and $h$ are all square integrable on $s$.

By definition of the $L^2$ inner product:
- $\langle f, g + h \rangle_s = \int_s f(x)(g(x) + h(x)) \, dx$
- $\langle f, g \rangle_s = \int_s f(x)g(x) \, dx$
- $\langle f, h \rangle_s = \int_s f(x)h(x) \, dx$

Using the distributive property of multiplication over addition:
$$f(x)(g(x) + h(x)) = f(x)g(x) + f(x)h(x)$$

Since $f$, $g$, and $h$ are all square integrable on $s$, the theorem `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` ensures that the products $f(x)g(x)$ and $f(x)h(x)$ are both integrable on $s$.

Therefore, we can apply the linearity of integration to obtain:
$$\int_s f(x)(g(x) + h(x)) \, dx = \int_s (f(x)g(x) + f(x)h(x)) \, dx = \int_s f(x)g(x) \, dx + \int_s f(x)h(x) \, dx$$

This gives us $\langle f, g + h \rangle_s = \langle f, g \rangle_s + \langle f, h \rangle_s$, as required.

### Mathematical insight
This theorem establishes that the $L^2$ inner product is linear in its second argument. This is one of the key properties of an inner product space, which is essential in functional analysis and the theory of Hilbert spaces.

The $L^2$ inner product is particularly important in Fourier analysis, quantum mechanics, and many areas of mathematical physics, where it enables the representation of functions in terms of orthogonal basis functions.

The linearity property is crucial for many applications, including projection theorems, orthogonalization processes, and spectral decompositions. Combined with conjugate symmetry (in the complex case) and positive-definiteness, it defines the structure of an inner product space.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: If $f$ and $g$ are square integrable on $s$, then their product $f(x) \cdot g(x)$ is integrable on $s$
  - `REAL_INTEGRAL_ADD`: Linearity of integration with respect to addition
  - `REAL_ADD_LDISTRIB`: Left distributive property of multiplication over addition for real numbers

- **Definitions**:
  - `square_integrable_on`: $f$ is square integrable on $s$ if $f$ is measurable on $s$ and $f(x)^2$ is integrable on $s$
  - `l2product`: The $L^2$ inner product, defined as $l2product\ s\ f\ g = \int_s f(x)g(x) \, dx$

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the underlying theory of integration and measurability is available
2. The definitions of square integrability and $L^2$ inner product are standard in mathematical analysis, but their formalization may vary across systems
3. This proof relies on the linearity of integration, which should be established first

---

## L2PRODUCT_LSUB

### Name of formal statement
L2PRODUCT_LSUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x - g x) h =
            l2product s f h - l2product s g h`,
  SIMP_TAC[l2product; REAL_SUB_RDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```

### Informal statement
For any set $s$ and real-valued functions $f$, $g$, and $h$, if $f$, $g$, and $h$ are all square-integrable on $s$ (i.e., measurable with square-integrable), then the L2 inner product between $(f - g)$ and $h$ equals the difference of the L2 inner products of $f$ with $h$ and $g$ with $h$:

$$\text{l2product}(s, f - g, h) = \text{l2product}(s, f, h) - \text{l2product}(s, g, h)$$

where $\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$.

### Informal proof
This theorem follows directly from the properties of integrals and the definition of the L2 product:

1. By the definition of `l2product`, we have:
   $$\text{l2product}(s, f-g, h) = \int_s (f(x)-g(x)) \cdot h(x) \, dx$$

2. By the distributive property of multiplication over subtraction:
   $$\int_s (f(x)-g(x)) \cdot h(x) \, dx = \int_s (f(x) \cdot h(x) - g(x) \cdot h(x)) \, dx$$

3. Using the linearity of integration:
   $$\int_s (f(x) \cdot h(x) - g(x) \cdot h(x)) \, dx = \int_s f(x) \cdot h(x) \, dx - \int_s g(x) \cdot h(x) \, dx$$

4. By the definition of `l2product` again:
   $$\int_s f(x) \cdot h(x) \, dx - \int_s g(x) \cdot h(x) \, dx = \text{l2product}(s, f, h) - \text{l2product}(s, g, h)$$

The theorem requires that $f$, $g$, and $h$ are all square-integrable on $s$ to ensure that all the products $(f-g) \cdot h$, $f \cdot h$, and $g \cdot h$ are integrable, which is guaranteed by `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`.

### Mathematical insight
This theorem establishes the linearity of the L2 inner product in its first argument. The L2 inner product is a fundamental concept in functional analysis and Hilbert spaces, particularly in $L^2$ spaces of square-integrable functions.

The linearity property is essential for the L2 inner product to satisfy the axioms of an inner product space. This theorem specifically demonstrates the distributive property with respect to subtraction in the first argument, which is a key component of linearity.

In practical applications, such as Fourier analysis or when working with orthogonal function systems, this property is frequently used when decomposing functions into linear combinations of basis functions.

### Dependencies
- **Definitions**:
  - `l2product`: Defines the L2 inner product as the integral of the product of two functions
  - `square_integrable_on`: A function is square integrable if it's measurable and its square is integrable

- **Theorems**:
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: If two functions are square integrable, their product is integrable
  - `REAL_SUB_RDISTRIB`: Distributivity of multiplication over subtraction for reals
  - `REAL_INTEGRAL_SUB`: Linearity of integration with respect to subtraction

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has an appropriate definition of square-integrable functions and L2 inner products
2. Check how the target system handles measurability and integrability of functions
3. This proof relies on basic properties of real integrals; most proof assistants with developed real analysis libraries should have similar theorems

---

## L2PRODUCT_RSUB

### Name of formal statement
L2PRODUCT_RSUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x - h x) =
            l2product s f g - l2product s f h`,
  SIMP_TAC[l2product; REAL_SUB_LDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```

### Informal statement
For any set $s$ and functions $f$, $g$, and $h$, if $f$, $g$, and $h$ are square integrable on $s$, then:

$$\langle f, g - h \rangle_s = \langle f, g \rangle_s - \langle f, h \rangle_s$$

where $\langle f, g \rangle_s = \int_s f(x) \cdot g(x) \, dx$ denotes the $L^2$ inner product on $s$.

### Informal proof
This theorem states that the $L^2$ inner product distributes over subtraction in its second argument.

The proof follows directly from:
1. The definition of the $L^2$ inner product: $\langle f, g \rangle_s = \int_s f(x) \cdot g(x) \, dx$
2. The distributive property of real multiplication over subtraction: $f(x) \cdot (g(x) - h(x)) = f(x) \cdot g(x) - f(x) \cdot h(x)$
3. The linearity of integration, specifically that $\int_s (a(x) - b(x)) \, dx = \int_s a(x) \, dx - \int_s b(x) \, dx$
4. The fact that if $f$ and $g$ are square integrable on $s$, then their product $f \cdot g$ is integrable on $s$

By applying these properties in sequence, we get:
$$\langle f, g - h \rangle_s = \int_s f(x) \cdot (g(x) - h(x)) \, dx = \int_s (f(x) \cdot g(x) - f(x) \cdot h(x)) \, dx = \int_s f(x) \cdot g(x) \, dx - \int_s f(x) \cdot h(x) \, dx = \langle f, g \rangle_s - \langle f, h \rangle_s$$

### Mathematical insight
This theorem establishes one of the fundamental properties of inner products: linearity in the second argument. The $L^2$ inner product is a canonical example of an inner product space in functional analysis, and this property is essential for many theoretical results in Hilbert spaces.

The theorem is particularly important when working with orthogonal projections, Fourier analysis, or any context involving function spaces where the $L^2$ inner product is used. It's a direct consequence of the linearity of integration and the distributive property of multiplication.

### Dependencies
- **Definitions:**
  - `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable on that set
  - `l2product`: Defines the $L^2$ inner product on a set as the integral of the product of two functions

- **Theorems:**
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: If two functions are square integrable, then their product is integrable
  - `REAL_SUB_LDISTRIB`: Left distributivity of multiplication over subtraction for real numbers
  - `REAL_INTEGRAL_SUB`: Linearity of integration with respect to subtraction

### Porting notes
When porting this theorem to other proof assistants, ensure that:
1. The `l2product` is properly defined as an inner product
2. The notion of square integrability is correctly set up
3. The linearity properties of integration are available
4. The proof is likely to be equally straightforward in most proof assistants that have a well-developed theory of integration

---

## L2PRODUCT_LZERO

### Name of formal statement
L2PRODUCT_LZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LZERO = prove
 (`!s f. l2product s (\x. &0) f = &0`,
  REWRITE_TAC[l2product; REAL_MUL_LZERO; REAL_INTEGRAL_0]);;
```

### Informal statement
For any set $s$ and function $f$, the $L^2$ inner product of the zero function with $f$ equals zero:

$$\forall s, f.\ \langle 0, f \rangle_{L^2(s)} = 0$$

where $\langle f, g \rangle_{L^2(s)}$ represents the inner product defined by $\int_s f(x) \cdot g(x) \, dx$.

### Informal proof
The proof follows directly by applying the definition of the $L^2$ product and simplifying:

1. By definition, $\langle 0, f \rangle_{L^2(s)} = \int_s 0 \cdot f(x) \, dx$
2. Since $0 \cdot f(x) = 0$ for all $x$ (using the left-zero property of multiplication)
3. The integral of the constant function 0 is 0

Therefore, $\langle 0, f \rangle_{L^2(s)} = 0$.

### Mathematical insight
This theorem establishes one of the basic properties of the $L^2$ inner product space - namely that the zero function is the additive identity element in this space. This is an expected property of any inner product space, where the inner product of the zero element with any other element must be zero.

This result forms part of the foundation for functional analysis, particularly when working with function spaces like $L^2$, which are widely used in analysis, partial differential equations, and quantum mechanics.

### Dependencies
- **Definitions**:
  - `l2product`: Defines the $L^2$ inner product between two functions as the integral of their product over a set
  
- **Theorems**:
  - `REAL_MUL_LZERO`: States that multiplying any real number by zero on the left yields zero
  - `REAL_INTEGRAL_0`: States that the integral of the constant function 0 equals 0

### Porting notes
When porting to other proof assistants, ensure that:
1. The underlying integration theory is compatible
2. The definition of the $L^2$ product is consistent with the standard mathematical definition
3. The basic properties of real multiplication and integration are available

---

## L2PRODUCT_RZERO

### Name of formal statement
L2PRODUCT_RZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RZERO = prove
 (`!s f. l2product s f (\x. &0) = &0`,
  REWRITE_TAC[l2product; REAL_MUL_RZERO; REAL_INTEGRAL_0]);;
```

### Informal statement
For any set $s$ and function $f$, the L2 product of $f$ with the zero function is zero:
$$\forall s, f. \langle f, 0 \rangle_{L^2(s)} = 0$$

where $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) dx$ is the L2 inner product.

### Informal proof
The proof is straightforward:
1. Expand the definition of L2 product: $\langle f, 0 \rangle_{L^2(s)} = \int_s f(x) \cdot 0 dx$
2. For any $x$, we have $f(x) \cdot 0 = 0$
3. The integral of the zero function is zero: $\int_s 0 dx = 0$

These steps are directly implemented using the rewriting tactics with the appropriate theorems.

### Mathematical insight
This theorem establishes one of the fundamental properties of the L2 inner product: the inner product of any function with the zero function equals zero. This is one of the axioms of inner product spaces, and is required for the L2 space to form a proper inner product space. This property is part of showing that the L2 product satisfies all the requirements of an inner product.

### Dependencies
- **Definitions**:
  - `l2product`: Defines the L2 inner product as `l2product s f g = real_integral s (λx. f(x) * g(x))`

- **Theorems**:
  - `REAL_MUL_RZERO`: States that for any real number x, x * 0 = 0
  - `REAL_INTEGRAL_0`: States that the integral of the zero function is zero

### Porting notes
When porting this theorem, ensure that the L2 inner product is properly defined in your target system, and that the necessary properties of real multiplication and integration are available. This theorem is straightforward to prove in most proof assistants that have support for real analysis.

---

## L2PRODUCT_LSUM

### Name of formal statement
L2PRODUCT_LSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s (\x. sum t (\i. f i x)) g =
            sum t (\i. l2product s (f i) g)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  ASM_CASES_TAC `g square_integrable_on s` THEN ASM_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[L2PRODUCT_LZERO; SUM_CLAUSES; L2PRODUCT_LADD;
               SQUARE_INTEGRABLE_SUM; ETA_AX; IN_INSERT]);;
```

### Informal statement
For any set $s$, functions $f$ and $g$, and finite set $t$, if $t$ is finite, each function $f(i)$ for $i \in t$ is square integrable on $s$, and $g$ is square integrable on $s$, then the L2 product of the sum of functions and $g$ equals the sum of L2 products:

$$\langle \sum_{i \in t} f_i, g \rangle_{L^2(s)} = \sum_{i \in t} \langle f_i, g \rangle_{L^2(s)}$$

where $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) \, dx$ is the L2 inner product.

### Informal proof
We prove this theorem by induction on the finite set $t$.

First, we separate our assumptions using `ASM_CASES_TAC` and `ASM_REWRITE_TAC` to handle the case where $g$ is square integrable on $s$.

For the induction proof:
- **Base case**: When $t = \emptyset$, we have:
  $$\langle \sum_{i \in \emptyset} f_i, g \rangle_{L^2(s)} = \langle 0, g \rangle_{L^2(s)} = 0 = \sum_{i \in \emptyset} \langle f_i, g \rangle_{L^2(s)}$$
  where we used `L2PRODUCT_LZERO` to establish that $\langle 0, g \rangle_{L^2(s)} = 0$.

- **Inductive step**: For $t \cup \{a\}$ where $a \notin t$, assuming the result holds for $t$:
  $$\begin{align*}
  \langle \sum_{i \in t \cup \{a\}} f_i, g \rangle_{L^2(s)} &= \langle \sum_{i \in t} f_i + f_a, g \rangle_{L^2(s)} \\
  &= \langle \sum_{i \in t} f_i, g \rangle_{L^2(s)} + \langle f_a, g \rangle_{L^2(s)} \\
  &= \sum_{i \in t} \langle f_i, g \rangle_{L^2(s)} + \langle f_a, g \rangle_{L^2(s)} \\
  &= \sum_{i \in t \cup \{a\}} \langle f_i, g \rangle_{L^2(s)}
  \end{align*}$$

  The second equality uses `L2PRODUCT_LADD`, which states that the L2 product distributes over addition in the first argument. The third equality applies the induction hypothesis, and the final equality follows from the definition of sum over a set.

The simplification uses `SQUARE_INTEGRABLE_SUM` to establish that the sum of square integrable functions is also square integrable, which is necessary to apply `L2PRODUCT_LADD`.

### Mathematical insight
This theorem establishes linearity in the first argument of the L2 inner product with respect to finite sums. This is a fundamental property of inner products that allows us to decompose complex expressions into simpler ones. It's particularly important in functional analysis, Hilbert space theory, and Fourier analysis where we often need to work with sums of functions and their inner products.

The result is canonical because it demonstrates that the L2 product behaves as expected for an inner product space, satisfying the linearity property. This theorem enables breaking down complicated integrals involving sums into simpler individual terms, which is crucial for many applications in analysis and partial differential equations.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_SUM`: Finite sum of square integrable functions is square integrable
  - `L2PRODUCT_LADD`: L2 product distributes over addition in the first argument
  - `L2PRODUCT_LZERO`: L2 product of the zero function with any function is zero

- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable
  - `l2product`: The L2 inner product defined as the integral of the product of two functions

### Porting notes
When porting this theorem:
1. Ensure your target system has proper definitions for square integrability and L2 inner products
2. The proof relies on induction over finite sets, so make sure your system has appropriate finite set induction principles
3. You may need to establish distributivity properties of the inner product before proving this theorem
4. The theorem assumes but doesn't explicitly check that the sum is well-defined, so ensure your target system captures this assumption

---

## L2PRODUCT_RSUM

### Name of formal statement
L2PRODUCT_RSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s g (\x. sum t (\i. f i x)) =
            sum t (\i. l2product s g (f i))`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN REWRITE_TAC[L2PRODUCT_LSUM]);;
```

### Informal statement
For any set $s$, functions $f$ and $g$, and a finite set $t$, if:
- $t$ is finite
- For all $i \in t$, the function $f(i)$ is square integrable on $s$
- The function $g$ is square integrable on $s$

Then:
$$\langle g, \sum_{i \in t} f_i \rangle_s = \sum_{i \in t} \langle g, f_i \rangle_s$$

where $\langle f, g \rangle_s = \int_s f(x) \cdot g(x) \, dx$ denotes the $L^2$ inner product on $s$.

### Informal proof
The proof follows directly by:

1. First apply symmetry of the $L^2$ inner product (theorem `L2PRODUCT_SYM`):
   $$\langle g, \sum_{i \in t} f_i \rangle_s = \langle \sum_{i \in t} f_i, g \rangle_s$$

2. Then apply the theorem `L2PRODUCT_LSUM` which states that the $L^2$ inner product distributes over finite sums in the first argument:
   $$\langle \sum_{i \in t} f_i, g \rangle_s = \sum_{i \in t} \langle f_i, g \rangle_s$$

3. Apply symmetry again to each term in the sum:
   $$\sum_{i \in t} \langle f_i, g \rangle_s = \sum_{i \in t} \langle g, f_i \rangle_s$$

This completes the proof.

### Mathematical insight
This theorem demonstrates that the $L^2$ inner product distributes over finite sums in the second argument. Combined with the previously proven `L2PRODUCT_LSUM`, it establishes the bilinearity of the $L^2$ inner product, which is a fundamental property of inner products in functional analysis.

The proof technique is elegant and efficient, leveraging two key properties:
1. The symmetry of the inner product
2. The already-established distributivity over sums in the first argument

This result is particularly important for Fourier analysis, where one often needs to work with sums of square-integrable functions and compute their inner products.

### Dependencies
- **Definitions**:
  - `l2product`: Defines the $L^2$ inner product as `l2product s f g = real_integral s (λx. f(x) * g(x))`
  - `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable

- **Theorems**:
  - `L2PRODUCT_SYM`: States that the $L^2$ inner product is symmetric
  - `L2PRODUCT_LSUM`: States that the $L^2$ inner product distributes over finite sums in the first argument

### Porting notes
When porting this theorem:
- Ensure that the $L^2$ inner product is properly defined in the target system
- The proof is straightforward and should translate well to any system that has established the symmetry property and the distributivity over sums in the first argument
- Be aware of how the target system handles function spaces and measurability conditions, as these may require more explicit reasoning in some systems

---

## L2PRODUCT_LMUL

### L2PRODUCT_LMUL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2PRODUCT_LMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s (\x. c * f x) g = c * l2product s f g`,
  SIMP_TAC[l2product; GSYM REAL_MUL_ASSOC; REAL_INTEGRAL_LMUL;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```

### Informal statement
For all sets $s$, constants $c$, and functions $f$ and $g$, if $f$ is square integrable on $s$ and $g$ is square integrable on $s$, then the $L^2$ inner product of $c \cdot f$ with $g$ on $s$ equals $c$ times the $L^2$ inner product of $f$ with $g$ on $s$:

$$\forall s, c, f, g. \, (f \text{ square integrable on } s) \land (g \text{ square integrable on } s) \Rightarrow \langle c \cdot f, g \rangle_{L^2(s)} = c \cdot \langle f, g \rangle_{L^2(s)}$$

where $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) \, dx$.

### Informal proof
This theorem shows that the $L^2$ inner product is linear in its first argument.

The proof proceeds as follows:
- We use the definition of the $L^2$ inner product: $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) \, dx$
- For the left side, we have $\langle c \cdot f, g \rangle_{L^2(s)} = \int_s (c \cdot f(x)) \cdot g(x) \, dx = \int_s c \cdot (f(x) \cdot g(x)) \, dx$
- By the associativity of multiplication, $(c \cdot f(x)) \cdot g(x) = c \cdot (f(x) \cdot g(x))$
- By the property that constants can be pulled out of integrals, $\int_s c \cdot (f(x) \cdot g(x)) \, dx = c \cdot \int_s f(x) \cdot g(x) \, dx = c \cdot \langle f, g \rangle_{L^2(s)}$
- The integrability of the product $f(x) \cdot g(x)$ is guaranteed by the theorem `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`, which states that if both functions are square integrable, then their product is integrable.

### Mathematical insight
This theorem establishes the linearity property of the $L^2$ inner product with respect to its first argument, which is a fundamental property of inner products in general. This property is essential for the $L^2$ space to form a proper inner product space, which in turn enables the application of many results from functional analysis and Hilbert space theory.

The result is part of a broader collection of theorems establishing that $L^2$ functions with this inner product form a complete inner product space (a Hilbert space), which is crucial for applications in Fourier analysis, partial differential equations, and quantum mechanics.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`: If $f$ and $g$ are square integrable on $s$, then their product is integrable on $s$
  - `REAL_MUL_ASSOC`: Associativity of real multiplication
  - `REAL_INTEGRAL_LMUL`: A constant can be pulled out of a real integral

- **Definitions**:
  - `square_integrable_on`: A function $f$ is square integrable on $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$
  - `l2product`: The $L^2$ inner product of functions $f$ and $g$ on set $s$ is defined as the integral of their product: $\langle f, g \rangle_{L^2(s)} = \int_s f(x) \cdot g(x) \, dx$

### Porting notes
When porting this theorem:
1. Ensure that the target system has a proper formalization of Lebesgue integration
2. Verify that the square integrability concept is defined
3. Check that the $L^2$ inner product is properly defined
4. The proof is straightforward and should work in any system with basic properties of real integrals

---

## L2PRODUCT_RMUL

### L2PRODUCT_RMUL
- L2PRODUCT_RMUL

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2PRODUCT_RMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s f (\x. c * g x) = c * l2product s f g`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN SIMP_TAC[L2PRODUCT_LMUL]);;
```

### Informal statement
For all sets $s$, constants $c$, and functions $f$ and $g$, if $f$ and $g$ are square integrable on $s$, then:

$$\langle f, c \cdot g \rangle_s = c \cdot \langle f, g \rangle_s$$

where $\langle f, g \rangle_s$ denotes the L2 inner product of $f$ and $g$ over the set $s$, defined as $\int_s f(x) \cdot g(x) \, dx$.

### Informal proof
The proof uses symmetry of the L2 product and a previously established result about multiplication on the left side:

1. First, use the symmetry of the L2 product (`L2PRODUCT_SYM`) to rewrite:
   $$\langle f, c \cdot g \rangle_s = \langle c \cdot g, f \rangle_s$$

2. Then apply `L2PRODUCT_LMUL` which states that 
   $$\langle c \cdot g, f \rangle_s = c \cdot \langle g, f \rangle_s$$

3. Using symmetry again (implicitly), we get 
   $$c \cdot \langle g, f \rangle_s = c \cdot \langle f, g \rangle_s$$

Therefore, $\langle f, c \cdot g \rangle_s = c \cdot \langle f, g \rangle_s$.

### Mathematical insight
This theorem establishes that the L2 inner product is linear in its second argument. Combined with `L2PRODUCT_LMUL` (which shows linearity in the first argument) and `L2PRODUCT_SYM` (which shows symmetry), these properties confirm that the L2 product behaves as a proper inner product in terms of its algebraic properties.

This property is fundamental in functional analysis, particularly in the theory of Hilbert spaces, where the L2 inner product is used to define the standard inner product structure on the space of square-integrable functions. Linearity in both arguments is a key property of any inner product.

### Dependencies
- **Theorems:**
  - `L2PRODUCT_SYM`: The L2 product is symmetric: $\langle f, g \rangle_s = \langle g, f \rangle_s$
  - `L2PRODUCT_LMUL`: For multiplication in the first argument: $\langle c \cdot f, g \rangle_s = c \cdot \langle f, g \rangle_s$

- **Definitions:**
  - `l2product`: Defines the L2 inner product as $\langle f, g \rangle_s = \int_s f(x) \cdot g(x) \, dx$
  - `square_integrable_on`: A function is square integrable on a set if it is measurable and its square is integrable

### Porting notes
When porting this theorem, ensure that:
1. The L2 inner product is properly defined using the appropriate integral
2. The symmetry and left-multiplication properties have already been established
3. The concept of square-integrability is correctly defined in the target system

The proof is quite simple and should translate well to other proof assistants that have good support for rewriting with equalities.

---

## L2NORM_LMUL

### L2NORM_LMUL

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2NORM_LMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. c * f(x)) = abs(c) * l2norm s f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[l2norm; L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN
  REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]);;
```

### Informal statement
For any function $f$ that is square integrable on a set $s$ and any constant $c$, the $L^2$ norm of the scaled function $c \cdot f(x)$ on $s$ is equal to the absolute value of $c$ multiplied by the $L^2$ norm of $f$ on $s$:

$$\forall f, s, c.\ f \text{ square_integrable_on } s \implies \|c \cdot f\|_{L^2(s)} = |c| \cdot \|f\|_{L^2(s)}$$

### Informal proof
We prove that the $L^2$ norm of a scaled function equals the absolute value of the scaling factor times the original function's $L^2$ norm.

- Start with the definition of $L^2$ norm: $\|f\|_{L^2(s)} = \sqrt{\langle f, f \rangle_{L^2(s)}}$
- For the scaled function $c \cdot f$, we have:
  $\|c \cdot f\|_{L^2(s)} = \sqrt{\langle c \cdot f, c \cdot f \rangle_{L^2(s)}}$
- Apply `L2PRODUCT_LMUL` to get $\langle c \cdot f, c \cdot f \rangle_{L^2(s)} = c \cdot \langle f, c \cdot f \rangle_{L^2(s)}$
- Apply `L2PRODUCT_RMUL` to further simplify: $c \cdot \langle f, c \cdot f \rangle_{L^2(s)} = c \cdot c \cdot \langle f, f \rangle_{L^2(s)} = c^2 \cdot \langle f, f \rangle_{L^2(s)}$
- Therefore: $\|c \cdot f\|_{L^2(s)} = \sqrt{c^2 \cdot \langle f, f \rangle_{L^2(s)}} = \sqrt{c^2} \cdot \sqrt{\langle f, f \rangle_{L^2(s)}} = |c| \cdot \|f\|_{L^2(s)}$

The last step uses the properties of square roots, specifically that $\sqrt{c^2} = |c|$.

### Mathematical insight
This theorem establishes the homogeneity property of the $L^2$ norm, which is a fundamental property of norms. It shows how scaling a function affects its $L^2$ norm in a predictable way.

This property is important for several reasons:
- It's a crucial property for any norm in functional analysis
- It allows for normalization of functions
- It helps in understanding how the $L^2$ space behaves under scalar multiplication
- It's essential for working with the theory of Hilbert spaces

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_LMUL`: If $f$ is square integrable on $s$, then $c \cdot f$ is also square integrable on $s$
  - `L2PRODUCT_LMUL`: For square integrable functions, $\langle c \cdot f, g \rangle_{L^2(s)} = c \cdot \langle f, g \rangle_{L^2(s)}$
  - `L2PRODUCT_RMUL`: For square integrable functions, $\langle f, c \cdot g \rangle_{L^2(s)} = c \cdot \langle f, g \rangle_{L^2(s)}$

- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable
  - `l2norm`: The $L^2$ norm of a function on a set, defined as the square root of its $L^2$ inner product with itself

---

## L2NORM_RMUL

### Name of formal statement
L2NORM_RMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_RMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. f(x) * c) = l2norm s f * abs(c)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[L2NORM_LMUL]);;
```

### Informal statement
For any function $f$, set $s$, and constant $c$, if $f$ is square integrable on $s$, then:

$$\|f \cdot c\|_{L^2(s)} = \|f\|_{L^2(s)} \cdot |c|$$

where $\|f \cdot c\|_{L^2(s)}$ denotes the $L^2$ norm of the function $x \mapsto f(x) \cdot c$ on the set $s$, and $|c|$ is the absolute value of $c$.

### Informal proof
The proof is straightforward:
1. First, apply commutativity of multiplication to convert $f(x) \cdot c$ to $c \cdot f(x)$
2. Then apply the already-proven theorem `L2NORM_LMUL`, which states that $\|c \cdot f\|_{L^2(s)} = |c| \cdot \|f\|_{L^2(s)}$

The proof leverages the commutativity of real multiplication to reduce this theorem to a previously established result about left multiplication.

### Mathematical insight
This theorem shows that the $L^2$ norm scales linearly with scalar multiplication, which is a fundamental property of norms in general. Together with `L2NORM_LMUL`, it establishes that the position of the scalar (whether multiplying the function from the left or right) doesn't affect the result, as expected from the commutativity of real multiplication.

This property is part of demonstrating that the $L^2$ space forms a normed vector space, which is a key structure in functional analysis. The result confirms that scalar multiplication behaves correctly with respect to the $L^2$ norm.

### Dependencies
- **Theorems**:
  - `L2NORM_LMUL`: States that $\|c \cdot f\|_{L^2(s)} = |c| \cdot \|f\|_{L^2(s)}$
  - `REAL_MUL_SYM`: Commutativity of real multiplication
- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it is measurable and its square is integrable
  - `l2norm`: The $L^2$ norm of a function, defined as the square root of its inner product with itself

### Porting notes
When porting to other proof assistants, note that:
1. The theorem relies on commutativity of multiplication, which should be straightforward to establish in any system
2. The main work will be in porting the prerequisite theorem `L2NORM_LMUL` and the supporting definitions for $L^2$ spaces

---

## L2NORM_NEG

### Name of formal statement
L2NORM_NEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_NEG = prove
 (`!f s. f square_integrable_on s ==> l2norm s (\x. --(f x)) = l2norm s f`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x:real = --(&1) * x`] THEN
  SIMP_TAC[L2NORM_LMUL; REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID]);;
```

### Informal statement
For any function $f$ and set $s$, if $f$ is square integrable on $s$, then the $L^2$-norm of the negation of $f$ equals the $L^2$-norm of $f$ itself:

$$\forall f,s.\ f \text{ square_integrable_on } s \Rightarrow \|{-f}\|_{L^2(s)} = \|f\|_{L^2(s)}$$

where $\|-f\|_{L^2(s)}$ denotes the $L^2$-norm of the function $-f$ on the set $s$.

### Informal proof
We show that negating a function preserves its $L^2$-norm.

First, observe that $-f(x) = -1 \cdot f(x)$ for any function $f$.

By the theorem `L2NORM_LMUL`, we know that for any constant $c$ and square-integrable function $f$ on $s$:
$$\|c \cdot f\|_{L^2(s)} = |c| \cdot \|f\|_{L^2(s)}$$

Applying this with $c = -1$, we get:
$$\|-f\|_{L^2(s)} = |-1| \cdot \|f\|_{L^2(s)}$$

Since $|-1| = 1$ and $1 \cdot \|f\|_{L^2(s)} = \|f\|_{L^2(s)}$, we conclude:
$$\|-f\|_{L^2(s)} = \|f\|_{L^2(s)}$$

### Mathematical insight
This theorem establishes that the $L^2$-norm is invariant under negation of functions. This is a specific case of the more general property that the $L^2$-norm scales linearly with constant factors, but preserves its value when the constant has absolute value 1 (such as -1).

This property is important in analysis, particularly in the theory of Hilbert spaces of square-integrable functions. It illustrates the natural behavior of norms with respect to scalar multiplication, highlighting that the $L^2$-norm measures the "size" of a function independent of its sign.

### Dependencies
#### Theorems
- `L2NORM_LMUL`: For any square-integrable function $f$ on a set $s$ and constant $c$, the $L^2$-norm of $c \cdot f$ equals $|c|$ times the $L^2$-norm of $f$.

#### Definitions
- `square_integrable_on`: A function $f$ is square-integrable on a set $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$.
- `l2norm`: The $L^2$-norm of a function $f$ on a set $s$ is the square root of the $L^2$-inner product of $f$ with itself.

### Porting notes
This theorem should be straightforward to port to other proof assistants. The key requirement is having established definitions for square-integrable functions and $L^2$-norms, along with the more fundamental theorem `L2NORM_LMUL` about how the $L^2$-norm behaves under scalar multiplication.

---

## L2NORM_SUB

### Name of formal statement
L2NORM_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_SUB = prove
 (`!f g s.  f square_integrable_on s /\ g square_integrable_on s
        ==> l2norm s (\x. f x - g x) = l2norm s (\x. g x - f x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[L2NORM_NEG; SQUARE_INTEGRABLE_SUB; ETA_AX]);;
```

### Informal statement
For all functions $f$ and $g$ and a set $s$, if both $f$ and $g$ are square integrable on $s$, then the L2-norm of the difference $(f - g)$ equals the L2-norm of the difference $(g - f)$:

$$\forall f, g, s. \, (f \text{ square integrable on } s) \land (g \text{ square integrable on } s) \Rightarrow \|f - g\|_{L^2(s)} = \|g - f\|_{L^2(s)}$$

### Informal proof
The proof shows that the L2-norm remains unchanged when the difference between two square-integrable functions is negated.

1. Starting with $\|f - g\|_{L^2(s)}$, we rewrite $f - g$ as $-(g - f)$ using properties of real subtraction.

2. Apply the theorem `L2NORM_NEG` to the negated function, which states that the L2-norm of a negated function equals the L2-norm of the original function:
   $$\|\!-h\|_{L^2(s)} = \|h\|_{L^2(s)}$$

3. The function $(g - f)$ is square integrable because both $f$ and $g$ are square integrable, which is established by the theorem `SQUARE_INTEGRABLE_SUB`.

4. Finally, we have:
   $$\|f - g\|_{L^2(s)} = \|\!-(g - f)\|_{L^2(s)} = \|g - f\|_{L^2(s)}$$

### Mathematical insight
This theorem establishes the symmetry property of the L2 distance between two functions, showing that the distance from $f$ to $g$ equals the distance from $g$ to $f$. This is a fundamental metric space property, demonstrating that the L2-norm induces a proper distance function on the space of square-integrable functions. This symmetry property is one of the necessary conditions for a function to be a metric, and is essential in functional analysis and the theory of Hilbert spaces.

### Dependencies
**Theorems:**
- `SQUARE_INTEGRABLE_SUB`: Shows that the difference of two square-integrable functions is square integrable
- `L2NORM_NEG`: States that the L2-norm of a negated function equals the L2-norm of the original function

**Definitions:**
- `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable on that set
- `l2norm`: The L2-norm of a function defined as the square root of its inner product with itself

### Porting notes
When porting to other systems, ensure that:
1. The underlying measure theory and integration framework is compatible
2. The definition of L2-norm is consistent with the HOL Light definition
3. The system has appropriate support for functional equality and reasoning with function application

---

## L2_SUMMABLE

### Name of formal statement
L2_SUMMABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2_SUMMABLE = prove
 (`!f s t.
     (!i. i IN t ==> (f i) square_integrable_on s) /\
     real_summable t (\i. l2norm s (f i))
     ==> ?g. g square_integrable_on s /\
             ((\n. l2norm s (\x. sum (t INTER (0..n)) (\i. f i x) - g x))
              ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. (lift o f n o drop)`;
                 `&2`; `IMAGE lift s`; `t:num->bool`]
        LSPACE_SUMMABLE) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
   [UNDISCH_TAC `real_summable t (\i. l2norm s (f i))` THEN
    MATCH_MP_TAC EQ_IMP THEN
    REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `e:real` THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `N:num` THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[GSYM L2NORM_LNORM; IN_INTER; ETA_AX];
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[o_DEF; GSYM LIFT_SUB; REWRITE_RULE[o_DEF] (GSYM LIFT_SUM);
             FINITE_NUMSEG; FINITE_INTER] THEN
    SUBGOAL_THEN `!f. (\x. lift(f(drop x))) = (lift o f o drop)`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(GSYM L2NORM_LNORM) THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    ASM_SIMP_TAC[FINITE_INTER; IN_INTER; FINITE_NUMSEG]]);;
```

### Informal statement
For all functions $f: \mathbb{N} \to \mathbb{R} \to \mathbb{R}$, sets $s \subseteq \mathbb{R}$, and sets of indices $t \subseteq \mathbb{N}$, if:
1. For all $i \in t$, the function $f_i$ is square integrable on $s$ (i.e., $f_i$ is measurable and $\int_s |f_i(x)|^2 dx < \infty$)
2. The series $\sum_{i \in t} \|f_i\|_2$ converges (where $\|f_i\|_2 = \sqrt{\int_s |f_i(x)|^2 dx}$ is the L2-norm)

Then there exists a function $g: \mathbb{R} \to \mathbb{R}$ such that:
1. $g$ is square integrable on $s$
2. The L2-norm of the difference between the partial sums of $f_i$ and $g$ converges to zero, i.e.,
   $\lim_{n\to\infty} \|\sum_{i \in t \cap \{0,1,\ldots,n\}} f_i(x) - g(x)\|_2 = 0$

### Informal proof
This theorem establishes the convergence of L2-summable sequences to an L2 function.

The proof proceeds as follows:

* We apply the more general theorem `LSPACE_SUMMABLE` to the functions $\text{lift} \circ f_i \circ \text{drop}$, with $p = 2$ and the set $\text{IMAGE lift}~s$.

* The theorem `LSPACE_SUMMABLE` states that for functions in Lp spaces, if the series of their Lp norms converges, then there exists a limit function in the Lp space such that the partial sums converge to it in the Lp norm.

* To apply this theorem, we need to show that our functions are in the L2 space. This is done using `SQUARE_INTEGRABLE_LSPACE`, which establishes the equivalence between square integrability of a real function $f$ on $s$ and the property that $\text{lift} \circ f \circ \text{drop}$ belongs to the L2 space over $\text{IMAGE lift}~s$.

* We also need to show that the summability condition in our theorem matches the one required by `LSPACE_SUMMABLE`. This is done by showing that the L2 norm of $f_i$ equals the Lp norm (with p=2) of $\text{lift} \circ f_i \circ \text{drop}$, using the theorem `L2NORM_LNORM`.

* After applying `LSPACE_SUMMABLE`, we get a function $g: \mathbb{R}^1 \to \mathbb{R}^1$ in the appropriate Lp space.

* We then define $h = \text{drop} \circ g \circ \text{lift}$ and show that $h$ is the desired square-integrable function on $s$.

* Finally, we prove that the convergence of partial sums in the L2 norm holds, using `SQUARE_INTEGRABLE_SUB` and `SQUARE_INTEGRABLE_SUM` to establish that the difference between the partial sum and $h$ is square integrable.

### Mathematical insight
This theorem establishes that if a sequence of square-integrable functions has summable L2 norms, then their series converges in the L2 sense to a square-integrable function. This is a fundamental result in the theory of L2 spaces and is analogous to completeness properties in other function spaces.

The result shows that the space of square-integrable functions is complete with respect to the L2 norm, which is a critical property for many applications in analysis, particularly in Fourier theory and PDEs where expansions of functions in terms of orthogonal bases are common.

This theorem essentially states that the L2 space on a measurable set forms a Banach space, which allows for powerful analytical tools to be applied to problems involving square-integrable functions.

### Dependencies
- Theorems:
  - `LSPACE_SUMMABLE`: Establishes summability in general Lp spaces
  - `SQUARE_INTEGRABLE_LSPACE`: Relates square integrability to L2 space membership
  - `SQUARE_INTEGRABLE_SUB`: Shows that the difference of square integrable functions is square integrable
  - `SQUARE_INTEGRABLE_SUM`: Shows that finite sums of square integrable functions are square integrable
  - `L2NORM_LNORM`: Relates the L2 norm to the general Lp norm for p=2

- Definitions:
  - `square_integrable_on`: Defines when a function is square integrable on a set
  - `l2norm`: Defines the L2 norm of a function

### Porting notes
When porting this theorem:
1. Ensure that your target system has appropriate definitions for L2 spaces, square integrability, and convergence in norm.
2. Be mindful of the handling of partial functions and measure theory concepts.
3. The proof relies on the lifting/dropping between real numbers and 1D vectors - your target system might handle this differently or more directly.
4. The summability condition might be expressible more cleanly in systems with better support for series.

---

## L2_COMPLETE

### L2_COMPLETE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let L2_COMPLETE = prove
 (`!f s. (!i. f i square_integrable_on s) /\
         (!e. &0 < e ==> ?N. !m n. m >= N /\ n >= N
                                   ==> l2norm s (\x. f m x - f n x) < e)
         ==> ?g. g square_integrable_on s /\
                 ((\n. l2norm s (\x. f n x - g x)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. lift o f n o drop`; `&2`; `IMAGE lift s`]
        RIESZ_FISCHER) THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[]] THEN
  (SUBGOAL_THEN `!f g. (\x. (lift o f o drop) x - (lift o g o drop) x) =
                       (lift o (\y. f y - g y) o drop)`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB];
     ASM_SIMP_TAC[GSYM L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX]]) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs(x - &0) = x`; GE;
               L2NORM_POS_LE; SQUARE_INTEGRABLE_SUB; ETA_AX]);;
```

### Informal statement
For any sequence of square-integrable functions $f_i: \mathbb{R} \to \mathbb{R}$ on a set $s$, if for any $\epsilon > 0$ there exists $N$ such that for all $m, n \geq N$, the $L^2$ norm of their difference $\|f_m - f_n\|_{L^2(s)} < \epsilon$ (i.e., the sequence is Cauchy in the $L^2$ norm), then there exists a square-integrable function $g$ on $s$ such that the sequence of $L^2$ norms $\|f_n - g\|_{L^2(s)}$ converges to $0$ as $n \to \infty$.

In mathematical notation:
$$\forall f, s. \left(\forall i. f_i \text{ is square-integrable on } s \right) \land \left(\forall \epsilon > 0. \exists N. \forall m, n \geq N. \|f_m - f_n\|_{L^2(s)} < \epsilon \right) \Rightarrow$$
$$\exists g. \left(g \text{ is square-integrable on } s\right) \land \left(\lim_{n \to \infty} \|f_n - g\|_{L^2(s)} = 0\right)$$

### Informal proof
The proof uses the Riesz-Fischer theorem, which is a completeness result for $L^p$ spaces.

* First, we transform our problem to use the Riesz-Fischer theorem by lifting our real-valued functions to functions in $\mathbb{R}^1$ using the embedding $\text{lift} : \mathbb{R} \to \mathbb{R}^1$.

* We apply the Riesz-Fischer theorem to the sequence of lifted functions $\text{lift} \circ f_n \circ \text{drop}$, where $\text{drop} : \mathbb{R}^1 \to \mathbb{R}$ is the inverse operation to $\text{lift}$.

* The Riesz-Fischer theorem gives us that there exists a function $g : \mathbb{R}^1 \to \mathbb{R}^1$ in $L^2(\text{IMAGE lift }s)$ such that $\text{lift} \circ f_n \circ \text{drop}$ converges to $g$ in the $L^2$ norm.

* We substitute $g = \text{lift} \circ (h \circ \text{drop})$ where $h = \text{drop} \circ g \circ \text{lift}$, and show that $h$ is the desired limit function in the original space.

* We verify that $h$ is square-integrable on $s$ and that the $L^2$ norm of $f_n - h$ converges to zero.

* Finally, using the equivalence between the $L^2$ norm of real-valued functions and the $L^2$ norm of their lifted versions, we conclude that $\|f_n - h\|_{L^2(s)} \to 0$ as required.

### Mathematical insight
This theorem establishes the completeness of the $L^2$ space of square-integrable functions. This is a fundamental property of $L^2$ spaces, stating that every Cauchy sequence in $L^2$ converges to an element in $L^2$. This completeness property is essential in functional analysis and the theory of Hilbert spaces.

The theorem is effectively a special case of the Riesz-Fischer theorem for $L^2(\mathbb{R})$ but presented in terms of the specific HOL Light setup for real-valued functions rather than the more general vector-valued functions. This completeness property allows for many important constructions, such as Fourier series and orthogonal expansions, and is foundational in the study of partial differential equations.

### Dependencies
#### Theorems
- `RIESZ_FISCHER`: Completeness of $L^p$ spaces, stating that any Cauchy sequence in $L^p$ converges to a function in $L^p$.
- `SQUARE_INTEGRABLE_LSPACE`: Equivalence between square-integrable functions and functions in $L^2$ space.
- `SQUARE_INTEGRABLE_SUB`: The difference of square-integrable functions is square-integrable.
- `L2NORM_LNORM`: Relationship between $L^2$ norm of a real function and the $L^p$ norm of its lifted version.
- `L2NORM_POS_LE`: Non-negativity of $L^2$ norm.

#### Definitions
- `square_integrable_on`: Definition of a square-integrable function.
- `l2norm`: Definition of the $L^2$ norm.

### Porting notes
When porting this theorem:
1. Ensure that your system has a properly defined notion of $L^2$ space and square integrability.
2. The proof relies heavily on lifting real-valued functions to $\mathbb{R}^1$ and back. This might be unnecessary in systems with more direct handling of real-valued function spaces.
3. The use of the Riesz-Fischer theorem is central, so this should be available or proved first.
4. Be careful with the handling of function composition and the lift/drop operations, which might be implicit in other systems.

---

## SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Name of formal statement
SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f square_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g square_integrable_on s /\
                   l2norm s (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&2:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; REAL_OF_NUM_LE; ARITH;
                  GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SQUARE_INTEGRABLE_LSPACE; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    ASM_SIMP_TAC[L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB]]);;
```

### Informal statement
For any real-valued function $f$, measurable set $s$, and positive real number $e > 0$, if $s$ is measurable and $f$ is square integrable on $s$, then there exists a continuous function $g$ defined on $\mathbb{R}$ such that:
1. $g$ is square integrable on $s$, and
2. The $L^2$ norm of the difference $\|f - g\|_{L^2(s)} < e$

In other words, square integrable functions can be approximated arbitrarily well (in the $L^2$ norm) by continuous functions.

### Informal proof
The proof uses the fact that square integrable functions correspond to functions in the $L^2$ space.

1. We begin by applying `LSPACE_APPROXIMATE_CONTINUOUS` to the function $\text{lift} \circ f \circ \text{drop}$ over the set $\text{IMAGE lift}\ s$ with $p = 2$ and our given $\epsilon$.
   - `LSPACE_APPROXIMATE_CONTINUOUS` states that functions in $L^p$ spaces can be approximated by continuous functions.
   - We use `SQUARE_INTEGRABLE_LSPACE` which establishes the correspondence between square integrable functions and $L^2$ space.

2. This gives us a continuous function $g: \mathbb{R}^1 \to \mathbb{R}^1$ such that:
   - $g$ is continuous on $\mathbb{R}^1$
   - $g \in L^2(\text{IMAGE lift}\ s)$
   - $\|(\text{lift} \circ f \circ \text{drop}) - g\|_{L^2} < \epsilon$

3. We then define our desired continuous function as $\text{drop} \circ g \circ \text{lift}$, and prove:
   - It is continuous on $\mathbb{R}$ (using `REAL_CONTINUOUS_ON`)
   - It is square integrable on $s$ (using `SQUARE_INTEGRABLE_LSPACE`)
   - The $L^2$ norm of the difference is less than $\epsilon$
   
4. For the last part, we use `L2NORM_LNORM` to relate the $L^2$ norm to the $L^p$ norm, and `SQUARE_INTEGRABLE_SUB` to establish that the difference of square integrable functions is square integrable.

5. Finally, we show that the $L^2$ norm of the difference simplifies to the $L^p$ norm we already established is less than $\epsilon$.

### Mathematical insight
This theorem establishes the density of continuous functions in the space of square integrable functions. It is a special case of a more general result that continuous functions are dense in $L^p$ spaces for $1 \leq p < \infty$.

This is a crucial approximation result in analysis and has many applications:
- It allows us to approximate potentially irregular functions with well-behaved continuous functions
- It provides a theoretical foundation for numerical methods that use continuous approximations
- In the theory of Fourier analysis and PDEs, it helps establish the existence of solutions through approximation schemes

The result is especially important because square integrable functions ($L^2$) form a Hilbert space, which enables many powerful analysis techniques.

### Dependencies
- **Theorems**:
  - `LSPACE_APPROXIMATE_CONTINUOUS`: Functions in $L^p$ spaces can be approximated by continuous functions
  - `SQUARE_INTEGRABLE_LSPACE`: Equivalence between square integrable functions and functions in $L^2$ space
  - `SQUARE_INTEGRABLE_SUB`: The difference of square integrable functions is square integrable
  - `L2NORM_LNORM`: Relationship between $L^2$ norm and $L^p$ norm for $p = 2$
  
- **Definitions**:
  - `square_integrable_on`: A function is square integrable if it's measurable and its square is integrable
  - `l2norm`: The $L^2$ norm of a function, defined as the square root of its $L^2$ inner product with itself

### Porting notes
When porting to other systems:
1. Pay attention to the translation between real-valued functions and vector-valued functions (the use of `lift` and `drop` operations in HOL Light).
2. Different systems may have different ways of representing measurability and integrability.
3. The notion of square integrability might be defined differently in other systems, but conceptually should be the same.
4. The proof relies on the more general approximation result for $L^p$ spaces, which should be available in most mathematical libraries.

---

## SCHWARZ_BOUND

### Name of formal statement
SCHWARZ_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARZ_BOUND = prove
 (`!f s. real_measurable s /\ f square_integrable_on s
         ==> f absolutely_real_integrable_on s /\
             (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[SQUARE_INTEGRABLE_LSPACE; REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOELDER_BOUND)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_ON; RPOW_POW] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [square_integrable_on]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[REAL_POW_1; o_DEF; NORM_1; LIFT_DROP; REAL_POW2_ABS] THEN
  REWRITE_TAC[GSYM REAL_MEASURE_MEASURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_MEASURE_POS_LE] THEN
  REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  REWRITE_TAC[o_DEF]);;
```

### Informal statement
For any real-valued function $f$ and measurable set $s$, if $s$ is measurable and $f$ is square integrable on $s$, then:
1. $f$ is absolutely integrable on $s$
2. The square of the integral of $f$ over $s$ is bounded by the product of the measure of $s$ and the integral of $f^2$ over $s$:
   
   $\left(\int_s f(x) \, dx\right)^2 \leq \mu(s) \cdot \int_s f(x)^2 \, dx$

where $\mu(s)$ represents the measure of set $s$.

### Informal proof
This theorem is an application of the Cauchy-Schwarz inequality (derived from Hölder's inequality). The proof proceeds as follows:

* We start with a measurable set $s$ and a square integrable function $f$.

* By definition, square integrable means that $f$ is measurable and $f^2$ is integrable on $s$.

* We use `SQUARE_INTEGRABLE_LSPACE` to reframe the condition in terms of $f$ belonging to the $L^2$ space over $s$.

* Apply Hölder's inequality (specifically `HOELDER_BOUND` with $p=2$) to establish that:
  - $f$ is absolutely integrable on $s$
  - The $L^2$ norm of the integral is bounded appropriately

* Since $p=2$, the exponent $p-1=1$ in Hölder's inequality, which simplifies the expression.

* We convert from the general vector space formulation back to real-valued functions.

* The final inequality follows directly:
  $\left(\int_s f(x) \, dx\right)^2 \leq \mu(s) \cdot \int_s f(x)^2 \, dx$

### Mathematical insight
This result is the Cauchy-Schwarz inequality for integrals, a special case of Hölder's inequality when $p=2$. It provides a fundamental bound relating the square of an integral to the integral of the square.

The inequality has numerous applications in analysis and probability theory:
- In probability, it relates the square of the expected value to the second moment: $[E(X)]^2 \leq E(X^2)$
- It's essential for proving convergence in $L^2$ spaces
- It's used in proving many other inequalities in analysis

This result is particularly important because it shows that square integrability is a stronger condition than absolute integrability, and provides a precise bound on the integral in terms of the $L^2$ norm.

### Dependencies
- Theorems:
  - `HOELDER_BOUND`: The general Hölder inequality for function spaces
  - `SQUARE_INTEGRABLE_LSPACE`: Relates square integrability to the $L^2$ space concept

- Definitions:
  - `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$

### Porting notes
When porting this theorem:
1. Ensure the target system has appropriate definitions for measurability and integrability
2. The proof depends critically on Hölder's inequality, so that should be ported first
3. Be aware of differences in how $L^p$ spaces might be formalized in other systems
4. The conversion between vector-valued integrals and real-valued integrals should be handled carefully, as this is where notation often diverges between systems

---

## orthonormal_system

### orthonormal_system
- orthonormal_system

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let orthonormal_system = new_definition
 `orthonormal_system s w <=>
        !m n. l2product s (w m) (w n) = if m = n then &1 else &0`;;
```

### Informal statement
An orthonormal system on a set $s$ is a family of functions $w$ indexed by natural numbers such that:

$$\text{orthonormal\_system}(s, w) \Leftrightarrow \forall m,n. \int_s w(m)(x) \cdot w(n)(x) \, dx = \begin{cases} 1 & \text{if } m = n \\ 0 & \text{if } m \neq n \end{cases}$$

This states that the $L^2$ inner product of any two functions in the system equals 1 if they are the same function, and 0 if they are different functions.

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
Orthonormal systems are fundamental in Fourier analysis and functional analysis. They provide a generalization of orthonormal bases to function spaces. A key property is that functions from an orthonormal system are linearly independent and can be used to represent other functions through series expansions.

The orthonormality condition ensures that:
1. Each function has unit $L^2$ norm (normalized)
2. Different functions are orthogonal to each other

This definition is particularly important for constructing Fourier series, wavelets, and other function expansions where we decompose functions into simpler orthogonal components. The orthogonality property simplifies many calculations, as it allows coefficients in expansions to be calculated through simple inner products.

### Dependencies
- Definitions:
  - `l2product`: The $L^2$ inner product defined as `l2product s f g = real_integral s (λx. f(x) * g(x))`, representing the integral of the product of two functions over a set.

### Porting notes
When porting this definition:
- Ensure the target system has a suitable notion of real integration
- The indexing of the orthonormal system is by natural numbers, which may need to be adjusted depending on the type system of the target proof assistant
- The definition uses an if-then-else construct which should be translated appropriately in systems that prefer match statements or other conditional constructs

---

## orthonormal_coefficient

### orthonormal_coefficient
- orthonormal_coefficient

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let orthonormal_coefficient = new_definition
 `orthonormal_coefficient s w f (n:num) = l2product s (w n) f`;;
```

### Informal statement
The definition states that the $n$-th orthonormal coefficient of a function $f$ with respect to an orthonormal system $w$ over a set $s$ is given by:

$$\text{orthonormal\_coefficient}(s, w, f, n) = \text{l2product}(s, w(n), f)$$

where $\text{l2product}(s, w(n), f)$ represents the $L^2$ inner product of the functions $w(n)$ and $f$ over the set $s$, defined as:

$$\text{l2product}(s, w(n), f) = \int_s w(n)(x) \cdot f(x) \, dx$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the fundamental concept of computing the Fourier coefficients of a function with respect to an orthonormal basis. In functional analysis and Fourier analysis, when we have an orthonormal system $\{w_n\}$ of functions over a set $s$, the orthonormal coefficients of a function $f$ are obtained by taking the inner product of $f$ with each basis function.

These coefficients are essential for representing functions as linear combinations of orthonormal basis functions. For example, if $\{w_n\}$ is a complete orthonormal system (like the trigonometric basis for periodic functions), then any square-integrable function $f$ can be represented as:

$$f = \sum_{n} \langle w_n, f \rangle w_n = \sum_{n} \text{orthonormal\_coefficient}(s, w, f, n) \cdot w_n$$

This result is a cornerstone in Fourier analysis and the theory of function spaces, enabling the decomposition of complex functions into simpler components.

### Dependencies
- Definitions:
  - `l2product`: The $L^2$ inner product of two functions over a set, defined as the integral of their product.

### Porting notes
When porting this definition:
- Ensure the target system has a suitable notion of real integration.
- Check that function application is handled similarly, especially the application of $w$ to the natural number $n$.
- Consider how the target system represents function spaces and inner products, as these might have established libraries or notations.

---

## ORTHONORMAL_SYSTEM_L2NORM

### ORTHONORMAL_SYSTEM_L2NORM

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ORTHONORMAL_SYSTEM_L2NORM = prove
 (`!s w. orthonormal_system s w ==> !i. l2norm s (w i) = &1`,
  SIMP_TAC[orthonormal_system; l2norm; SQRT_1]);;
```

### Informal statement
For any set $s$ and function family $w$, if $w$ forms an orthonormal system on $s$, then the L2-norm of each function $w(i)$ on $s$ equals $1$.

Formally, $\forall s, w. \text{orthonormal\_system}(s, w) \implies \forall i. \text{l2norm}(s, w(i)) = 1$.

### Informal proof
The proof follows directly from the definition of an orthonormal system and the L2-norm.

By definition, an orthonormal system $w$ on $s$ satisfies the property that for all indices $m$ and $n$, the L2 inner product $\text{l2product}(s, w(m), w(n)) = 1$ if $m = n$, and $0$ otherwise.

The L2-norm of a function $f$ is defined as $\text{l2norm}(s, f) = \sqrt{\text{l2product}(s, f, f)}$.

For any index $i$, we have:
$\text{l2norm}(s, w(i)) = \sqrt{\text{l2product}(s, w(i), w(i))}$

Since $w$ is an orthonormal system, $\text{l2product}(s, w(i), w(i)) = 1$ (as $i = i$).

Therefore, $\text{l2norm}(s, w(i)) = \sqrt{1} = 1$.

### Mathematical insight
This theorem confirms a basic property of orthonormal systems: each function in the system has unit L2-norm. This is part of what makes orthonormal systems so useful in analysis, particularly in Fourier analysis and other expansions of functions into orthogonal series. The orthonormality condition ensures that the functions in the system are both orthogonal to each other and individually normalized, making them ideal as a basis for function spaces.

In functional analysis, orthonormal systems provide a generalization of orthonormal bases from finite-dimensional vector spaces to infinite-dimensional function spaces, particularly Hilbert spaces.

### Dependencies
- **Definitions**:
  - `l2norm`: Defines the L2-norm of a function $f$ on a set $s$ as $\sqrt{\text{l2product}(s, f, f)}$
  - `orthonormal_system`: Defines a system of functions $w$ to be orthonormal on a set $s$ if the L2 inner product of any two functions equals 1 when they are the same function, and 0 otherwise

- **Theorems**:
  - `SQRT_1`: States that $\sqrt{1} = 1$

### Porting notes
This theorem should be straightforward to port to other systems that have the necessary infrastructure for L2 norms and inner products. The proof is a direct simplification using definitions and basic properties of the square root function.

---

## ORTHONORMAL_PARTIAL_SUM_DIFF

### Name of formal statement
ORTHONORMAL_PARTIAL_SUM_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_PARTIAL_SUM_DIFF = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> l2norm s (\x. f(x) - sum t (\i. a i * w i x)) pow 2 =
            (l2norm s f) pow 2 + sum t (\i. (a i) pow 2) -
            &2 * sum t (\i. a i * orthonormal_coefficient s w f i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. sum t (\i:num. a i * w i x)) square_integrable_on s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
                 SQUARE_INTEGRABLE_LMUL];
   ALL_TAC] THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_LSUB] THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_RSUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x' = x /\ b - &2 * x = c ==> a - x - (x' - b) = a + c`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[L2PRODUCT_SYM]; ALL_TAC] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[orthonormal_coefficient; REAL_MUL_RID; GSYM REAL_POW_2] THEN
  REWRITE_TAC[L2PRODUCT_SYM]);;
```

### Informal statement
Let $s$ be a set, $w$ be an orthonormal system on $s$, $a$ be a function mapping indices to real numbers, $f$ be a square-integrable function on $s$, and $t$ be a finite set of indices. Then:

$$\left\|f(x) - \sum_{i \in t} a_i w_i(x)\right\|^2_2 = \|f\|^2_2 + \sum_{i \in t} a_i^2 - 2 \sum_{i \in t} a_i \langle w_i, f \rangle$$

where $\|\cdot\|_2$ denotes the $L^2$ norm, and $\langle w_i, f \rangle$ represents the inner product of $w_i$ and $f$, which is the orthonormal coefficient.

### Informal proof
We need to prove that for an orthonormal system $w$ and a square-integrable function $f$ on $s$, the $L^2$ norm squared of the difference between $f$ and its partial sum approximation gives the expression on the right-hand side.

First, we establish that the sum $\sum_{i \in t} a_i w_i(x)$ is square-integrable on $s$ since each $w_i$ is square-integrable and $t$ is finite.

Using the property that $\|g\|^2_2 = \langle g, g \rangle$ for any square-integrable function $g$, we have:
$$\left\|f(x) - \sum_{i \in t} a_i w_i(x)\right\|^2_2 = \left\langle f(x) - \sum_{i \in t} a_i w_i(x), f(x) - \sum_{i \in t} a_i w_i(x) \right\rangle$$

Expanding this inner product using linearity:
$$\left\langle f, f \right\rangle - \left\langle f, \sum_{i \in t} a_i w_i \right\rangle - \left\langle \sum_{i \in t} a_i w_i, f \right\rangle + \left\langle \sum_{i \in t} a_i w_i, \sum_{i \in t} a_i w_i \right\rangle$$

By symmetry of inner product, $\left\langle \sum_{i \in t} a_i w_i, f \right\rangle = \left\langle f, \sum_{i \in t} a_i w_i \right\rangle$.

Using linearity of inner product:
$$\left\langle f, \sum_{i \in t} a_i w_i \right\rangle = \sum_{i \in t} a_i \langle f, w_i \rangle = \sum_{i \in t} a_i \langle w_i, f \rangle$$

The last term expands as:
$$\left\langle \sum_{i \in t} a_i w_i, \sum_{i \in t} a_i w_i \right\rangle = \sum_{i \in t} \sum_{j \in t} a_i a_j \langle w_i, w_j \rangle$$

Since $w$ is an orthonormal system, $\langle w_i, w_j \rangle = 1$ if $i = j$ and $0$ otherwise. Thus, the double sum simplifies to:
$$\sum_{i \in t} a_i^2$$

Combining all these terms:
$$\|f\|^2_2 - 2\sum_{i \in t} a_i \langle w_i, f \rangle + \sum_{i \in t} a_i^2 = \|f\|^2_2 + \sum_{i \in t} a_i^2 - 2\sum_{i \in t} a_i \langle w_i, f \rangle$$

which is the desired result.

### Mathematical insight
This theorem quantifies the error when approximating a square-integrable function by a finite linear combination of orthonormal functions. It can be viewed as a generalization of the Pythagoras theorem to function spaces, showing how the squared $L^2$ norm of the difference decomposes.

The result is particularly useful in Fourier analysis and approximation theory, where it helps:
1. Quantify the error when using a partial sum of an orthonormal expansion
2. Prove minimization properties of orthogonal projections
3. Analyze convergence rates of orthogonal series

The formula demonstrates that the best approximation (minimizing the $L^2$ distance) is achieved when the coefficients $a_i$ are set to the orthonormal coefficients $\langle w_i, f \rangle$, as this choice minimizes the right-hand side.

### Dependencies
- Definitions:
  - `square_integrable_on`: A function is square-integrable on a set if it's measurable and its square is integrable
  - `l2norm`: The $L^2$ norm of a function, defined as the square root of the inner product with itself
  - `orthonormal_system`: A system of functions where the inner product of any two functions is 1 if they're the same and 0 otherwise
  - `orthonormal_coefficient`: The inner product of a function with a member of an orthonormal system

- Theorems:
  - `SQUARE_INTEGRABLE_LMUL`: Scalar multiplication preserves square integrability
  - `SQUARE_INTEGRABLE_SUB`: Subtraction preserves square integrability 
  - `SQUARE_INTEGRABLE_SUM`: Finite sum of square-integrable functions is square-integrable
  - `L2PRODUCT_SYM`: Symmetry of the $L^2$ inner product
  - `L2NORM_POW_2`: Relates the squared $L^2$ norm to the inner product
  - `L2PRODUCT_LSUB`, `L2PRODUCT_RSUB`: Linearity of the $L^2$ inner product with respect to subtraction
  - `L2PRODUCT_LSUM`, `L2PRODUCT_RSUM`: Linearity of the $L^2$ inner product with respect to summation
  - `L2PRODUCT_LMUL`, `L2PRODUCT_RMUL`: Linearity of the $L^2$ inner product with respect to scalar multiplication

### Porting notes
When porting this theorem to other proof assistants, pay attention to:
1. The representation of orthonormal systems and inner products
2. The handling of measurability and integrability conditions
3. The approach to defining $L^2$ norms and inner products
4. The set-theoretical treatment of finite summations

In systems with a well-developed theory of Hilbert spaces or $L^2$ spaces (like Coq's Mathematical Components or Isabelle's HOL-Analysis), this result might be expressible in a more abstract form using general inner product spaces.

---

## ORTHONORMAL_OPTIMAL_PARTIAL_SUM

### Name of formal statement
ORTHONORMAL_OPTIMAL_PARTIAL_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_OPTIMAL_PARTIAL_SUM = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==>  l2norm s (\x. f(x) -
                           sum t (\i. orthonormal_coefficient s w f i * w i x))
             <= l2norm s (\x. f(x) - sum t (\i. a i * w i x))`,
  REPEAT STRIP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2NORM_LE; SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
    GSYM L2NORM_POW_2; SQUARE_INTEGRABLE_LMUL; SQUARE_INTEGRABLE_SUB] THEN
  ASM_SIMP_TAC[ORTHONORMAL_PARTIAL_SUM_DIFF] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH
   `b pow 2 - &2 * b * b <= a pow 2 - &2 * a * b <=> &0 <= (a - b) pow 2`] THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```

### Informal statement
For a set $s$, an orthonormal system $w$, coefficients $a$, and a square-integrable function $f$ on $s$, if $t$ is a finite set and all $w_i$ are square-integrable on $s$, then:

$$\|f - \sum_{i \in t} \langle w_i, f \rangle \cdot w_i\|_{L^2(s)} \leq \|f - \sum_{i \in t} a_i \cdot w_i\|_{L^2(s)}$$

Where $\langle w_i, f \rangle = \text{orthonormal\_coefficient}\ s\ w\ f\ i$ represents the inner product of $w_i$ and $f$ in the $L^2$ space.

### Informal proof
This theorem establishes that using the orthonormal coefficients $\langle w_i, f \rangle$ provides the optimal partial sum approximation of $f$ in the $L^2$ norm.

The proof proceeds as follows:

- We apply the `L2NORM_LE` theorem to convert the inequality of $L^2$ norms to an inequality of squared $L^2$ norms (inner products).

- Then we use `ORTHONORMAL_PARTIAL_SUM_DIFF` which gives us an explicit formula for the squared $L^2$ norm of the difference between $f$ and a partial sum:
  $$\|f - \sum_{i \in t} a_i \cdot w_i\|_{L^2(s)}^2 = \|f\|_{L^2(s)}^2 + \sum_{i \in t} a_i^2 - 2 \sum_{i \in t} a_i \cdot \langle w_i, f \rangle$$

- After some algebraic manipulations, we need to show that:
  $$\sum_{i \in t} (c_i^2 - 2c_i c_i) \leq \sum_{i \in t} (a_i^2 - 2a_i c_i)$$
  where $c_i = \langle w_i, f \rangle$ is the orthonormal coefficient.

- This simplifies to showing:
  $$\sum_{i \in t} (a_i - c_i)^2 \geq 0$$
  which is true because squares of real numbers are always non-negative.

### Mathematical insight
This theorem is a fundamental result in approximation theory and Fourier analysis. It shows that when approximating a function $f$ using a finite linear combination of orthonormal functions, the optimal coefficients (that minimize the $L^2$ error) are precisely the inner products $\langle w_i, f \rangle$ of $f$ with each basis function.

This result is the mathematical foundation for many important applications:
- It explains why Fourier coefficients give the best approximation in Fourier series
- It's the basis of the least squares method in statistics
- It justifies the use of projection methods in numerical analysis and signal processing

The theorem demonstrates the power of orthogonality in function approximation: the best approximation using an orthonormal system is obtained by simply projecting the function onto each basis element.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_LMUL`: Shows that scaling preserves square-integrability
  - `SQUARE_INTEGRABLE_SUB`: Shows that subtraction preserves square-integrability
  - `SQUARE_INTEGRABLE_SUM`: Shows that finite sums of square-integrable functions remain square-integrable
  - `L2NORM_POW_2`: Relates the squared L2-norm to the inner product
  - `L2NORM_LE`: Provides an equivalent condition for L2-norm inequality
  - `ORTHONORMAL_PARTIAL_SUM_DIFF`: Gives the formula for the squared L2-norm of the difference between a function and its partial sum approximation

- **Definitions**:
  - `square_integrable_on`: Defines when a function is square-integrable on a set
  - `l2norm`: Defines the L2 norm of a function
  - `orthonormal_system`: Defines an orthonormal system of functions
  - `orthonormal_coefficient`: Defines the coefficient using the L2 inner product

### Porting notes
When porting this theorem:
1. Ensure your system has a well-developed theory of measure and integration
2. Carefully define the L2 inner product and norm structures
3. The key insight is that this theorem is primarily algebraic once the appropriate orthonormal system properties are established
4. The proof relies heavily on algebraic manipulations of sums and squares, which should be straightforward in most proof assistants

---

## BESSEL_INEQUALITY

### Name of formal statement
BESSEL_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BESSEL_INEQUALITY = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> sum t (\i. (orthonormal_coefficient s w f i) pow 2)
             <= l2norm s f pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= p ==> p = x - y ==> y <= x`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```

### Informal statement
For any set $s$, a family of functions $w$ indexed by natural numbers, a function $f$, and a finite set $t$ of indices:

If:
- $w$ forms an orthonormal system on $s$ (i.e., $\langle w_m, w_n \rangle_s = \delta_{mn}$)
- For all indices $i$, the function $w_i$ is square-integrable on $s$
- The function $f$ is square-integrable on $s$
- The set $t$ is finite

Then:
$$\sum_{i \in t} (\langle w_i, f \rangle_s)^2 \leq \|f\|_s^2$$

where $\langle w_i, f \rangle_s$ is the inner product (orthonormal coefficient) and $\|f\|_s$ is the L2-norm of $f$ on $s$.

### Informal proof
The proof uses the result about the norm of differences between a function and its partial sum approximation (theorem `ORTHONORMAL_PARTIAL_SUM_DIFF`).

1. We start with the identity from `ORTHONORMAL_PARTIAL_SUM_DIFF` where we set the coefficients $a_i$ to be equal to the orthonormal coefficients $\langle w_i, f \rangle_s$:
   
   $$\left\|f - \sum_{i \in t} \langle w_i, f \rangle_s \cdot w_i\right\|_s^2 = \|f\|_s^2 + \sum_{i \in t} (\langle w_i, f \rangle_s)^2 - 2 \sum_{i \in t} \langle w_i, f \rangle_s \cdot \langle w_i, f \rangle_s$$

2. Simplifying the right side using the fact that $2 \sum_{i \in t} (\langle w_i, f \rangle_s)^2 = 2 \sum_{i \in t} \langle w_i, f \rangle_s \cdot \langle w_i, f \rangle_s$:
   
   $$\left\|f - \sum_{i \in t} \langle w_i, f \rangle_s \cdot w_i\right\|_s^2 = \|f\|_s^2 - \sum_{i \in t} (\langle w_i, f \rangle_s)^2$$

3. Since the norm squared of any function is always non-negative, we have:
   
   $$\|f\|_s^2 - \sum_{i \in t} (\langle w_i, f \rangle_s)^2 \geq 0$$

4. Rearranging, we get the Bessel inequality:
   
   $$\sum_{i \in t} (\langle w_i, f \rangle_s)^2 \leq \|f\|_s^2$$

### Mathematical insight
Bessel's inequality is a fundamental result in Fourier analysis and the theory of orthogonal expansions. It states that the sum of squares of Fourier coefficients (orthonormal coefficients) is bounded by the squared L2-norm of the function itself.

This inequality reflects an important property of orthogonal projections: when approximating a function using an orthonormal basis, the sum of the squared coefficients represents the "energy" captured by the approximation, which cannot exceed the total "energy" of the original function.

The equality case (Parseval's identity) occurs when the set of functions forms a complete orthonormal system and the sum extends over the entire basis. The difference between the two sides of the inequality represents the energy in the part of the function that cannot be approximated using only the functions indexed by the finite set $t$.

### Dependencies
- **Theorems:**
  - `ORTHONORMAL_PARTIAL_SUM_DIFF`: Provides the relationship between the L2-norm of the difference between a function and its partial sum approximation, and the function's norm and coefficients.
  - `REAL_LE_POW_2`: Non-negativity of squares of real numbers.
  - `REAL_ARITH`: Used for algebraic manipulations of real expressions.

- **Definitions:**
  - `orthonormal_system`: A system where the inner product of basis functions equals 1 if indices are equal and 0 otherwise.
  - `orthonormal_coefficient`: The inner product of a basis function with another function.
  - `square_integrable_on`: Functions whose square is integrable on the given set.
  - `l2norm`: The square root of the inner product of a function with itself.

### Porting notes
When porting to other proof assistants:
1. Ensure the L2 inner product space is properly defined with appropriate measurability conditions.
2. The theorem relies on orthonormal properties which should be carefully formalized.
3. In systems with stronger typing, you may need to explicitly specify the types of functions and their domains.
4. Different proof assistants handle summations over finite sets differently, so check how this is represented.

---

## FOURIER_SERIES_SQUARE_SUMMABLE

### FOURIER_SERIES_SQUARE_SUMMABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SERIES_SQUARE_SUMMABLE = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s
        ==> real_summable t (\i. (orthonormal_coefficient s w f i) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
  MP_TAC(ISPECL
   [`\n. sum(t INTER (0..n)) (\i. (orthonormal_coefficient s w f i) pow 2)`;
    `l2norm s f pow 2`] CONVERGENT_BOUNDED_MONOTONE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`s:real->bool`; `w:num->real->real`;
                `f:real->real`; `t INTER (0..n)`] BESSEL_INEQUALITY) THEN
    ASM_SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs(x) <= y`) THEN
    SIMP_TAC[SUM_POS_LE; FINITE_INTER; FINITE_NUMSEG; REAL_LE_POW_2] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_INTER; SUBSET_REFL; FINITE_NUMSEG; REAL_LE_POW_2];
    DISJ1_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[INTER_SUBSET; FINITE_NUMSEG; REAL_LE_POW_2; FINITE_INTER] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u INTER s SUBSET u INTER t`) THEN
    REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC]);;
```

### Informal statement
For any set $s$, orthonormal system $w$ indexed by natural numbers, and square-integrable function $f$ on $s$, the sequence of squared orthonormal coefficients $(\text{orthonormal\_coefficient}(s, w, f, i))^2$ is summable over any index set $t$.

Formally, for all $s$, $w$, $f$, and $t$:
- If $w$ is an orthonormal system on $s$, i.e., $\langle w_m, w_n \rangle_s = \delta_{mn}$
- Every function $w_i$ in the system is square-integrable on $s$
- $f$ is square-integrable on $s$

Then the series $\sum_{i \in t} (\langle w_i, f \rangle_s)^2$ is convergent.

### Informal proof
We need to show that the series $\sum_{i \in t} (\langle w_i, f \rangle_s)^2$ is convergent. We apply the theorem `CONVERGENT_BOUNDED_MONOTONE` to prove this.

For a sequence to be convergent, we need to verify:
1. The sequence of partial sums is bounded
2. The sequence of partial sums is monotonically increasing

We define our sequence of partial sums as $s_n = \sum_{i \in t \cap \{0,1,...,n\}} (\langle w_i, f \rangle_s)^2$

For boundedness:
- By Bessel's inequality (`BESSEL_INEQUALITY`), we have $\sum_{i \in t \cap \{0,1,...,n\}} (\langle w_i, f \rangle_s)^2 \leq \|f\|_{s}^2$
- This provides an upper bound of $\|f\|_{s}^2$ for all partial sums

For monotonicity:
- When $m \leq n$, we have $\{0,1,...,m\} \subseteq \{0,1,...,n\}$
- Therefore $t \cap \{0,1,...,m\} \subseteq t \cap \{0,1,...,n\}$
- Since all terms in the sum are non-negative (being squares), the sum over $t \cap \{0,1,...,m\}$ is less than or equal to the sum over $t \cap \{0,1,...,n\}$

Therefore, the sequence of partial sums is bounded and monotonically increasing, which means the series $\sum_{i \in t} (\langle w_i, f \rangle_s)^2$ converges.

### Mathematical insight
This theorem establishes that the squared Fourier coefficients of a square-integrable function form a summable sequence. This is a fundamental result in harmonic analysis and the theory of Fourier series.

The result is a direct consequence of Bessel's inequality, which states that the sum of squared Fourier coefficients is bounded by the squared L2-norm of the function. This bound ensures that the infinite sum of squared coefficients converges.

The theorem is important because it shows that the energy of a square-integrable function, when projected onto an orthonormal system, is distributed in a way that the total energy contribution from all basis elements is finite. This allows for the proper definition of Fourier series expansions and supports the concept of approximating functions using orthogonal basis functions.

### Dependencies
- Theorems:
  - `BESSEL_INEQUALITY`: Sum of squared orthonormal coefficients over a finite set is bounded by the square of the L2 norm
  - `CONVERGENT_BOUNDED_MONOTONE`: A bounded monotone sequence converges

- Definitions:
  - `square_integrable_on`: A function is square-integrable if it is measurable and its square is integrable
  - `l2norm`: The L2 norm of a function, defined as the square root of its inner product with itself
  - `orthonormal_system`: A system of functions where the inner product of any two distinct functions is 0, and the inner product of a function with itself is 1
  - `orthonormal_coefficient`: The inner product of a function with an element of the orthonormal system

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the orthonormal system is properly indexed by natural numbers
2. The L2 product (inner product) should be defined in the same way
3. The notion of real summability might be defined differently in other systems, so be careful about the translation
4. The proof relies on the monotone convergence principle, which should be readily available in most proof assistants

---

## ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED

### ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED = prove
 (`!s w a f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s /\ FINITE t
    ==> l2norm s (\x. f x -
                      sum t (\i. orthonormal_coefficient s w f i * w i x))
        pow 2 =
        l2norm s f pow 2 - sum t (\i. orthonormal_coefficient s w f i pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`]);;
```

### Informal statement
For any set $s$, family of functions $w$, function $f$, and finite set $t$:

If 
- $w$ forms an orthonormal system on $s$ (i.e., $\langle w_m, w_n \rangle = \delta_{mn}$, where $\delta_{mn}$ is the Kronecker delta),
- Each function $w_i$ is square-integrable on $s$,
- $f$ is square-integrable on $s$, and
- $t$ is a finite set,

Then the squared $L^2$ norm of the difference between $f$ and its partial Fourier sum equals:

$$\|f - \sum_{i \in t} \langle w_i, f \rangle w_i\|_2^2 = \|f\|_2^2 - \sum_{i \in t} |\langle w_i, f \rangle|^2$$

where $\langle w_i, f \rangle$ represents the orthonormal coefficient (Fourier coefficient) of $f$ with respect to the basis function $w_i$.

### Informal proof
This theorem follows directly from the more general result `ORTHONORMAL_PARTIAL_SUM_DIFF`. 

Starting with the general formula for the squared $L^2$ norm of the difference between $f$ and a linear combination of basis functions:

$$\|f - \sum_{i \in t} a_i w_i\|_2^2 = \|f\|_2^2 + \sum_{i \in t} a_i^2 - 2\sum_{i \in t} a_i \langle w_i, f \rangle$$

We substitute $a_i = \langle w_i, f \rangle$ (which are the orthonormal coefficients) to get:

$$\|f - \sum_{i \in t} \langle w_i, f \rangle w_i\|_2^2 = \|f\|_2^2 + \sum_{i \in t} \langle w_i, f \rangle^2 - 2\sum_{i \in t} \langle w_i, f \rangle^2$$

Simplifying the right side using the algebraic identity $a + b - 2b = a - b$:

$$\|f - \sum_{i \in t} \langle w_i, f \rangle w_i\|_2^2 = \|f\|_2^2 - \sum_{i \in t} \langle w_i, f \rangle^2$$

This gives us the desired result.

### Mathematical insight
This theorem expresses Bessel's inequality for orthonormal systems. It shows that the squared $L^2$ norm of a function minus its orthogonal projection onto a finite-dimensional subspace equals the original squared norm minus the sum of squared Fourier coefficients.

This result has several important implications:
- It confirms that approximating a function with its Fourier partial sum minimizes the $L^2$ error
- It shows that the partial sums of Fourier coefficients are always bounded by the function's energy (squared norm)
- It connects to Parseval's identity, which extends this to complete orthonormal systems

The theorem is fundamental in Fourier analysis, approximation theory, and signal processing, showing how energy is distributed across different orthogonal components of a function.

### Dependencies
- **Theorems**:
  - `ORTHONORMAL_PARTIAL_SUM_DIFF`: Core theorem about the $L^2$ norm of the difference between a function and a linear combination of basis functions
- **Definitions**:
  - `square_integrable_on`: Defines a square-integrable function on a set
  - `l2norm`: Defines the $L^2$ norm of a function
  - `orthonormal_system`: Defines the orthonormality condition for a family of functions
  - `orthonormal_coefficient`: Defines the inner product between a basis function and another function

### Porting notes
When implementing in other systems:
- Ensure the system has a well-defined notion of $L^2$ inner products and norms
- Take care with the treatment of square-integrability, as different systems might have different formulations
- The proof is quite straightforward if the dependency `ORTHONORMAL_PARTIAL_SUM_DIFF` is already available

---

## FOURIER_SERIES_L2_SUMMABLE

### FOURIER_SERIES_L2_SUMMABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2_SUMMABLE = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            ((\n. l2norm s
                    (\x. sum (t INTER (0..n))
                             (\i. orthonormal_coefficient s w f i * w i x) -
                         g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC L2_COMPLETE THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
   MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  REWRITE_TAC[REAL_SUMMABLE; summable; sums; CONVERGENT_EQ_CAUCHY] THEN
  REWRITE_TAC[cauchy; GE] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC WLOG_LE THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THENL
   [ASM_CASES_TAC `N:num <= m` THEN ASM_CASES_TAC `N:num <= n` THEN
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC L2NORM_SUB THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`]) THEN
  SIMP_TAC[DIST_REAL; GSYM drop; DROP_VSUM; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN
   `!f. sum (t INTER (0..n)) f - sum (t INTER (0..m)) f =
        sum (t INTER (m+1..n)) f`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `h:num->real` THEN
    REWRITE_TAC[REAL_ARITH `a - b:real = c <=> b + c = a`] THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG; EXTENSION; IN_INTER; NOT_IN_EMPTY;
             IN_UNION; IN_NUMSEG] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) IN t` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUM; FINITE_INTER;
               FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_POW_2; REAL_ARITH `x <= abs x`]);;
```

### Informal statement
Let $s$ be a measurable set, $w$ be an orthonormal system of functions on $s$, and $f$ be a square integrable function on $s$. If $t$ is any set of indices, then there exists a square integrable function $g$ such that the sequence of partial Fourier series:

$$\left(\sum_{i \in t \cap \{0,1,...,n\}} c_i \cdot w_i(x) \right)_{n=0}^{\infty}$$

where $c_i = \langle w_i, f \rangle$ is the orthonormal coefficient (inner product of $w_i$ and $f$), converges to $g$ in the $L^2$ norm as $n$ approaches infinity.

Formally, for any set $s$, orthonormal system $w$, square integrable function $f$, and set of indices $t$:

$$\text{orthonormal\_system}(s, w) \land (\forall i. w_i \text{ square\_integrable\_on } s) \land (f \text{ square\_integrable\_on } s) \Rightarrow \exists g. (g \text{ square\_integrable\_on } s) \land \left(\left(n \mapsto \left\|{\sum_{i \in t \cap \{0,1,...,n\}} c_i \cdot w_i} - g\right\|_{L^2(s)}\right) \to 0\right) \text{ sequentially}$$

where $c_i = \text{orthonormal\_coefficient}(s, w, f, i)$.

### Informal proof
The proof uses the completeness of the $L^2$ space to show that the sequence of partial Fourier series converges to some function in $L^2$.

1. First, we apply the theorem `L2_COMPLETE` which states that if a sequence of square integrable functions forms a Cauchy sequence in the $L^2$ norm, then it converges to some square integrable function.

2. We verify that our partial Fourier series are square integrable functions:
   - Each term $c_i \cdot w_i$ is square integrable since $w_i$ is square integrable.
   - Finite sums of square integrable functions remain square integrable.

3. We need to show that the sequence of partial sums forms a Cauchy sequence in $L^2$. That is, for any $\varepsilon > 0$, there exists $N$ such that for all $m, n \geq N$, we have:
   $$\|S_n - S_m\|_{L^2(s)} < \varepsilon$$
   where $S_n = \sum_{i \in t \cap \{0,...,n\}} c_i \cdot w_i$.

4. By the theorem `FOURIER_SERIES_SQUARE_SUMMABLE`, the squares of the Fourier coefficients form a summable series:
   $$\sum_{i \in t} c_i^2 < \infty$$

5. Since this series converges, for any $\varepsilon^2 > 0$, there exists $N$ such that for all $m, n \geq N$:
   $$\left|\sum_{i \in t \cap \{0,...,n\}} c_i^2 - \sum_{i \in t \cap \{0,...,m\}} c_i^2\right| < \varepsilon^2$$

6. Without loss of generality, assume $m \leq n$. Then:
   $$S_n - S_m = \sum_{i \in t \cap \{m+1,...,n\}} c_i \cdot w_i$$

7. Using the orthonormality of the system $w$, we compute the $L^2$ norm squared:
   $$\|S_n - S_m\|_{L^2(s)}^2 = \left\langle \sum_{i \in t \cap \{m+1,...,n\}} c_i \cdot w_i, \sum_{j \in t \cap \{m+1,...,n\}} c_j \cdot w_j \right\rangle$$
   
8. Expanding the inner product using the orthonormality condition (which means $\langle w_i, w_j \rangle = 1$ if $i = j$ and $0$ otherwise):
   $$\|S_n - S_m\|_{L^2(s)}^2 = \sum_{i \in t \cap \{m+1,...,n\}} c_i^2$$

9. Since this sum is precisely the difference we bounded in step 5, we have:
   $$\|S_n - S_m\|_{L^2(s)}^2 < \varepsilon^2$$

10. Taking the square root of both sides:
    $$\|S_n - S_m\|_{L^2(s)} < \varepsilon$$

11. This completes the proof that the sequence of partial Fourier series forms a Cauchy sequence in $L^2(s)$, which by completeness of $L^2$, converges to some function $g \in L^2(s)$.

### Mathematical insight
This theorem establishes the convergence of generalized Fourier series in the $L^2$ norm. It is a fundamental result in harmonic analysis and the theory of Hilbert spaces, showing that a square integrable function can be approximated arbitrarily well (in the mean-square sense) by finite linear combinations of functions from an orthonormal system.

The key insight is that:
1. The orthonormality condition ensures that the $L^2$ norm of the difference between partial sums equals the sum of squares of the corresponding Fourier coefficients.
2. Bessel's inequality (used indirectly through `FOURIER_SERIES_SQUARE_SUMMABLE`) ensures that these coefficient squares form a summable series.
3. The completeness of $L^2$ space guarantees the existence of a limit function.

This result forms part of the foundation for Fourier analysis and is closely related to the concept of Hilbert spaces where any element can be represented as an infinite sum of basis elements. In the context of signal processing, it shows how a signal can be decomposed into simpler orthogonal components.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_LMUL`: If $f$ is square integrable on $s$, then so is $c \cdot f$ for any constant $c$
  - `SQUARE_INTEGRABLE_SUM`: Finite sums of square integrable functions are square integrable
  - `L2NORM_POW_2`: The square of the $L^2$ norm equals the inner product of a function with itself
  - `L2PRODUCT_LSUM`, `L2PRODUCT_RSUM`: Properties of inner product with respect to summation
  - `L2PRODUCT_LMUL`, `L2PRODUCT_RMUL`: Properties of inner product with respect to scalar multiplication
  - `L2NORM_SUB`: $L^2$ norm of the difference between functions is symmetric
  - `L2_COMPLETE`: Completeness of $L^2$ space (Cauchy sequences converge)
  - `FOURIER_SERIES_SQUARE_SUMMABLE`: The squares of Fourier coefficients form a summable series

- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it's measurable and its square is integrable
  - `l2norm`: The $L^2$ norm of a function
  - `orthonormal_system`: A system of functions where the inner product of any two different functions is 0, and the inner product of any function with itself is 1
  - `orthonormal_coefficient`: The inner product of a function with a member of an orthonormal system

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-developed theory of measure and integration with corresponding notions of square-integrable functions.
2. The completeness of $L^2$ space might be approached differently in other systems - some may have it as a fundamental axiom rather than a proven theorem.
3. The handling of sequences and limits should be adapted to the target system's conventions.
4. Orthonormal systems might be represented differently, possibly using Hilbert space terminology.
5. The theorem's statement uses finite intersections of sets with ranges of natural numbers, which might require different syntax in other systems.

---

## FOURIER_SERIES_L2_SUMMABLE_STRONG

### FOURIER_SERIES_L2_SUMMABLE_STRONG

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2_SUMMABLE_STRONG = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            (!i. i IN t
                 ==> orthonormal_coefficient s w (\x. f x - g x) i = &0) /\
            ((\n. l2norm s
                   (\x. sum (t INTER (0..n))
                            (\i. orthonormal_coefficient s w f i * w i x) -
                        g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
    MATCH_MP FOURIER_SERIES_L2_SUMMABLE) THEN
  REWRITE_TAC[orthonormal_coefficient] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[orthonormal_coefficient] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. l2product s (w i)
     (\x. (f x - sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x)) +
          (sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x) - g x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2PRODUCT_RADD; SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
    FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `i:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[L2PRODUCT_RSUB; SQUARE_INTEGRABLE_SUM; L2PRODUCT_RSUM;
           FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[L2PRODUCT_RMUL; ETA_AX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
    ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_INTER; IN_NUMSEG; LE_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_REFL];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REALLIM_NULL_COMPARISON)) THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SCHWARTZ_INEQUALITY_ABS o
        lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
      FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[ORTHONORMAL_SYSTEM_L2NORM; REAL_MUL_LID]]);;
```

### Informal statement
Let $s$ be a measurable set, $w$ be an orthonormal system of functions on $s$, and $f$ be a square integrable function on $s$. Let $t$ be a set of indices. Then there exists a square integrable function $g$ such that:

1. For all $i \in t$, the orthonormal coefficient of $f - g$ with respect to $w_i$ is zero:
   $\langle w_i, f - g \rangle_s = 0$

2. The sequence of partial sums of the Fourier series converges to $g$ in the $L^2$ norm:
   $\lim_{n \to \infty} \left\| \sum_{i \in t \cap \{0,1,\ldots,n\}} \langle w_i, f \rangle_s \cdot w_i - g \right\|_2 = 0$

where $\langle \cdot, \cdot \rangle_s$ is the $L^2$ inner product on the set $s$, and $\|\cdot\|_2$ is the corresponding $L^2$ norm.

### Informal proof
This theorem is a strengthening of the result `FOURIER_SERIES_L2_SUMMABLE`. We'll show that the function $g$ whose existence is guaranteed by that theorem also satisfies the additional orthogonality condition.

First, we apply `FOURIER_SERIES_L2_SUMMABLE` to obtain a square-integrable function $g$ such that 
$\lim_{n \to \infty} \left\| \sum_{i \in t \cap \{0,1,\ldots,n\}} \langle w_i, f \rangle_s \cdot w_i - g \right\|_2 = 0$

For the orthogonality condition, we need to prove that for any $i \in t$, 
$\langle w_i, f-g \rangle_s = 0$. 

We use the uniqueness of limits in the real number system and show that this inner product has two expressions that must be equal:

* We can write $\langle w_i, f-g \rangle_s$ as the limit of 
$\langle w_i, f - \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j + \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j - g \rangle_s$

* By linearity of the inner product, this equals
$\langle w_i, f - \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j \rangle_s + \langle w_i, \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j - g \rangle_s$

For the first term:
- For $n \geq i$, we have $i \in t \cap \{0,1,\ldots,n\}$ (assuming $i \in t$)
- By the orthonormality of $w$, we have $\langle w_i, w_j \rangle_s = 1$ if $i = j$ and $0$ otherwise
- Thus $\langle w_i, \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j \rangle_s = \langle w_i, f \rangle_s$
- Therefore $\langle w_i, f - \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j \rangle_s = 0$ for all $n \geq i$

For the second term:
- By the Schwarz inequality:
$|\langle w_i, \sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j - g \rangle_s| \leq \|w_i\|_2 \cdot \|\sum_{j \in t \cap \{0,1,\ldots,n\}} \langle w_j, f \rangle_s \cdot w_j - g\|_2$
- Since $\|w_i\|_2 = 1$ (by orthonormality), and the rightmost term converges to 0 by our assumption, the second term approaches 0 as $n$ approaches infinity.

Therefore, $\langle w_i, f-g \rangle_s = 0 + 0 = 0$ for all $i \in t$.

### Mathematical insight
This theorem establishes a stronger version of the Fourier series convergence result. It shows not only that the Fourier series of a square-integrable function converges in the $L^2$ norm to some function $g$, but also that this function $g$ is precisely the component of $f$ that can be represented using the orthonormal basis elements indexed by $t$.

The orthogonality condition $\langle w_i, f-g \rangle_s = 0$ for all $i \in t$ means that $f-g$ is orthogonal to the subspace spanned by the basis functions indexed by $t$. This makes $g$ the orthogonal projection of $f$ onto this subspace. 

This is a fundamental result in Fourier analysis and more generally in the theory of orthogonal expansions of functions in Hilbert spaces, providing the basis for approximating arbitrary square-integrable functions by linear combinations of orthonormal basis elements.

### Dependencies
- **Theorems**:
  - `FOURIER_SERIES_L2_SUMMABLE`: The weaker version of this theorem that provides $L^2$ convergence
  - `L2PRODUCT_RADD`: Linearity of $L^2$ product with respect to addition
  - `L2PRODUCT_RSUB`: Linearity of $L^2$ product with respect to subtraction
  - `L2PRODUCT_RSUM`: $L^2$ product with a sum becomes a sum of $L^2$ products
  - `L2PRODUCT_RMUL`: Multiplicative property of $L^2$ product
  - `SQUARE_INTEGRABLE_SUB`: Square integrability of the difference of functions
  - `SQUARE_INTEGRABLE_SUM`: Square integrability of the sum of functions
  - `SQUARE_INTEGRABLE_LMUL`: Square integrability of scalar multiplication
  - `SCHWARTZ_INEQUALITY_ABS`: The Schwarz inequality for $L^2$ products
  - `ORTHONORMAL_SYSTEM_L2NORM`: Norm of functions in an orthonormal system is 1

- **Definitions**:
  - `square_integrable_on`: Functions whose square is integrable
  - `l2product`: The inner product in $L^2$ space
  - `l2norm`: The norm in $L^2$ space
  - `orthonormal_system`: A system of functions with orthonormal properties
  - `orthonormal_coefficient`: The Fourier coefficient with respect to an orthonormal basis

### Porting notes
When porting this theorem, pay attention to:

1. The representation of orthonormal systems and their properties
2. The handling of limit theorems in different proof assistants
3. The treatment of measure theory and integration in the target system
4. The notation for inner products and norms, which might differ from HOL Light's `l2product` and `l2norm`
5. The representation of partial sums over finite sets, which might require different lemmas in other systems

---

## REAL_INTEGRABLE_ON_INTERVAL_TAC

### Name of formal statement
REAL_INTEGRABLE_ON_INTERVAL_TAC

### Type of the formal statement
A tactic definition (let binding)

### Formal Content
```ocaml
let REAL_INTEGRABLE_ON_INTERVAL_TAC =
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;;
```

### Informal statement
This is a tactic designed to prove that a real-valued function is integrable on an interval. The tactic works by:
1. Showing that continuous functions are integrable
2. Showing that differentiable functions are continuous
3. Then using automatic differentiation tactics to establish differentiability

### Informal proof
This is a tactic definition and not a theorem, so it doesn't have a proof in the traditional sense. However, the tactic implements the following proof strategy:

1. Apply the theorem `REAL_INTEGRABLE_CONTINUOUS`, which states that continuous functions are integrable on a closed interval.
2. Then prove the continuity by applying `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`, which states that differentiable functions are continuous.
3. Rewrite with `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE` to convert to the standard definition of differentiability.
4. Use a generic tactic (`GEN_TAC`) to introduce a universal quantifier.
5. Handle any assumption with `DISCH_TAC`.
6. Finally, use the automatic differentiation tactic `REAL_DIFFERENTIABLE_TAC` to establish differentiability.

### Mathematical insight
This tactic encapsulates a common proof pattern for establishing integrability of real functions: 
- If a function is differentiable, then it's continuous
- If a function is continuous on a closed interval, then it's integrable

This tactic automates this reasoning chain, which is particularly useful when working with elementary functions like polynomials, trigonometric functions, exponentials, etc., whose differentiability can be established automatically by `REAL_DIFFERENTIABLE_TAC`.

The tactic exemplifies how formal proof assistants can automate routine mathematical reasoning, allowing users to focus on more complex parts of their proofs.

### Dependencies
- **Theorems**:
  - `REAL_INTEGRABLE_CONTINUOUS`: If a function is continuous on a closed interval, then it's integrable
  - `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`: If a function is differentiable on a set, then it's continuous on that set
  - `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`: Relates the HOL Light formal definition of differentiability to the standard mathematical definition

- **Tactics**:
  - `MATCH_MP_TAC`: Applies modus ponens with a theorem
  - `REWRITE_TAC`: Performs rewriting with given theorems
  - `GEN_TAC`: Handles universal quantifiers
  - `DISCH_TAC`: Moves antecedents to the assumption list
  - `REAL_DIFFERENTIABLE_TAC`: Automatically proves differentiability of standard functions

### Porting notes
When porting this tactic to another system:
1. Ensure the target system has corresponding theorems about integrability of continuous functions and continuity of differentiable functions.
2. Check if the target system has automatic differentiation tactics similar to `REAL_DIFFERENTIABLE_TAC`. If not, you might need to implement a similar tactic or use a different approach.
3. Adapt the tactic structure to match the target system's proof style and tactical combinators.

---

## HAS_REAL_INTEGRAL_SIN_NX

### HAS_REAL_INTEGRAL_SIN_NX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_SIN_NX = prove
 (`!n. ((\x. sin(&n * x)) has_real_integral &0) (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0; REAL_MUL_LZERO; SIN_0] THEN
  MP_TAC(ISPECL
   [`\x. --(inv(&n) * cos(&n * x))`; `\x. sin(&n * x)`; `--pi`; `pi`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For any natural number $n$, the function $f(x) = \sin(n \cdot x)$ has real integral equal to $0$ over the interval $[-\pi, \pi]$.

Formally:
$$\forall n \in \mathbb{N}. \int_{-\pi}^{\pi} \sin(n \cdot x) \, dx = 0$$

### Informal proof
The proof proceeds by considering two cases:

- **Case 1**: When $n = 0$
  If $n = 0$, then $\sin(n \cdot x) = \sin(0) = 0$ for all $x$. The integral of the zero function is zero.

- **Case 2**: When $n \neq 0$
  We apply the Fundamental Theorem of Calculus. Let $F(x) = -\frac{1}{n} \cos(n \cdot x)$, which is an antiderivative of $\sin(n \cdot x)$ since $\frac{d}{dx}(-\frac{1}{n} \cos(n \cdot x)) = \sin(n \cdot x)$.
  
  By the Fundamental Theorem of Calculus:
  $$\int_{-\pi}^{\pi} \sin(n \cdot x) \, dx = F(\pi) - F(-\pi) = -\frac{1}{n} \cos(n \cdot \pi) - \left(-\frac{1}{n} \cos(n \cdot (-\pi))\right)$$
  
  Since $\cos(n\pi) = \cos(-n\pi)$, we get:
  $$\int_{-\pi}^{\pi} \sin(n \cdot x) \, dx = -\frac{1}{n} \cos(n \cdot \pi) + \frac{1}{n} \cos(n \cdot \pi) = 0$$

Therefore, the integral of $\sin(n \cdot x)$ over $[-\pi, \pi]$ is equal to $0$ for all natural numbers $n$.

### Mathematical insight
This theorem demonstrates a fundamental property of sine functions with integer frequency: when integrated over a full period (or multiple periods), they yield zero. This is a key result in Fourier analysis where functions are decomposed into sums of sines and cosines.

The result is intuitive geometrically since the sine function has odd symmetry about the origin, meaning $\sin(-x) = -\sin(x)$. When $\sin(nx)$ is integrated over a symmetric interval $[-\pi, \pi]$, the negative and positive contributions exactly cancel each other out.

This property is essential in establishing orthogonality relations for the Fourier basis functions and in computing Fourier coefficients.

### Dependencies
- Fundamental Theorem of Calculus: `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
- Properties of trigonometric functions: `SIN_0`, `SIN_NPI`, `COS_NPI`, `SIN_NEG`, `COS_NEG`
- Basic real analysis: `HAS_REAL_INTEGRAL_0`, `PI_POS_LE`

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-defined notion of real integrals
2. Check that the representation of the interval $[-\pi, \pi]$ matches the target system's conventions
3. The proof relies on differentiation rules for trigonometric functions, so these should be available in the target system
4. The fundamental theorem of calculus should be available in a form that connects derivatives and integrals

---

## REAL_INTEGRABLE_SIN_CX

### REAL_INTEGRABLE_SIN_CX
- `REAL_INTEGRABLE_SIN_CX`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_SIN_CX = prove
 (`!c. (\x. sin(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```

### Informal statement
For all real numbers $c$, the function $f(x) = \sin(cx)$ is Riemann integrable on the interval $[-\pi,\pi]$.

### Informal proof
The proof uses a tactic called `REAL_INTEGRABLE_ON_INTERVAL_TAC`, which is specifically designed to prove integrability of common functions on closed intervals. 

This tactic likely:
1. Recognizes that sine is a continuous function
2. Notes that composition of continuous functions is continuous
3. Applies the fact that continuous functions are Riemann integrable on closed bounded intervals

The tactic handles the proof automatically without requiring further steps.

### Mathematical insight
This theorem establishes the integrability of sinusoidal functions with arbitrary frequency on the standard interval $[-\pi,\pi]$. It's a fundamental result that's needed for various applications in Fourier analysis and when studying properties of special functions.

The result is a special case of the more general fact that continuous functions are Riemann integrable on closed bounded intervals. While seemingly straightforward, having this specific case formalized allows it to be directly referenced in other proofs involving integration of sinusoidal functions.

### Dependencies
Since the proof uses an automatic tactic `REAL_INTEGRABLE_ON_INTERVAL_TAC`, the dependencies are implicit within the tactic itself, but would typically include:
- Theorems about continuity of sine function
- Theorems about preservation of continuity under composition
- Theorems connecting continuity and integrability

### Porting notes
When porting this theorem to another system:
1. Ensure the target system has a definition of Riemann integrability for real-valued functions
2. Verify that the target system has the necessary theorems about continuity implying integrability
3. The proof can likely be reconstructed by directly applying the fact that continuous functions are integrable on closed bounded intervals

---

## REAL_INTEGRAL_SIN_NX

### Name of formal statement
REAL_INTEGRAL_SIN_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. sin(&n * x)) = &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_SIN_NX]);;
```

### Informal statement
For any natural number $n$, the definite integral of $\sin(nx)$ over the interval $[-\pi, \pi]$ is equal to 0:

$$\forall n \in \mathbb{N}. \int_{-\pi}^{\pi} \sin(nx) \, dx = 0$$

### Informal proof
This theorem follows directly from the previously proven result `HAS_REAL_INTEGRAL_SIN_NX`, which states that the function $\sin(nx)$ has integral 0 on the interval $[-\pi, \pi]$.

The proof applies the `REAL_INTEGRAL_UNIQUE` theorem, which states that if a function has a particular real integral value over an interval, then the real integral of that function over that interval equals that value.

Specifically:
1. We start with an arbitrary natural number $n$.
2. We apply `REAL_INTEGRAL_UNIQUE` which requires us to show that $\sin(nx)$ has integral 0.
3. We rewrite using `HAS_REAL_INTEGRAL_SIN_NX` which provides exactly this fact.

### Mathematical insight
This integral result is fundamental in Fourier analysis and orthogonality relations. It demonstrates that sine functions with different integer frequencies are orthogonal to each other over the interval $[-\pi, \pi]$. 

The result can be understood intuitively because the sine function is odd (i.e., $\sin(-x) = -\sin(x)$), and when integrating an odd function over a symmetric interval like $[-\pi, \pi]$, the negative and positive contributions cancel each other out.

This theorem is part of the foundation for Fourier series expansions, where functions are represented as infinite sums of sine and cosine terms.

### Dependencies
- Theorems:
  - `REAL_INTEGRAL_UNIQUE`: States that if a function has a particular real integral value over an interval, then the real integral equals that value
  - `HAS_REAL_INTEGRAL_SIN_NX`: Proves that the function $\sin(nx)$ has integral 0 on $[-\pi, \pi]$

### Porting notes
When porting this theorem to another proof assistant, ensure that:
1. The sine function and definite integrals are properly defined
2. The corresponding version of the Fundamental Theorem of Calculus is available
3. The system has a way to handle real numbers and natural numbers, with appropriate coercions

---

## HAS_REAL_INTEGRAL_COS_NX

### Name of formal statement
HAS_REAL_INTEGRAL_COS_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_COS_NX = prove
 (`!n. ((\x. cos(&n * x)) has_real_integral (if n = 0 then &2 * pi else &0))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[COS_0; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi = &1 * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`\x. inv(&n) * sin(&n * x)`; `\x. cos(&n * x)`; `--pi`; `pi`]
          REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_SUB_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD]);;
```

### Informal statement
For any natural number $n$, the integral of the function $f(x) = \cos(n \cdot x)$ over the interval $[-\pi, \pi]$ is equal to $2\pi$ if $n = 0$, and $0$ otherwise. Formally:

$$\forall n \in \mathbb{N}. \int_{-\pi}^{\pi} \cos(n \cdot x) \, dx = \begin{cases}
2\pi & \text{if } n = 0 \\
0 & \text{if } n \neq 0
\end{cases}$$

### Informal proof
The proof is divided into two cases:

* **Case 1**: When $n = 0$
  
  In this case, $\cos(n \cdot x) = \cos(0) = 1$ for all $x$. Therefore:
  $$\int_{-\pi}^{\pi} \cos(0 \cdot x) \, dx = \int_{-\pi}^{\pi} 1 \, dx = \pi - (-\pi) = 2\pi$$
  We use the fact that the integral of a constant function $f(x) = c$ over an interval $[a,b]$ is $c \cdot (b-a)$.

* **Case 2**: When $n \neq 0$
  
  We apply the Fundamental Theorem of Calculus with the antiderivative $F(x) = \frac{1}{n} \sin(n \cdot x)$ since $\frac{d}{dx}[\frac{1}{n} \sin(n \cdot x)] = \cos(n \cdot x)$.
  
  Therefore:
  $$\int_{-\pi}^{\pi} \cos(n \cdot x) \, dx = \left. \frac{1}{n} \sin(n \cdot x) \right|_{-\pi}^{\pi} = \frac{1}{n} \sin(n\pi) - \frac{1}{n} \sin(-n\pi)$$
  
  Since $\sin(n\pi) = 0$ and $\sin(-n\pi) = -\sin(n\pi) = 0$ for any integer $n$, we get:
  $$\int_{-\pi}^{\pi} \cos(n \cdot x) \, dx = \frac{1}{n} \cdot 0 - \frac{1}{n} \cdot 0 = 0$$

### Mathematical insight
This theorem establishes the orthogonality of the cosine functions over the interval $[-\pi, \pi]$, which is fundamental in Fourier analysis. When $n = 0$, the cosine function becomes constant (equal to 1), and its integral gives the length of the interval ($2\pi$). For all other values of $n$, the integral is zero, demonstrating that these functions are orthogonal to the constant function.

This orthogonality property is essential for decomposing periodic functions into their Fourier series, allowing us to express complex periodic functions as linear combinations of sines and cosines.

### Dependencies
- The theorem uses standard trigonometric identities such as `COS_0`, `SIN_NPI`, `COS_NPI`, `SIN_NEG`, and `COS_NEG`.
- The `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS` is used for the case when $n \neq 0$.
- `HAS_REAL_INTEGRAL_CONST` is used for the case when $n = 0$.
- Basic real number arithmetic and properties, including `PI_POS` and `PI_POS_LE`.

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the trigonometric identities and the fundamental theorem of calculus are available.
2. The handling of the conditional result (if-then-else) might require different approaches in different systems.
3. The definition of integration may vary between systems, so adapt accordingly.

---

## REAL_INTEGRABLE_COS_CX

### REAL_INTEGRABLE_COS_CX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_COS_CX = prove
 (`!c. (\x. cos(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```

### Informal statement
For any real constant $c$, the function $f(x) = \cos(c \cdot x)$ is integrable on the interval $[-\pi, \pi]$.

Formally, for all $c \in \mathbb{R}$, the function $x \mapsto \cos(c \cdot x)$ is real-integrable on the real interval $[-\pi, \pi]$.

### Informal proof
The proof uses a general tactic for proving integrability of functions on intervals.

The theorem is proven by applying the `REAL_INTEGRABLE_ON_INTERVAL_TAC` tactic, which is designed to handle integrability proofs for well-behaved functions on closed intervals. Since $\cos(c \cdot x)$ is continuous for any real $c$, and continuous functions are integrable on closed bounded intervals, the tactic can automatically establish the integrability.

### Mathematical insight
This theorem establishes the integrability of cosine functions with linear arguments on the canonical interval $[-\pi, \pi]$.

This result is part of a standard collection of theorems about the integrability of elementary functions. The function $\cos(c \cdot x)$ is continuous for any real constant $c$, and continuous functions are always integrable on closed bounded intervals.

The interval $[-\pi, \pi]$ is chosen as it represents one complete period for the standard cosine function (when $c = 1$), making this theorem particularly useful for Fourier analysis and related mathematical areas.

### Dependencies
- Used tactics: `GEN_TAC`, `REAL_INTEGRABLE_ON_INTERVAL_TAC`

### Porting notes
When porting to other systems:
- Most proof assistants have built-in lemmas about the integrability of continuous functions, which should make this theorem straightforward to prove.
- The tactic `REAL_INTEGRABLE_ON_INTERVAL_TAC` likely combines continuity of trigonometric functions with a theorem about continuous functions being integrable, so in other systems you may need to make these steps explicit.

---

## REAL_INTEGRAL_COS_NX

### Name of formal statement
REAL_INTEGRAL_COS_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_COS_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. cos(&n * x)) =
       if n = 0 then &2 * pi else &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_COS_NX]);;
```

### Informal statement
For any natural number $n$, the definite integral of $\cos(nx)$ over the interval $[-\pi, \pi]$ is given by:

$$\int_{-\pi}^{\pi} \cos(nx) \, dx = \begin{cases}
2\pi & \text{if } n = 0 \\
0 & \text{if } n \neq 0
\end{cases}$$

### Informal proof
The proof applies the uniqueness of definite integrals. Specifically, we invoke `REAL_INTEGRAL_UNIQUE` and then use the theorem `HAS_REAL_INTEGRAL_COS_NX`, which already establishes that the function $x \mapsto \cos(nx)$ has the stated integral over $[-\pi, \pi]$.

The theorem `HAS_REAL_INTEGRAL_COS_NX` handles two cases:
- When $n = 0$: The integral becomes $\int_{-\pi}^{\pi} \cos(0) \, dx = \int_{-\pi}^{\pi} 1 \, dx = 2\pi$.
- When $n \neq 0$: The integral equals zero, which can be proven using the Fundamental Theorem of Calculus, noting that $\frac{d}{dx}\left(\frac{1}{n}\sin(nx)\right) = \cos(nx)$ and $\sin(n\pi) - \sin(-n\pi) = 0$ for integer $n$.

### Mathematical insight
This theorem establishes a fundamental property of trigonometric functions that forms the basis of Fourier series analysis. The result demonstrates the orthogonality properties of the cosine functions over the interval $[-\pi, \pi]$, which is crucial for the development of Fourier analysis.

Specifically, when $n = 0$, the cosine function is constant (equal to 1), so the integral equals the length of the interval. When $n \neq 0$, the result shows that different cosine functions with integer frequencies are orthogonal to each other with respect to integration over $[-\pi, \pi]$.

This property allows us to decompose periodic functions into sums of sine and cosine functions with different frequencies.

### Dependencies
- `REAL_INTEGRAL_UNIQUE`: Establishes the uniqueness of definite integrals.
- `HAS_REAL_INTEGRAL_COS_NX`: States that the function $\cos(nx)$ has a definite integral over $[-\pi, \pi]$ equal to $2\pi$ if $n = 0$ and $0$ otherwise.

### Porting notes
When porting this theorem to other systems, ensure that:
1. The definition of `real_integral` and `has_real_integral` are consistently handled.
2. The representation of natural numbers as reals (denoted by `&n` in HOL Light) is properly translated.
3. The corresponding version of the Fundamental Theorem of Calculus exists in the target system.

---

## REAL_INTEGRAL_SIN_AND_COS

### REAL_INTEGRAL_SIN_AND_COS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_AND_COS = prove
 (`!m n. real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * cos(&n * x)) =
                (if m = n then if n = 0 then &2 * pi else pi else &0) /\
         real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * sin(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * cos(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * sin(&n * x)) =
              (if m = n /\ ~(n = 0) then pi else &0)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
              REAL_MUL_COS_COS; REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
  SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRAL_SUB; real_div;
           REAL_INTEGRABLE_SIN_CX; REAL_INTEGRABLE_COS_CX;
           REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_ADD] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_NX; REAL_INTEGRAL_COS_NX] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> (m - n = 0 <=> m = n)`] THEN
  REWRITE_TAC[ADD_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ARITH `(a + a) * inv(&2) = a`;
                  REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
This theorem establishes the orthogonality relationships of trigonometric functions over the interval $[-\pi, \pi]$. For any natural numbers $m$ and $n$:

1. $\int_{-\pi}^{\pi} \cos(mx) \cos(nx) \, dx = \begin{cases}
   2\pi & \text{if } m = n = 0 \\
   \pi & \text{if } m = n \neq 0 \\
   0 & \text{if } m \neq n
   \end{cases}$

2. $\int_{-\pi}^{\pi} \cos(mx) \sin(nx) \, dx = 0$

3. $\int_{-\pi}^{\pi} \sin(mx) \cos(nx) \, dx = 0$

4. $\int_{-\pi}^{\pi} \sin(mx) \sin(nx) \, dx = \begin{cases}
   \pi & \text{if } m = n \neq 0 \\
   0 & \text{otherwise}
   \end{cases}$

### Informal proof
The proof employs trigonometric identities and properties of definite integrals:

1. Without loss of generality, assume $n \leq m$ (by symmetry of multiplication).

2. Apply the standard trigonometric product-to-sum formulas:
   - $\cos(mx)\cos(nx) = \frac{1}{2}[\cos((m+n)x) + \cos((m-n)x)]$
   - $\cos(mx)\sin(nx) = \frac{1}{2}[\sin((m+n)x) - \sin((m-n)x)]$
   - $\sin(mx)\cos(nx) = \frac{1}{2}[\sin((m+n)x) + \sin((m-n)x)]$
   - $\sin(mx)\sin(nx) = \frac{1}{2}[\cos((m-n)x) - \cos((m+n)x)]$

3. Use the linearity of the integral to distribute over the sums and differences.

4. Apply the known integral results:
   - $\int_{-\pi}^{\pi} \sin(kx) \, dx = 0$ for any integer $k$
   - $\int_{-\pi}^{\pi} \cos(kx) \, dx = \begin{cases}
     2\pi & \text{if } k = 0 \\
     0 & \text{if } k \neq 0
     \end{cases}$

5. Simplify the resulting expressions, handling special cases:
   - When $m = n$, then $m-n = 0$
   - When $n = 0$, special treatment is needed for certain cases

6. The final results follow from straightforward real arithmetic simplification.

### Mathematical insight
This theorem establishes the orthogonality relationships of the trigonometric basis functions over $[-\pi,\pi]$, which is fundamental to Fourier analysis. These orthogonality relationships show that the functions $\{1, \cos(x), \cos(2x), \ldots, \sin(x), \sin(2x), \ldots\}$ form an orthogonal system with respect to the standard inner product on $L^2[-\pi,\pi]$.

These relationships are crucial for calculating Fourier coefficients, as they ensure that when projecting a function onto this basis, the coefficients can be computed independently. This theorem provides the normalization constants needed when working with Fourier series representations of periodic functions.

### Dependencies
- `REAL_INTEGRABLE_SIN_CX`: The function $x \mapsto \sin(cx)$ is integrable on $[-\pi,\pi]$ for any constant $c$.
- `REAL_INTEGRAL_SIN_NX`: The integral of $\sin(nx)$ over $[-\pi,\pi]$ equals 0 for any natural number $n$.
- `REAL_INTEGRABLE_COS_CX`: The function $x \mapsto \cos(cx)$ is integrable on $[-\pi,\pi]$ for any constant $c$.
- `REAL_INTEGRAL_COS_NX`: The integral of $\cos(nx)$ over $[-\pi,\pi]$ equals $2\pi$ if $n=0$ and 0 otherwise.

### Porting notes
When porting this theorem:
1. Ensure that the trigonometric product-to-sum identities are available or easily provable.
2. The linearity properties of integrals should be established.
3. The integrals of individual sine and cosine functions over $[-\pi,\pi]$ need to be available.
4. Depending on the proof assistant, the case analysis (especially handling $m=n$ and $n=0$ cases) might require different tactics or approaches.

---

## REAL_INTEGRABLE_SIN_AND_COS

### REAL_INTEGRABLE_SIN_AND_COS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_SIN_AND_COS = prove
 (`!m n a b.
      (\x. cos(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. cos(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```

### Informal statement
For all integers $m, n$ and real numbers $a, b$, the following functions are integrable on the real interval $[a,b]$:
- $f(x) = \cos(m \cdot x) \cdot \cos(n \cdot x)$
- $f(x) = \cos(m \cdot x) \cdot \sin(n \cdot x)$
- $f(x) = \sin(m \cdot x) \cdot \cos(n \cdot x)$
- $f(x) = \sin(m \cdot x) \cdot \sin(n \cdot x)$

Where $\cdot$ denotes multiplication, and $&m$ and $&n$ in the formal statement represent the conversion from integers to real numbers.

### Informal proof
The proof is straightforward and follows from the integrability properties of trigonometric functions:

- All four statements are proved simultaneously using the tactic `REAL_INTEGRABLE_ON_INTERVAL_TAC`, which is designed to prove integrability of expressions on real intervals.
- This tactic likely uses the facts that:
  - Sine and cosine functions are continuous on the real line
  - Products of continuous functions are continuous
  - Continuous functions are integrable on closed bounded intervals

### Mathematical insight
This theorem establishes the integrability of products of trigonometric functions with integer frequency parameters. Such products frequently appear in Fourier analysis, signal processing, and when solving differential equations.

The result is fundamental because:
- These products arise when analyzing orthogonality relations between trigonometric functions
- They are building blocks for more complex integrations involving trigonometric functions
- They are used in computing Fourier coefficients

The theorem covers all four possible combinations of sine and cosine products systematically, making it a convenient reference result for more complex analyses.

### Dependencies
- `REAL_INTEGRABLE_ON_INTERVAL_TAC`: A specialized tactic that proves integrability of expressions on real intervals

### Porting notes
When porting to other systems:
- Ensure the target system has established libraries for real analysis, continuity, and integration
- The result is relatively straightforward once basic real analysis is in place
- Check how the target system handles the conversion from integers to reals (represented by `&m` and `&n` in HOL Light)
- The proof might be even more direct in systems with automated real analysis tactics

---

## trigonometric_set_def

### Name of formal statement
trigonometric_set_def

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let trigonometric_set_def = new_definition
 `trigonometric_set n =
    if n = 0 then \x. &1 / sqrt(&2 * pi)
    else if ODD n then \x. sin(&(n DIV 2 + 1) * x) / sqrt(pi)
    else \x. cos(&(n DIV 2) * x) / sqrt(pi)`;;
```

### Informal statement
The definition `trigonometric_set` defines a family of trigonometric functions indexed by natural numbers:

$$\text{trigonometric\_set}(n) = 
\begin{cases}
\frac{1}{\sqrt{2\pi}} & \text{if } n = 0 \\
\frac{\sin((n \text{ DIV } 2 + 1)x)}{\sqrt{\pi}} & \text{if } n \text{ is odd} \\
\frac{\cos((n \text{ DIV } 2)x)}{\sqrt{\pi}} & \text{if } n \text{ is even and } n \neq 0
\end{cases}$$

where `DIV` represents integer division.

### Informal proof
This is a definition, so there is no proof. However, the related theorem `trigonometric_set` (shown in the dependencies) proves that this definition can be expressed in a more explicit form:

$$\text{trigonometric\_set}(0) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$$
$$\text{trigonometric\_set}(2n+1) = \frac{\sin((n+1)x)}{\sqrt{\pi}}$$
$$\text{trigonometric\_set}(2n+2) = \frac{\cos((n+1)x)}{\sqrt{\pi}}$$

### Mathematical insight
This definition creates a countable family of normalized trigonometric functions that form an orthonormal basis for $L^2[-\pi,\pi]$. The functions include:
- A constant function (when $n=0$)
- Sine functions with increasing frequencies (for odd $n$)
- Cosine functions with increasing frequencies (for even $n \neq 0$)

The normalization factors $\frac{1}{\sqrt{2\pi}}$ and $\frac{1}{\sqrt{\pi}}$ ensure that these functions have unit norm in the $L^2$ space. This family is crucial for Fourier analysis, particularly for representing periodic functions as infinite series of sines and cosines, or for performing spectral analysis.

The special case for $n=0$ accounts for the different normalization needed for the constant function, while the DIV operations in the definition handle the appropriate frequency assignment for each index $n$.

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Provides an alternative, more explicit representation of this definition

### Porting notes
When porting this definition to another system:
1. Ensure the target system has good support for conditional expressions
2. Verify how integer division (DIV) is handled in the target system
3. Make sure the target system can handle real-valued functions properly
4. Check that trigonometric functions and square root are properly defined in the target system

---

## trigonometric_set

### trigonometric_set
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let trigonometric_set = prove
 (`trigonometric_set 0 = (\x. cos(&0 * x) / sqrt(&2 * pi)) /\
   trigonometric_set (2 * n + 1) = (\x. sin(&(n + 1) * x) / sqrt(pi)) /\
   trigonometric_set (2 * n + 2) = (\x. cos(&(n + 1) * x) / sqrt(pi))`,
  REWRITE_TAC[trigonometric_set_def; EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0;
              GSYM NOT_EVEN] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n`] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 2) DIV 2 = n + 1`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0]);;
```

### Informal statement
This theorem provides explicit expressions for the `trigonometric_set` function for different values of its integer argument:

1. $\text{trigonometric\_set}(0) = \lambda x. \frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$
2. $\text{trigonometric\_set}(2n+1) = \lambda x. \frac{\sin((n+1) \cdot x)}{\sqrt{\pi}}$ for any natural number $n$
3. $\text{trigonometric\_set}(2n+2) = \lambda x. \frac{\cos((n+1) \cdot x)}{\sqrt{\pi}}$ for any natural number $n$

These equalities hold for all real values of $x$.

### Informal proof
The proof involves simplifying the expressions by applying the definition of `trigonometric_set` and using properties of even and odd numbers:

1. Apply the definition of `trigonometric_set`.
2. Use properties of even and odd numbers to simplify the conditions in the definition.
3. For expressions involving integer division:
   - Show that $(2n+1) \div 2 = n$
   - Show that $(2n+2) \div 2 = n+1$
4. For the case where $n=0$, use the fact that $\cos(0 \cdot x) = \cos(0) = 1$, so the expression simplifies to $\frac{1}{\sqrt{2\pi}}$.

### Mathematical insight
This theorem provides explicit formulations for the trigonometric basis functions used in Fourier analysis. The functions form an orthonormal basis for $L^2[-\pi,\pi]$ and are crucial for decomposing periodic functions into sine and cosine components.

The pattern demonstrates how the functions alternate between sine and cosine terms with increasing frequency as the index increases, with a special normalization factor for the constant term (when $n=0$).

The normalization by $\sqrt{\pi}$ or $\sqrt{2\pi}$ ensures that these functions have the appropriate orthonormality properties needed for Fourier analysis.

### Dependencies
- Definitions:
  - `trigonometric_set_def`: Defines the trigonometric set function based on cases for different values of n
- Theorems:
  - `EVEN_ADD`: Properties of even numbers under addition
  - `EVEN_MULT`: Properties of even numbers under multiplication
  - `ARITH`: Basic arithmetic simplifications
  - `ADD_EQ_0`: Property of addition equaling zero
  - `GSYM NOT_EVEN`: Relationship between not even and odd
  - `REAL_MUL_LZERO`: Property that multiplication by zero gives zero
  - `COS_0`: The value of cosine at zero is 1

### Porting notes
When implementing this in other proof assistants:
1. Make sure the host system has appropriate definitions for trigonometric functions and their basic properties
2. Pay attention to how integer division is defined in the target system, as the DIV operation is crucial here
3. The representation of functions as lambda expressions might differ in syntax across systems

---

## TRIGONOMETRIC_SET_EVEN

### TRIGONOMETRIC_SET_EVEN
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_EVEN = prove
 (`!k. trigonometric_set(2 * k) =
        if k = 0 then \x. &1 / sqrt(&2 * pi)
        else \x. cos(&k * x) / sqrt pi`,
  INDUCT_TAC THEN
  REWRITE_TAC[ARITH; trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
  REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * SUC k = 2 * k + 2`] THEN
  REWRITE_TAC[trigonometric_set; GSYM ADD1]);;
```

### Informal statement
This theorem provides a simplified formula for the trigonometric set functions with even indices. Specifically, for all natural numbers $k$:

$$\text{trigonometric\_set}(2k) = 
\begin{cases} 
\frac{1}{\sqrt{2\pi}} & \text{if } k = 0 \\
\frac{\cos(kx)}{\sqrt{\pi}} & \text{if } k > 0
\end{cases}$$

### Informal proof
The proof proceeds by induction on $k$:

* **Base case** ($k = 0$):
  We need to show $\text{trigonometric\_set}(0) = \frac{1}{\sqrt{2\pi}}$.
  By the definition of `trigonometric_set`, we know that $\text{trigonometric\_set}(0) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$.
  Since $\cos(0) = 1$, this simplifies to $\frac{1}{\sqrt{2\pi}}$.

* **Inductive case** ($k \to k+1$):
  We need to show $\text{trigonometric\_set}(2(k+1)) = \frac{\cos((k+1)x)}{\sqrt{\pi}}$.
  We can rewrite $2(k+1)$ as $2k + 2$.
  From the `trigonometric_set` theorem, we know that $\text{trigonometric\_set}(2n + 2) = \frac{\cos((n+1)x)}{\sqrt{\pi}}$.
  Substituting $n = k$, we get $\text{trigonometric\_set}(2k + 2) = \frac{\cos((k+1)x)}{\sqrt{\pi}}$.
  This completes the induction.

### Mathematical insight
This theorem provides a cleaner and more direct formulation of the trigonometric set functions for even indices. The trigonometric set functions form an orthonormal basis for the space of $L^2$ functions on the interval $[-\pi, \pi]$, which is crucial in Fourier analysis. 

The special case for $k=0$ results in the constant function $\frac{1}{\sqrt{2\pi}}$, which corresponds to the DC component in Fourier series. For all other even indices, the functions are scaled cosine functions with specific frequencies.

This formulation makes it easier to work with these functions in applications like Fourier analysis, where understanding the behavior of functions with different indices is important.

### Dependencies
- `trigonometric_set`: Defines the trigonometric set functions for different indices
- `COS_0`: States that cosine of zero is one

### Porting notes
When porting this theorem, pay attention to:
1. The induction tactic used in HOL Light
2. The handling of conditional expressions
3. The representation of real numbers (denoted with `&` in HOL Light)
4. The simplification of arithmetic expressions

---

## ODD_EVEN_INDUCT_LEMMA

### ODD_EVEN_INDUCT_LEMMA
- This is the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODD_EVEN_INDUCT_LEMMA = prove
 (`(!n:num. P 0) /\ (!n. P(2 * n + 1)) /\ (!n. P(2 * n + 2)) ==> !n. P n`,
  REWRITE_TAC[FORALL_SIMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE
    `SUC(2 * n) = 2 * n + 1 /\ SUC(2 * n + 1) = 2 * n + 2`]);;
```

### Informal statement
The theorem states that for any predicate $P$ on natural numbers, if:
1. $P(0)$ holds, and
2. $P(2n + 1)$ holds for all natural numbers $n$, and
3. $P(2n + 2)$ holds for all natural numbers $n$,

then $P(n)$ holds for all natural numbers $n$.

Formally, this is expressed as:
$$((\forall n \in \mathbb{N}. P(0)) \wedge (\forall n \in \mathbb{N}. P(2n + 1)) \wedge (\forall n \in \mathbb{N}. P(2n + 2))) \Rightarrow \forall n \in \mathbb{N}. P(n)$$

### Informal proof
The proof proceeds by standard natural number induction:

1. First, we simplify the universal quantifier and establish the assumption that:
   - $P(0)$ holds
   - For all $n$, $P(2n + 1)$ holds
   - For all $n$, $P(2n + 2)$ holds

2. We apply natural number induction (`num_INDUCTION`) to prove $\forall n. P(n)$:
   - The base case $P(0)$ is handled by our assumptions.
   
3. For the inductive step, consider arbitrary $n$ where we assume $P(n)$ and need to prove $P(n+1)$.

4. We use the fact that every natural number is either even or odd (`EVEN_OR_ODD`):
   - If $n$ is even, then $n = 2k$ for some $k$
   - If $n$ is odd, then $n = 2k + 1$ for some $k$

5. We then use arithmetic to establish that:
   - $\text{SUC}(2n) = 2n + 1$, which is covered by our assumption that all odd numbers satisfy $P$
   - $\text{SUC}(2n + 1) = 2n + 2$, which is covered by our assumption that all numbers of the form $2n + 2$ satisfy $P$

6. Therefore, in either case, we conclude that $P(n+1)$ holds, completing the induction.

### Mathematical insight
This theorem establishes an alternative induction principle for natural numbers based on their parity. Instead of the standard induction basis (0) and step (n to n+1), this principle requires proving:
1. The base case for 0
2. The step case for even numbers to the next odd number (2n to 2n+1)
3. The step case for odd numbers to the next even number (2n+1 to 2n+2)

This induction scheme is particularly useful when dealing with problems where the behavior of even and odd numbers needs to be treated differently. It allows for more direct proofs in cases where properties have a pattern that alternates between even and odd numbers.

### Dependencies
- `num_INDUCTION`: The standard induction principle for natural numbers
- `EVEN_OR_ODD`: The theorem stating that every natural number is either even or odd
- `EVEN_EXISTS`: The characterization that a number is even iff it equals 2n for some n
- `ODD_EXISTS`: The characterization that a number is odd iff it equals 2n+1 for some n
- `ARITH_RULE`: A simplification rule for arithmetic calculations

### Porting notes
When porting this theorem:
1. Most proof assistants have equivalents for natural number induction and parity definitions.
2. The arithmetic simplification step might need to be handled differently depending on how the target system manages arithmetic reasoning.
3. The conclusion is structurally simple and should translate directly to other systems.

---

## ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET

### ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET = prove
 (`orthonormal_system (real_interval[--pi,pi]) trigonometric_set`,
  REWRITE_TAC[orthonormal_system; l2product] THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[REAL_ARITH `a / k * b / l:real = (inv(k) * inv(l)) * a * b`] THEN
  SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_SIN_AND_COS] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_AND_COS] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `m:num = n` THEN
  TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY (MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 = a + b <=> a = 0 /\ b = 0`;
                  EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN
  REWRITE_TAC[ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
The theorem states that the trigonometric system forms an orthonormal system on the interval $[-\pi, \pi]$. Formally:

$$\text{orthonormal\_system}([-\pi, \pi], \text{trigonometric\_set})$$

This means that for all natural numbers $m$ and $n$, the $L^2$ inner product of $\text{trigonometric\_set}(m)$ and $\text{trigonometric\_set}(n)$ equals 1 if $m = n$ and 0 otherwise.

### Informal proof
The proof establishes that the trigonometric functions form an orthonormal system on $[-\pi, \pi]$, meaning they satisfy the orthonormality property:

$$\int_{-\pi}^{\pi} \text{trigonometric\_set}(m)(x) \cdot \text{trigonometric\_set}(n)(x) \, dx = \begin{cases} 1 & \text{if } m = n \\ 0 & \text{if } m \neq n \end{cases}$$

The proof proceeds as follows:

- First, we unfold the definitions of `orthonormal_system` and `l2product`.
  
- We apply `ODD_EVEN_INDUCT_LEMMA` twice (once for $m$ and once for $n$), which means we need to prove the orthonormality relation for all combinations of cases:
  * Case 0 with 0
  * Case 0 with odd numbers
  * Case 0 with even numbers (excluding 0)
  * Case odd numbers with odd numbers
  * Case odd numbers with even numbers
  * Case even numbers with even numbers

- We use the definition of `trigonometric_set` to express these cases in terms of sine and cosine functions:
  * $\text{trigonometric\_set}(0)(x) = \cos(0 \cdot x)/\sqrt{2\pi}$
  * $\text{trigonometric\_set}(2n+1)(x) = \sin((n+1) \cdot x)/\sqrt{\pi}$
  * $\text{trigonometric\_set}(2n+2)(x) = \cos((n+1) \cdot x)/\sqrt{\pi}$

- For each case, we:
  1. Express the product as a multiplication with constants pulled out
  2. Use the integrals of products of sine and cosine functions (from `REAL_INTEGRAL_SIN_AND_COS`)
  3. Simplify the resulting expressions

- When $m = n$, we get integrals that evaluate to $\pi$ or $2\pi$, which, when multiplied by the appropriate normalization factors, give $1$.

- When $m \neq n$, the orthogonality properties of sine and cosine functions ensure that the integrals evaluate to $0$.

- The final part of the proof involves verifying that the normalization factors (inverse of square roots of $\pi$ or $2\pi$) properly convert the integrals to $1$ in the case where $m = n$.

### Mathematical insight
This theorem establishes that the trigonometric functions form an orthonormal basis for the $L^2$ space on $[-\pi, \pi]$. This is a fundamental result for Fourier analysis, allowing arbitrary square-integrable functions to be represented as linear combinations of these trigonometric functions.

The orthonormality property is crucial because it:
1. Makes the computation of Fourier coefficients straightforward
2. Ensures the uniqueness of Fourier series representations
3. Allows Parseval's identity to hold, connecting the $L^2$ norm of a function with the sum of squares of its Fourier coefficients

The specific normalization factors (dividing by $\sqrt{\pi}$ or $\sqrt{2\pi}$) are chosen to ensure the orthonormality property holds, making the trigonometric system a proper orthonormal basis rather than just an orthogonal basis.

### Dependencies
- **Theorems**:
  - `REAL_INTEGRAL_SIN_AND_COS`: Provides integral values for products of sine and cosine functions
  - `REAL_INTEGRABLE_SIN_AND_COS`: Establishes integrability of products of sine and cosine functions
  - `trigonometric_set`: Defines the trigonometric functions used in the theorem
  - `ODD_EVEN_INDUCT_LEMMA`: Used for induction on natural numbers by cases (0, odd, even)

- **Definitions**:
  - `l2product`: Defines the $L^2$ inner product as an integral of the product of two functions
  - `orthonormal_system`: Defines what it means for a system of functions to be orthonormal

### Porting notes
When porting this theorem:
1. Ensure that the trigonometric functions are properly normalized with the correct factors ($1/\sqrt{\pi}$ or $1/\sqrt{2\pi}$).
2. The proof relies heavily on the properties of integrals of products of sine and cosine functions, so these should be established first.
3. The induction pattern using separate cases for even and odd numbers is a key proof technique here, which might need to be adapted based on the induction principles available in the target system.
4. The orthonormality relationship is a standard concept in functional analysis, but the specific definition might vary slightly between systems.

---

## SQUARE_INTEGRABLE_TRIGONOMETRIC_SET

### Name of formal statement
SQUARE_INTEGRABLE_TRIGONOMETRIC_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_TRIGONOMETRIC_SET = prove
 (`!i. (trigonometric_set i) square_integrable_on real_interval[--pi,pi]`,
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[real_div] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC);;
```

### Informal statement
For all natural numbers $i$, the function $\text{trigonometric\_set}(i)$ is square integrable on the real interval $[-\pi, \pi]$.

Where $\text{trigonometric\_set}$ is defined as:
- $\text{trigonometric\_set}(0) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}} = \frac{1}{\sqrt{2\pi}}$
- $\text{trigonometric\_set}(2n+1) = \frac{\sin((n+1) \cdot x)}{\sqrt{\pi}}$ for any $n \geq 0$
- $\text{trigonometric\_set}(2n+2) = \frac{\cos((n+1) \cdot x)}{\sqrt{\pi}}$ for any $n \geq 0$

### Informal proof
We prove this statement by induction on the index $i$ using the lemma `ODD_EVEN_INDUCT_LEMMA`, which allows us to proceed by considering three cases: $i = 0$, $i = 2n + 1$, and $i = 2n + 2$.

For each case, we:

1. Expand the definition of `trigonometric_set` using the trigonometric_set theorem.
2. Rewrite the division expressions using `real_div`.
3. Apply `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`, which states that any continuous function on a closed interval is square integrable on that interval.
4. Prove that the trigonometric functions are continuous by showing they are differentiable, using `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`.
5. The differentiability of sine and cosine functions is established using the built-in differentiability tactic `REAL_DIFFERENTIABLE_TAC`.

Since all functions in the trigonometric set are differentiable on $[-\pi, \pi]$, they are continuous, and therefore square integrable on this interval.

### Mathematical insight
This theorem establishes that the functions in the trigonometric set are square integrable on the interval $[-\pi, \pi]$, which is crucial for Fourier analysis. These functions form an orthonormal basis for the space of square integrable functions on $[-\pi, \pi]$, and this property ensures that Fourier series expansions are well-defined.

The trigonometric set consists of normalized sine and cosine functions that are used in Fourier analysis. The normalization factors ($\frac{1}{\sqrt{2\pi}}$ for the constant function and $\frac{1}{\sqrt{\pi}}$ for the others) ensure that these functions form an orthonormal system with respect to the $L^2$ inner product on $[-\pi, \pi]$.

This result is a fundamental building block for proving properties of Fourier series and developing the theory of function approximation in Hilbert spaces.

### Dependencies
- **Theorems**:
  - `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`: Any continuous function on a closed interval is square integrable
  - `trigonometric_set`: Defines the functions in the trigonometric set
  - `ODD_EVEN_INDUCT_LEMMA`: Induction principle for proving properties for all natural numbers by showing them for 0, odd numbers, and even numbers

- **Definitions**:
  - `square_integrable_on`: A function is square integrable on a set if it is measurable and its square is integrable

### Porting notes
When porting this theorem to other proof assistants, consider the following:

1. You may need to define the trigonometric set functions first, ensuring proper normalization factors.
2. The proof strategy should transfer well to other systems, but the specific tactics for proving differentiability might differ.
3. In systems like Lean or Coq, you might need to prove the continuity of sine and cosine functions explicitly if such results are not already available in their libraries.
4. The odd-even induction principle might need to be proved separately if not available in the target system.

---

## WEIERSTRASS_TRIG_POLYNOMIAL

### WEIERSTRASS_TRIG_POLYNOMIAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WEIERSTRASS_TRIG_POLYNOMIAL = prove
 (`!f e. f real_continuous_on real_interval[--pi,pi] /\
         f(--pi) = f pi /\ &0 < e
         ==> ?n a b.
                !x. x IN real_interval[--pi,pi]
                    ==> abs(f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  let lemma1 = prove
   (`!f. f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= Re z \/ Re z < &0`) THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `Cx o f o (\x. x + pi) o Im o clog o (--)` THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
        ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[CLOG_NEG; o_THM] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX; REAL_SUB_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH `(x + pi) + pi = x + &2 * pi`];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN CONTINUOUS_TAC;
          REWRITE_TAC[GSYM o_ASSOC; GSYM REAL_CONTINUOUS_CONTINUOUS]]]] THEN
    REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOG THEN
       REWRITE_TAC[GSYM real] THEN DISCH_TAC THEN
       UNDISCH_TAC `norm(z:complex) = &1` THEN
       ASM_SIMP_TAC[REAL_NORM; RE_NEG; REAL_NEG_GT0] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
        SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_CONST;
                 REAL_CONTINUOUS_WITHIN_ID]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    SIMP_TAC[IN_UNIV; WITHINREAL_UNIV]) in
  let lemma2 = prove
   (`!f. f real_continuous_on real_interval[--pi,pi] /\ f(--pi) = f pi
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`f:real->real`; `--pi`; `pi`] REAL_TIETZE_PERIODIC_INTERVAL) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `g:real->real` lemma1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
    MATCH_MP_TAC(REWRITE_RULE
     [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
      CONTINUOUS_TRANSFORM_WITHIN) THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; CLOG_WORKS; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  (CHOOSE_THEN MP_TAC o prove_inductive_relations_exist)
   `(!c. poly2 (\x. c)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x + q x)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x * q x)) /\
    poly2 Re /\ poly2 Im` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`poly2:(complex->real)->bool`; `{z:complex | norm z = &1}`]
        STONE_WEIERSTRASS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_REFL];
        ONCE_REWRITE_TAC[SET_RULE `{x | p x} = {x | x IN UNIV /\ p x}`] THEN
        REWRITE_TAC[GSYM LIFT_EQ] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; GSYM o_DEF; CLOSED_UNIV]];
      MATCH_MP_TAC(MESON[]
       `(!x f. P f ==> R f x) ==> (!f. P f ==> !x. Q x ==> R f x)`) THEN
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_MUL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONST;
                  REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
      REWRITE_TAC[IN_ELIM_THM; COMPLEX_EQ; DE_MORGAN_THM] THEN STRIP_TAC THENL
       [EXISTS_TAC `Re` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `Im` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(f:real->real) o Im o clog`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; lemma2] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `trigpoly =
     \f. ?n a b.
         f = \x. sum(0..n) (\k. a k * sin(&k * x) +  b k * cos(&k * x))` THEN
  SUBGOAL_THEN `!c:real. trigpoly(\x:real. c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:real` THEN EXPAND_TAC "trigpoly" THEN REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[SUM_SING_NUMSEG; REAL_MUL_LZERO; SIN_0; COS_0] THEN
    MAP_EVERY EXISTS_TAC [`(\n. &0):num->real`; `(\n. c):num->real`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x + g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`n1:num`; `a1:num->real`; `b1:num->real`;
      `n2:num`; `a2:num->real`; `b2:num->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`MAX n1 n2`;
      `(\n. (if n <= n1 then a1 n else &0) +
             (if n <= n2 then a2 n else &0)):num->real`;
      `(\n. (if n <= n1 then b1 n else &0) +
            (if n <= n2 then b2 n else &0)):num->real`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; FUN_EQ_THM; REAL_ADD_RDISTRIB] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a:real = e /\ b = g /\ c = f /\ d = h
      ==> (a + b) + (c + d) = (e + f) + (g + h)`) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f s:num->bool. FINITE s /\ (!i. i IN s ==> trigpoly(f i))
                    ==> trigpoly(\x:real. sum s (\i. f i x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[SUM_CLAUSES; IN_INSERT; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real->real c. trigpoly f ==> trigpoly (\x. c * f x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC
     [`n:num`; `\i. c * (a:num->real) i`; `\i. c * (b:num->real) i`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. sin(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. if i = k then &1 else &0`; `\i:num. &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. cos(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. &0`; `\i:num. if i = k then &1 else &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. trigpoly(\x. sin(&i * x) * sin(&j * x)) /\
          trigpoly(\x. sin(&i * x) * cos(&j * x)) /\
          trigpoly(\x. cos(&i * x) * sin(&j * x)) /\
          trigpoly(\x. cos(&i * x) * cos(&j * x))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC WLOG_LE THEN
    CONJ_TAC THENL [REWRITE_TAC[CONJ_ACI; REAL_MUL_AC]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
                REAL_MUL_COS_COS] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`;
                REAL_ARITH `x - y:real = x + --(&1) * y`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x * g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM
         th]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL STRIP_THM_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_SUM_NUMSEG] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
    `(ai * si + bi * ci) * (aj * sj + bj * cj):real =
     ((ai * aj) * (si * sj) + (bi * bj) * (ci * cj)) +
     ((ai * bj) * (si * cj) + (aj * bi) * (ci * sj))`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:complex->real. poly2 f ==> trigpoly(\x.  f(cexp(ii * Cx x)))`
  (MP_TAC o SPEC `g:complex->real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[RE_CEXP; IM_CEXP; RE_MUL_II; IM_CX; IM_MUL_II; RE_CX] THEN
    ONCE_REWRITE_TAC[MESON[REAL_MUL_LID]
     `cos x = cos(&1 * x) /\ sin x = sin(&1 * x)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "trigpoly" THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `a:num->real`; `b:num->real`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cexp(ii * Cx r)`) THEN
  REWRITE_TAC[NORM_CEXP_II] THEN MATCH_MP_TAC(REAL_ARITH
   `x = x' ==> abs(x - y) < e ==> abs(x' - y) < e`) THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_CASES_TAC `r = --pi` THENL
   [UNDISCH_THEN `r = --pi` SUBST_ALL_TAC THEN
    REWRITE_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN] THEN
    REWRITE_TAC[COS_NEG; SIN_NEG; SIN_PI; COS_PI] THEN
    REWRITE_TAC[CX_NEG; COMPLEX_MUL_RZERO; COMPLEX_NEG_0] THEN
    ASM_REWRITE_TAC[CLOG_NEG_1; COMPLEX_ADD_RID; IM_MUL_II; RE_CX];
    ASM_SIMP_TAC[CLOG_CEXP; IM_MUL_II; RE_CX; REAL_LT_LE]]);;
```

### Informal statement
Let $f$ be a real-valued continuous function on the interval $[-\pi, \pi]$ such that $f(-\pi) = f(\pi)$, and let $\varepsilon > 0$. Then there exist a natural number $n$ and sequences of real coefficients $(a_k)_{k=0}^n$ and $(b_k)_{k=0}^n$ such that for all $x \in [-\pi, \pi]$:

$$\left|f(x) - \sum_{k=0}^n (a_k \sin(kx) + b_k \cos(kx))\right| < \varepsilon$$

This theorem states that continuous periodic functions on $[-\pi, \pi]$ can be uniformly approximated by trigonometric polynomials to arbitrary precision.

### Informal proof
The proof follows several main steps:

1. **Extend the problem to the complex plane**:
   - We use the Stone-Weierstrass theorem on the unit circle in the complex plane.
   - First, we show that for a continuous function $f$ on $[-\pi,\pi]$ with $f(-\pi) = f(\pi)$, the composition $(f \circ \text{Im} \circ \text{clog})$ is real-continuous at any point on the unit circle.

2. **Establish a key lemma**:
   - Lemma 1 shows that if $f$ is real-continuous on all of $\mathbb{R}$ and $2\pi$-periodic (i.e., $f(x+2\pi) = f(x)$ for all $x$), then $(f \circ \text{Im} \circ \text{clog})$ is real-continuous at any point on the unit circle.
   - Lemma 2 extends this to functions continuous only on $[-\pi,\pi]$ with matching endpoints, using Tietze's extension theorem to create a periodic continuous extension.

3. **Apply Stone-Weierstrass**:
   - Define the set of polynomials in $\text{Re}$ and $\text{Im}$ of complex variables.
   - Use the Stone-Weierstrass theorem to show that these polynomials can uniformly approximate $(f \circ \text{Im} \circ \text{clog})$ on the unit circle.

4. **Translate back to trigonometric polynomials**:
   - Define the set of trigonometric polynomials as functions of the form $\sum_{k=0}^n (a_k \sin(kx) + b_k \cos(kx))$.
   - Show that:
     - Constants are trigonometric polynomials
     - Sums of trigonometric polynomials are trigonometric polynomials
     - Products of trigonometric polynomials are trigonometric polynomials
     - $\sin(kx)$ and $\cos(kx)$ are trigonometric polynomials

5. **Complete the approximation**:
   - Show that if $p$ is a polynomial in $\text{Re}$ and $\text{Im}$, then $p(\exp(ix))$ can be expressed as a trigonometric polynomial.
   - The approximating polynomial from Stone-Weierstrass, when evaluated at $\exp(ix)$, gives the desired trigonometric polynomial approximating $f(x)$.

The proof uses a number of trigonometric identities (product-to-sum formulas) to verify that the product of trigonometric polynomials is again a trigonometric polynomial, which is crucial for applying Stone-Weierstrass.

### Mathematical insight
This theorem is a specific case of the Weierstrass approximation theorem, specialized to periodic functions. It establishes that trigonometric polynomials are dense in the space of continuous periodic functions on $[-\pi,\pi]$ with respect to the uniform norm.

The result is fundamental to Fourier analysis, as it shows that continuous periodic functions can be approximated arbitrarily well by finite Fourier series. It provides the theoretical foundation for applications in signal processing, differential equations, and many other areas of mathematical physics.

The proof strategy - using the Stone-Weierstrass theorem on the unit circle and translating back to real functions - cleverly connects complex analysis, topology, and trigonometric series. This approach allows us to leverage the power of Stone-Weierstrass in the complex domain to prove results about real trigonometric approximation.

### Dependencies
- **Theorems**:
  - `STONE_WEIERSTRASS` - The Stone-Weierstrass approximation theorem
  - `REAL_TIETZE_PERIODIC_INTERVAL` - Extension theorem for periodic functions
  - Various theorems about continuity and complex analysis

### Porting notes
When porting this theorem to another system:
1. Ensure the target system has a well-developed theory of complex analysis, particularly for logarithms and exponentials on the complex plane
2. The Stone-Weierstrass theorem is essential and should be available or ported first
3. The proof makes extensive use of function composition and operations on real and complex functions, so ensure the target system has good support for these
4. Pay attention to the handling of periodic boundary conditions and function extensions

---

## REAL_INTEGRAL_TWEAK_ENDS

### REAL_INTEGRAL_TWEAK_ENDS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_TWEAK_ENDS = prove
 (`!a b d e.
        a < b /\ &0 < e
        ==> ?f. f real_continuous_on real_interval[a,b] /\
                f(a) = d /\ f(b) = &0 /\
                l2norm (real_interval[a,b]) f < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. if x <= a + inv(&n + &1)
             then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
        real_continuous_on real_interval[a,b]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `a < a + inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `a + inv(&n + &1) <= b` THENL
     [SUBGOAL_THEN
       `real_interval[a,b] = real_interval[a,a + inv(&n + &1)] UNION
                             real_interval[a + inv(&n + &1),b]`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_CASES THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST] THEN
      CONJ_TAC THENL
       [SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID];
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_CASES_TAC `x:real = a + inv(&n + &1)` THENL
         [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_RZERO];
          ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\x. ((&n + &1) * d) * ((a + inv(&n + &1)) - x)` THEN
      SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC
   (ISPECL [`\n x. (if x <= a + inv(&n + &1)
                    then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
                   pow 2`;
            `\x:real. if x = a then d pow 2 else &0`;
            `\x:real. (d:real) pow 2`;
            `real_interval[a,b]`]
        REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_POW] THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_ABS] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
      ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_ARITH `d * x <= d <=> &0 <= d * (&1 - x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      REWRITE_TAC[REAL_ARITH `&0 <= &1 - x * y <=> y * x <= &1`] THEN
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THENL
       [ASM_REWRITE_TAC[REAL_LE_ADDR; REAL_LE_INV_EQ;
                        REAL_ARITH `&0 <= &n + &1`] THEN
        REWRITE_TAC[REAL_ADD_SUB] THEN
        SIMP_TAC[REAL_FIELD `&0 < x ==> (x * d) * inv x = d`;
                 REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
        REWRITE_TAC[REALLIM_CONST];
        MATCH_MP_TAC REALLIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        MP_TAC(ISPEC `x - a:real` REAL_ARCH_INV) THEN
        DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        SUBGOAL_THEN `inv(&n + &1) <= inv(&N)` MP_TAC THENL
         [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    MP_TAC(ISPEC `b - a:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?n:num. N <= n /\ M <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `M + N:num` THEN ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    EXISTS_TAC `\x. if x <= a + inv(&n + &1)
                 then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(REAL_ARITH `&0 < &n + &1`) THEN
      SIMP_TAC[REAL_LE_ADDR; REAL_LT_INV_EQ; REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `inv(&n + &1) < b - a` MP_TAC THENL
        [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&M)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
       [ASM_MESON_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[l2norm; l2product] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `abs(i - l) < e ==> &0 <= i /\ l = &0 ==> i < e`)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_POS THEN
        ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_CONTINUOUS_ON_POW] THEN
        REWRITE_TAC[REAL_LE_POW_2];
        MP_TAC(ISPEC `real_interval[a,b]` REAL_INTEGRAL_0) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
        EXISTS_TAC `{a:real}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
        SIMP_TAC[IN_DIFF; IN_SING]]]]);;
```

### Informal statement
For any real numbers $a$, $b$, $d$, and $e$ where $a < b$ and $0 < e$, there exists a function $f$ such that:
1. $f$ is continuous on the interval $[a,b]$
2. $f(a) = d$ and $f(b) = 0$
3. The L²-norm of $f$ on the interval $[a,b]$ is less than $e$, i.e., $\|f\|_{L^2[a,b]} < e$

### Informal proof
We prove that for any $a < b$ and $e > 0$, we can find a continuous function $f$ on $[a,b]$ with $f(a) = d$, $f(b) = 0$, and $\|f\|_{L^2[a,b]} < e$.

The key idea is to construct a sequence of functions that are zero except on a small interval $[a, a+\frac{1}{n+1}]$, where they linearly decrease from $d$ to 0.

1. For each natural number $n$, we define:
   $$f_n(x) = \begin{cases}
   (n+1)d \cdot (a+\frac{1}{n+1}-x) & \text{if } x \leq a+\frac{1}{n+1} \\
   0 & \text{otherwise}
   \end{cases}$$

2. First, we prove that each $f_n$ is continuous on $[a,b]$:
   - We show that $a < a+\frac{1}{n+1}$ (obvious since $\frac{1}{n+1} > 0$)
   - We consider two cases:
     - If $a+\frac{1}{n+1} \leq b$, we split $[a,b]$ into $[a,a+\frac{1}{n+1}] \cup [a+\frac{1}{n+1},b]$
     - If $a+\frac{1}{n+1} > b$, then $f_n$ is just the linear function on all of $[a,b]$
   - In both cases, we verify that $f_n$ is continuous

3. We apply the dominated convergence theorem to show that $\int_{[a,b]} f_n^2$ converges to $\int_{[a,b]} g$, where:
   $$g(x) = \begin{cases}
   d^2 & \text{if } x = a \\
   0 & \text{otherwise}
   \end{cases}$$

4. We verify the conditions for the dominated convergence theorem:
   - Each $f_n^2$ is integrable because $f_n$ is continuous
   - The dominant function is the constant $d^2$, which is integrable
   - $|f_n(x)^2| \leq d^2$ for all $x \in [a,b]$
   - $f_n(x)^2$ converges to $g(x)$ for all $x \in [a,b]$

5. Since $g$ is zero except at a single point, its integral is zero. By the dominated convergence theorem, $\int_{[a,b]} f_n^2 \to 0$ as $n \to \infty$.

6. Therefore, we can find a sufficiently large $n$ such that:
   - $\int_{[a,b]} f_n^2 < e^2$
   - $\frac{1}{n+1} < b-a$ (ensuring $f_n(b) = 0$)

7. Taking $f = f_n$ for this value of $n$, we have:
   - $f$ is continuous on $[a,b]$
   - $f(a) = d$ (by construction)
   - $f(b) = 0$ (since $\frac{1}{n+1} < b-a$)
   - $\|f\|_{L^2[a,b]} = \sqrt{\int_{[a,b]} f^2} < e$

### Mathematical insight
This theorem demonstrates that we can construct a continuous function with specified values at the endpoints of an interval while keeping its L²-norm arbitrarily small. 

The key insight is to compress the non-zero part of the function into a very small interval near one endpoint. By making this interval sufficiently small, we can make the L²-norm arbitrarily small while maintaining continuity and the required endpoint values.

This result is useful in functional analysis and approximation theory, where we often need to construct functions with specific properties while controlling their norms. It shows that endpoint constraints and small L²-norm are compatible requirements.

### Dependencies
- `l2product`: defines the L² inner product of two functions $f$ and $g$ on a set $s$ as $\langle f,g \rangle_{L^2(s)} = \int_s f(x)g(x) \, dx$
- `l2norm`: defines the L² norm of a function $f$ on a set $s$ as $\|f\|_{L^2(s)} = \sqrt{\langle f,f \rangle_{L^2(s)}}$

### Porting notes
When porting to other systems:
1. The proof relies heavily on the dominated convergence theorem for real integrals, which should be available in most systems.
2. The construction involves creating a piecewise function with specific properties, so systems with good support for piecewise definitions would be helpful.
3. In systems like Lean or Coq, you might need to explicitly handle the measurability of the functions involved, which is implicit in HOL Light.

---

## SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS

### Name of formal statement
SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS = prove
 (`!f a b e.
        f square_integrable_on real_interval[a,b] /\ a < b /\ &0 < e
        ==> ?g. g real_continuous_on real_interval[a,b] /\
                g b = g a /\
                g square_integrable_on real_interval[a,b] /\
                l2norm (real_interval[a,b]) (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval[a,b]`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`a:real`; `b:real`; `(g:real->real) b - g a`; `e / &2`]
        REAL_INTEGRAL_TWEAK_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `h square_integrable_on real_interval[a,b]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE]; ALL_TAC] THEN
  EXISTS_TAC `\x. (g:real->real) x + h x` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQUARE_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH `f - (g + h):real = (f - g) + --h`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) L2NORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; SQUARE_INTEGRABLE_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH
     `y < e / &2 /\ z < e / &2 ==> x <= y + z ==> x < e`) THEN
    ASM_SIMP_TAC[L2NORM_NEG]]);;
```

### Informal statement
For any function $f$ that is square integrable on the real interval $[a,b]$ where $a < b$, and for any $\varepsilon > 0$, there exists a function $g$ such that:
1. $g$ is real continuous on the interval $[a,b]$
2. $g(b) = g(a)$ (the function has the same value at both endpoints)
3. $g$ is square integrable on the interval $[a,b]$
4. The L2-norm of the difference between $f$ and $g$ on the interval $[a,b]$ is less than $\varepsilon$, i.e., $\|f - g\|_2 < \varepsilon$

### Informal proof
We prove this by constructing $g$ as the sum of two functions:

1. First, we apply `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS` to $f$ on the interval $[a,b]$ with error bound $\frac{\varepsilon}{2}$. This gives us a continuous function $g$ such that $\|f - g\|_2 < \frac{\varepsilon}{2}$. However, $g$ may not satisfy the condition that $g(b) = g(a)$.

2. To fix the endpoint values, we use `REAL_INTEGRAL_TWEAK_ENDS` with $a$, $b$, $g(b) - g(a)$, and $\frac{\varepsilon}{2}$. This gives us a function $h$ that:
   - Is continuous on $[a,b]$
   - Satisfies $h(a) = g(b) - g(a)$ and $h(b) = 0$
   - Has L2-norm less than $\frac{\varepsilon}{2}$, i.e., $\|h\|_2 < \frac{\varepsilon}{2}$

3. We prove that $h$ is square integrable on $[a,b]$ using `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`.

4. We define our final approximation as $g(x) + h(x)$.

5. We verify that this function satisfies all required properties:
   - It is continuous on $[a,b]$ (using `REAL_CONTINUOUS_ON_ADD`)
   - At the endpoints: $(g+h)(b) = g(b) + h(b) = g(b) + 0 = g(b)$ and $(g+h)(a) = g(a) + h(a) = g(a) + (g(b) - g(a)) = g(b)$, so the values at endpoints are equal
   - It is square integrable on $[a,b]$ (using `SQUARE_INTEGRABLE_ADD`)

6. Finally, for the L2-norm bound:
   - We rewrite $f - (g + h) = (f - g) + (-h)$
   - By the triangle inequality for L2-norm (`L2NORM_TRIANGLE`): $\|f - (g + h)\|_2 ≤ \|f - g\|_2 + \|-h\|_2 = \|f - g\|_2 + \|h\|_2$
   - Since $\|f - g\|_2 < \frac{\varepsilon}{2}$ and $\|h\|_2 < \frac{\varepsilon}{2}$, we have $\|f - (g + h)\|_2 < \varepsilon$

### Mathematical insight
This theorem provides a strengthening of the `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS` result by adding a constraint that the approximating continuous function must have matching values at the endpoints of the interval.

This is important because functions with matching endpoint values can be extended to periodic functions, which is often required in Fourier analysis. The ability to approximate any square integrable function with a continuous function that has matching endpoints while controlling the L2 error enables many results in Fourier theory.

The construction shows that we can first get a general continuous approximation and then "fix" the endpoints by adding a small correction function that only affects the function near the boundary points. This technique of "tweaking" function values at endpoints while maintaining control over the L2-norm is a common approach in analysis.

### Dependencies
- **Square Integrability Theorems:**
  - `square_integrable_on`: Definition of square integrability
  - `SQUARE_INTEGRABLE_NEG`: Negation of square integrable function
  - `SQUARE_INTEGRABLE_ADD`: Sum of square integrable functions
  - `SQUARE_INTEGRABLE_SUB`: Difference of square integrable functions
  - `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`: Continuous functions are square integrable
  - `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS`: Approximation by continuous functions

- **L2 Norm Properties:**
  - `l2norm`: Definition of L2 norm
  - `L2NORM_TRIANGLE`: Triangle inequality for L2 norm
  - `L2NORM_NEG`: L2 norm of negation

- **Construction Theorems:**
  - `REAL_INTEGRAL_TWEAK_ENDS`: Creates a continuous function with specified endpoint values

### Porting notes
When porting this theorem:
1. Ensure you have properly defined the concept of square integrability and L2 norm.
2. The proof relies on creating a function with specific endpoint values via `REAL_INTEGRAL_TWEAK_ENDS`, which constructs a small continuous function with prescribed values. This construction might need to be reimplemented depending on the system.
3. The triangle inequality for L2 norms is essential for the error bound; ensure this is available.

---

## WEIERSTRASS_L2_TRIG_POLYNOMIAL

### Name of formal statement
WEIERSTRASS_L2_TRIG_POLYNOMIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WEIERSTRASS_L2_TRIG_POLYNOMIAL = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a b.
                l2norm (real_interval[--pi,pi])
                       (\x. f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `--pi < pi <=> &0 < pi`; PI_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real->real`; `e / &6`] WEIERSTRASS_TRIG_POLYNOMIAL) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `u:num->real`; `v:num->real`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  SUBGOAL_THEN
   `!n u v. (\x. sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
            square_integrable_on (real_interval[--pi,pi])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `l2norm (real_interval[--pi,pi]) (\x. f x - g x) +
              l2norm (real_interval[--pi,pi]) (\x. g x - sum(0..n)
                   (\k. u k * sin(&k * x) + v k * cos(&k * x)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) L2NORM_TRIANGLE o rand o snd) THEN
    REWRITE_TAC[REAL_ARITH `(f - g) + (g - h):real = f - h`] THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y <= e / &2 ==> x + y < e`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[l2norm; l2product; GSYM REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SUBGOAL_THEN
   `(\x. g x - sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
    square_integrable_on (real_interval[--pi,pi])`
  MP_TAC THENL [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB]; ALL_TAC] THEN
  REWRITE_TAC[square_integrable_on] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_POS; REAL_LE_POW_2] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral(real_interval[--pi,pi]) (\x. (e / &6) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN X_GEN_TAC `x:real` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> abs(x) <= abs e`) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `--pi <= pi <=> &0 <= pi`;
             PI_POS_LE] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any square-integrable function $f$ on the interval $[-\pi, \pi]$ and any positive real number $\varepsilon > 0$, there exist a natural number $n$ and sequences of real coefficients $a_0, a_1, \ldots, a_n$ and $b_0, b_1, \ldots, b_n$ such that the $L^2$-norm of the difference between $f$ and the trigonometric polynomial $\sum_{k=0}^n (a_k \sin(k x) + b_k \cos(k x))$ is less than $\varepsilon$. Formally:

$$\forall f,\varepsilon. f \text{ square_integrable_on } [-\pi,\pi] \land \varepsilon > 0 \Rightarrow \exists n,a,b. \|f - \sum_{k=0}^n (a_k \sin(kx) + b_k \cos(kx))\|_{L^2([-\pi,\pi])} < \varepsilon$$

where $\|f\|_{L^2([-\pi,\pi])}$ represents the $L^2$-norm of $f$ on $[-\pi,\pi]$, defined as $\sqrt{\int_{-\pi}^{\pi} f(x)^2 dx}$.

### Informal proof
We want to prove that any square-integrable function on $[-\pi,\pi]$ can be approximated by trigonometric polynomials in the $L^2$ norm. The proof proceeds as follows:

- Given a square-integrable function $f$ on $[-\pi,\pi]$ and $\varepsilon > 0$, we first apply `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS` with error bound $\varepsilon/2$ to find a continuous function $g$ on $[-\pi,\pi]$ such that:
  * $g$ is continuous on $[-\pi,\pi]$
  * $g(-\pi) = g(\pi)$ (the function values match at endpoints)
  * $g$ is square-integrable on $[-\pi,\pi]$
  * $\|f - g\|_{L^2([-\pi,\pi])} < \varepsilon/2$

- Next, we apply `WEIERSTRASS_TRIG_POLYNOMIAL` to $g$ with error bound $\varepsilon/6$ to find coefficients $u_k$ and $v_k$ such that for all $x \in [-\pi,\pi]$:
  * $|g(x) - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))| < \varepsilon/6$

- We then prove that trigonometric polynomials are square-integrable on $[-\pi,\pi]$ using `SQUARE_INTEGRABLE_SUM` and the fact that sine and cosine functions are differentiable, hence continuous, hence square-integrable.

- By the triangle inequality for $L^2$ norms (`L2NORM_TRIANGLE`), we have:
  $$\|f - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))\|_{L^2} \leq \|f - g\|_{L^2} + \|g - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))\|_{L^2}$$

- For the first term, we already know $\|f - g\|_{L^2} < \varepsilon/2$.

- For the second term, we estimate:
  $$\|g - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))\|_{L^2}^2 = \int_{-\pi}^{\pi} |g(x) - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))|^2 dx$$
  * Since $|g(x) - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))| < \varepsilon/6$ for all $x \in [-\pi,\pi]$, we have:
  $$\int_{-\pi}^{\pi} |g(x) - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))|^2 dx \leq \int_{-\pi}^{\pi} (\varepsilon/6)^2 dx = (\varepsilon/6)^2 \cdot 2\pi$$
  
- Using numerical bounds on $\pi$ (from `PI_APPROX_32`), we calculate $(\varepsilon/6)^2 \cdot 2\pi \leq (\varepsilon/2)^2$

- Taking square roots, we get $\|g - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))\|_{L^2} \leq \varepsilon/2$

- Therefore, $\|f - \sum_{k=0}^n (u_k \sin(kx) + v_k \cos(kx))\|_{L^2} < \varepsilon/2 + \varepsilon/2 = \varepsilon$

### Mathematical insight
This theorem extends the Weierstrass approximation theorem to the $L^2$ space context. While the classical Weierstrass theorem states that continuous functions on a closed interval can be uniformly approximated by polynomials, this result shows that square-integrable functions on $[-\pi,\pi]$ can be approximated in the $L^2$ norm by trigonometric polynomials.

The result is foundational in Fourier analysis, as it essentially states that trigonometric polynomials are dense in the space of square-integrable functions on $[-\pi,\pi]$. This is a key step toward showing that the Fourier series of a square-integrable function converges to the function in the $L^2$ norm.

The theorem has broad applications in signal processing, differential equations, and mathematical physics, where decomposing functions into their frequency components (via trigonometric or Fourier series) is a fundamental technique.

### Dependencies
- Definitions:
  - `square_integrable_on`: A function is square-integrable on a set if it is measurable on that set and its square is integrable
  - `l2product`: The inner product of two functions in $L^2$ space, defined as the integral of their product
  - `l2norm`: The $L^2$ norm of a function, defined as the square root of its inner product with itself

- Theorems:
  - `SQUARE_INTEGRABLE_SUB`: The difference of two square-integrable functions is square-integrable
  - `SQUARE_INTEGRABLE_SUM`: A finite sum of square-integrable functions is square-integrable
  - `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`: A continuous function on a closed interval is square-integrable
  - `L2NORM_TRIANGLE`: Triangle inequality for $L^2$ norms
  - `WEIERSTRASS_TRIG_POLYNOMIAL`: Any continuous function on $[-\pi,\pi]$ with matching endpoint values can be uniformly approximated by trigonometric polynomials
  - `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS`: Any square-integrable function can be approximated in $L^2$ norm by a continuous function with matching endpoint values

### Porting notes
When porting to other proof assistants:
1. The definition of square-integrability may vary across systems. Ensure your target system has an equivalent notion of measurable functions and integrability.
2. The theorem uses specific numerical bounds and arithmetic calculations when estimating the error. These calculations might need adjustment based on how the target system handles real number arithmetic.
3. The theorem relies on the existence and properties of trigonometric functions. Ensure your target system has appropriate definitions and properties of sine and cosine functions.
4. The L2 norm calculation depends on integration theory. Ensure your target system has compatible integration theory, especially for handling operations like integrals of bounded functions.

---

## WEIERSTRASS_L2_TRIGONOMETRIC_SET

### Name of formal statement
WEIERSTRASS_L2_TRIGONOMETRIC_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WEIERSTRASS_L2_TRIGONOMETRIC_SET = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a.
                l2norm (real_interval[--pi,pi])
                       (\x. f x -
                            sum(0..n) (\k. a k * trigonometric_set k x))
                < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WEIERSTRASS_L2_TRIG_POLYNOMIAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
  DISCH_TAC THEN EXISTS_TAC `2 * n + 1` THEN
  SUBST1_TAC(ARITH_RULE `0 = 2 * 0`) THEN
  REWRITE_TAC[SUM_PAIR; SUM_ADD_NUMSEG; trigonometric_set] THEN
  EXISTS_TAC
   `(\k. if k = 0 then sqrt(&2 * pi) * b 0
         else if EVEN k then sqrt pi * b(k DIV 2)
         else if k <= 2 * n then sqrt pi * a((k + 1) DIV 2)
         else &0):num->real` THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0; MULT_EQ_0] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LE_0; ARITH_RULE `2 * i <= 2 * n <=> i <= n`] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC[trigonometric_set; ARITH; LE_0] THEN
      MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * (SUC i) = 2 * i + 2`] THEN
      REWRITE_TAC[trigonometric_set;
                  ARITH_RULE `(2 * i + 2) DIV 2 = SUC i`] THEN
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]];
    REWRITE_TAC[ARITH_RULE `2 * i + 1 = 2 * (i + 1) - 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
    REWRITE_TAC[GSYM ADD1; ARITH; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ 2 * SUC n - 1 = 2 * n + 1`] THEN
    REWRITE_TAC[ARITH_RULE `~(2 * n + 1 <= 2 * n)`; REAL_MUL_LZERO] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_ADD_RID] THEN
    SIMP_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; ARITH] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> 2 * i - 1 <= 2 * n`] THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[ARITH_RULE `SUC(2 * SUC i - 1) DIV 2 = SUC i`] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_FIELD
     `&0 < s ==> (s * b) * c / s = b * c`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]]);;
```

### Informal statement
For any square-integrable function $f$ on the interval $[-\pi, \pi]$ and any positive real number $\varepsilon > 0$, there exists a non-negative integer $n$ and a sequence of coefficients $a_0, a_1, \ldots, a_n$ such that:

$$\|f - \sum_{k=0}^{n} a_k \cdot \text{trigonometric\_set}(k)\|_{L^2[-\pi,\pi]} < \varepsilon$$

where $\|\cdot\|_{L^2[-\pi,\pi]}$ represents the $L^2$ norm on the interval $[-\pi, \pi]$, and $\text{trigonometric\_set}$ is defined as:
- $\text{trigonometric\_set}(0)(x) = \cos(0 \cdot x) / \sqrt{2\pi}$
- $\text{trigonometric\_set}(2n+1)(x) = \sin((n+1) \cdot x) / \sqrt{\pi}$
- $\text{trigonometric\_set}(2n+2)(x) = \cos((n+1) \cdot x) / \sqrt{\pi}$

### Informal proof
The proof shows that the orthogonal functions from the trigonometric set can approximate any square-integrable function with arbitrary precision in the $L^2$ norm.

1. We begin by applying the theorem `WEIERSTRASS_L2_TRIG_POLYNOMIAL`, which states that for any square-integrable function $f$ and $\varepsilon > 0$, there exist $n$, $a$, and $b$ such that:
   $$\|f - \sum_{k=0}^{n} (a_k \sin(kx) + b_k \cos(kx))\|_{L^2[-\pi,\pi]} < \varepsilon$$

2. We need to convert this standard Fourier series into the form using the trigonometric set functions. We set our target $n$ to be $2n+1$ (where $n$ is from the previous theorem).

3. We define a new coefficient sequence:
   - $a(0) = \sqrt{2\pi} \cdot b(0)$ if $k = 0$
   - $a(k) = \sqrt{\pi} \cdot b(k/2)$ if $k$ is even
   - $a(k) = \sqrt{\pi} \cdot a((k+1)/2)$ if $k$ is odd and $k \leq 2n$
   - $a(k) = 0$ otherwise

4. We then prove that with these coefficients:
   $$\sum_{k=0}^{n} (a_k \sin(kx) + b_k \cos(kx)) = \sum_{k=0}^{2n+1} a_k \cdot \text{trigonometric\_set}(k)(x)$$

5. This involves carefully separating the sum into even and odd indices, applying the definition of trigonometric_set, and showing term-by-term equivalence:
   - For even terms $2i$, we show they correspond to cosine terms
   - For odd terms $2i+1$, we show they correspond to sine terms

6. Since the two expressions are equal, the $L^2$ norm of their difference from $f$ is the same, which proves the theorem.

### Mathematical insight
This theorem is a version of the Weierstrass approximation theorem for the $L^2$ space on $[-\pi,\pi]$. It shows that the trigonometric basis functions (properly normalized) form a complete orthonormal system in the $L^2$ space. This is the foundation of Fourier series theory, which states that a square-integrable function can be represented as an infinite sum of sines and cosines (or complex exponentials).

The significance of this theorem is that it uses the specifically normalized trigonometric functions defined in `trigonometric_set`, which makes them orthonormal with respect to the $L^2$ inner product. This particular normalization (division by $\sqrt{\pi}$ or $\sqrt{2\pi}$) ensures orthonormality, which is crucial for many applications in functional analysis and mathematical physics.

The theorem essentially provides the mathematical justification for approximating any square-integrable function to arbitrary precision using a finite linear combination of these basis functions.

### Dependencies
- **Theorems**:
  - `WEIERSTRASS_L2_TRIG_POLYNOMIAL`: The underlying trigonometric polynomial approximation theorem
  - `trigonometric_set`: Defines the specific orthonormal trigonometric basis

- **Definitions**:
  - `square_integrable_on`: $f$ is square integrable on $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$
  - `l2norm`: The $L^2$ norm defined as $\|f\|_{L^2} = \sqrt{\langle f,f \rangle_{L^2}}$

### Porting notes
When porting this theorem:
1. Ensure your target system has the correct definition of the trigonometric set with proper normalization factors ($\sqrt{\pi}$ and $\sqrt{2\pi}$).
2. The proof relies heavily on algebraic manipulations of indices and sums. Be careful with the handling of even/odd indices and division operations.
3. The $L^2$ norm definition may vary between systems, so ensure consistency in the definition.
4. The sum rearrangement and index manipulation may require different tactics in other proof assistants.
5. The proof uses the WEIERSTRASS_L2_TRIG_POLYNOMIAL theorem, so that would need to be ported first.

---

## fourier_coefficient

### Name of formal statement
fourier_coefficient

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let fourier_coefficient = new_definition
 `fourier_coefficient =
    orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`;;
```

### Informal statement
The Fourier coefficient is defined as:

$$\text{fourier\_coefficient} = \text{orthonormal\_coefficient}([-\pi, \pi], \text{trigonometric\_set})$$

This means that for a function $f$ and a natural number $n$, the $n$-th Fourier coefficient is the inner product (L2 product) of $f$ with the $n$-th function in the trigonometric basis set over the interval $[-\pi, \pi]$.

### Informal proof
This is a definition rather than a theorem, so there is no proof.

### Mathematical insight
Fourier coefficients are fundamental in Fourier analysis, allowing the decomposition of a periodic function into a sum of sine and cosine terms. The definition specifically establishes Fourier coefficients as inner products between a function and the orthonormal basis of trigonometric functions on $[-\pi, \pi]$.

The trigonometric set used in this definition consists of:
- $\text{trigonometric\_set}(0) = \frac{1}{\sqrt{2\pi}} \cos(0 \cdot x)$
- $\text{trigonometric\_set}(2n+1) = \frac{1}{\sqrt{\pi}} \sin((n+1) \cdot x)$
- $\text{trigonometric\_set}(2n+2) = \frac{1}{\sqrt{\pi}} \cos((n+1) \cdot x)$

These functions form an orthonormal basis for the Hilbert space of square-integrable functions on $[-\pi, \pi]$. Computing Fourier coefficients is the first step in constructing a Fourier series, which can approximate or exactly represent functions with suitable properties.

### Dependencies
- **Definitions**:
  - `orthonormal_coefficient`: Defines the inner product of a function with a member of an orthonormal basis
  - `trigonometric_set`: Defines the orthonormal trigonometric basis functions

### Porting notes
When porting to other proof assistants, ensure that:
1. The L2 inner product is properly defined for the interval $[-\pi, \pi]$
2. The trigonometric basis functions are normalized correctly (as shown in the dependency)
3. The interval $[-\pi, \pi]$ is properly represented in the target system's real number formalization

---

## FOURIER_SERIES_L2

### FOURIER_SERIES_L2
- fourier_series_l2

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2 = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> ((\n. l2norm (real_interval[--pi,pi])
                        (\x. f(x) - sum(0..n) (\i. fourier_coefficient f i *
                                                   trigonometric_set i x)))
            ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `e:real`]
    WEIERSTRASS_L2_TRIGONOMETRIC_SET) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:num->real` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fourier_coefficient] THEN MP_TAC(ISPECL
   [`real_interval[--pi,pi]`; `trigonometric_set`;
    `(\i. if i <= n then a i else &0):num->real`;
    `f:real->real`; `0..m`]
    ORTHONORMAL_OPTIMAL_PARTIAL_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                  SQUARE_INTEGRABLE_TRIGONOMETRIC_SET; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a < e ==> x <= a ==> abs x < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC L2NORM_POS_LE THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_LMUL THEN
    REWRITE_TAC[ETA_AX; SQUARE_INTEGRABLE_TRIGONOMETRIC_SET];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_0] THEN
    SIMP_TAC[IN_NUMSEG; REAL_MUL_LZERO; LE_0]]);;
```

### Informal statement
For any function $f$ that is square integrable on the interval $[-\pi,\pi]$, the sequence of $L^2$ norms of the difference between $f$ and its partial Fourier series converges to $0$. Formally:

$$\forall f. \text{ If } f \text{ is square integrable on } [-\pi,\pi], \text{ then } \lim_{n \to \infty} \|f - \sum_{i=0}^{n} c_i \cdot \phi_i\|_{L^2} = 0$$

where:
- $c_i = \text{fourier\_coefficient}(f, i)$ are the Fourier coefficients of $f$
- $\phi_i = \text{trigonometric\_set}(i)$ are the trigonometric basis functions
- $\|\cdot\|_{L^2}$ denotes the $L^2$ norm on the interval $[-\pi,\pi]$

### Informal proof
We need to show that for any $\varepsilon > 0$, there exists an $N$ such that for all $n \geq N$, the $L^2$ norm of the difference between $f$ and its partial Fourier series up to $n$ terms is less than $\varepsilon$.

1. We begin by applying the Weierstrass L2 approximation theorem for trigonometric polynomials (`WEIERSTRASS_L2_TRIGONOMETRIC_SET`), which states that for any square-integrable function on $[-\pi,\pi]$ and any $\varepsilon > 0$, there exists a trigonometric polynomial that approximates $f$ with an $L^2$ error less than $\varepsilon$.

2. This gives us an $n$ and coefficients $a_i$ such that:
   $$\|f - \sum_{i=0}^{n} a_i \cdot \phi_i\|_{L^2} < \varepsilon$$

3. Next, we use the optimality property of Fourier coefficients (`ORTHONORMAL_OPTIMAL_PARTIAL_SUM`): given an orthonormal system, the partial sum of the function using the orthonormal coefficients minimizes the $L^2$ distance among all possible choices of coefficients.

4. We apply this to our case with:
   - The orthonormal system is `trigonometric_set` on the interval $[-\pi,\pi]$
   - We compare our Fourier coefficients with the coefficients $a_i$ we obtained from the Weierstrass approximation
   - For indices beyond $n$, we set $a_i = 0$

5. This gives us that for all $m \geq n$:
   $$\|f - \sum_{i=0}^{m} c_i \cdot \phi_i\|_{L^2} \leq \|f - \sum_{i=0}^{m} a_i \cdot \phi_i\|_{L^2}$$

6. Since $a_i = 0$ for $i > n$, we have:
   $$\|f - \sum_{i=0}^{m} a_i \cdot \phi_i\|_{L^2} = \|f - \sum_{i=0}^{n} a_i \cdot \phi_i\|_{L^2} < \varepsilon$$

7. We verify that the expressions involved are square integrable using the appropriate lemmas (`SQUARE_INTEGRABLE_SUB`, `SQUARE_INTEGRABLE_SUM`, and `SQUARE_INTEGRABLE_LMUL`).

8. Therefore, for any $m \geq n$:
   $$\|f - \sum_{i=0}^{m} c_i \cdot \phi_i\|_{L^2} < \varepsilon$$

9. This proves that the sequence of partial Fourier series converges to $f$ in the $L^2$ norm.

### Mathematical insight
This theorem establishes the completeness of the trigonometric system in $L^2([-\pi,\pi])$. It is a fundamental result in Fourier analysis, showing that any square-integrable function on $[-\pi,\pi]$ can be approximated arbitrarily well (in the $L^2$ sense) by a finite Fourier series.

The result also has significant practical implications:
1. It justifies the use of Fourier series for representing and approximating periodic functions in applications.
2. It provides a theoretical foundation for numerical methods based on Fourier approximations.
3. It connects to broader mathematical theories like functional analysis and the theory of orthogonal expansions.

The proof combines the Weierstrass approximation theorem with the optimality property of orthonormal expansions, illustrating how these fundamental results work together in Fourier analysis.

### Dependencies
- Definitions:
  - `square_integrable_on`: A function is square integrable if it is measurable and its square is integrable
  - `l2norm`: The L2 norm defined as the square root of the L2 inner product of a function with itself
  - `fourier_coefficient`: Defined as the orthonormal coefficient of the trigonometric set on $[-\pi,\pi]$

- Theorems:
  - `SQUARE_INTEGRABLE_LMUL`: Scalar multiplication preserves square integrability
  - `SQUARE_INTEGRABLE_SUB`: Subtraction preserves square integrability
  - `SQUARE_INTEGRABLE_SUM`: Finite sum of square integrable functions is square integrable
  - `L2NORM_POS_LE`: L2 norm is non-negative
  - `ORTHONORMAL_OPTIMAL_PARTIAL_SUM`: Optimality of partial sums using orthonormal coefficients
  - `ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET`: The trigonometric system forms an orthonormal system
  - `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`: Elements of the trigonometric set are square integrable
  - `WEIERSTRASS_L2_TRIGONOMETRIC_SET`: Weierstrass approximation theorem for L2 functions

### Porting notes
When porting this theorem:
1. Ensure that the appropriate definitions of square integrability, L2 norm, and Fourier coefficients are in place.
2. The concept of an orthonormal system and the optimality of orthonormal expansions must be established.
3. The trigonometric basis functions and their orthonormality properties will need special attention.
4. The Weierstrass approximation theorem for the L2 space is crucial and may need to be proven separately if not available.
5. In some systems, the handling of the sequence convergence (`---> &0 sequentially`) may require different notation or approach.

---

## TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE

### TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE
- Theorem name: `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; real_div] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all functions $f$ and natural numbers $n$, if $f$ is absolutely real integrable on the real interval $[-\pi, \pi]$, then the product function $x \mapsto \text{trigonometric\_set}(n, x) \cdot f(x)$ is also absolutely real integrable on the real interval $[-\pi, \pi]$.

Here, $\text{trigonometric\_set}(n, x)$ represents the normalized Fourier basis functions defined as:
- $\text{trigonometric\_set}(0, x) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}} = \frac{1}{\sqrt{2\pi}}$
- $\text{trigonometric\_set}(2n+1, x) = \frac{\sin((n+1) \cdot x)}{\sqrt{\pi}}$
- $\text{trigonometric\_set}(2n+2, x) = \frac{\cos((n+1) \cdot x)}{\sqrt{\pi}}$

### Informal proof
The proof applies the theorem for absolute integrability of a product of a bounded measurable function with an absolutely integrable function.

We need to establish two things:
1. The trigonometric basis function $\text{trigonometric\_set}(n, x)$ is real measurable on $[-\pi, \pi]$.
2. The trigonometric basis function $\text{trigonometric\_set}(n, x)$ is bounded.

For the first part:
* We show that $\text{trigonometric\_set}(n, x)$ is measurable by proving it is continuous, which follows from differentiability.
* We use induction on $n$ considering the three cases (0, odd, and even) separately.
* For each case, the function involves $\sin$ or $\cos$ divided by a constant, which are differentiable, hence continuous, thus measurable.

For the second part:
* We prove that $|\text{trigonometric\_set}(n, x)| \leq 1$ for all $x$ and all $n$.
* Again using induction on $n$ with the three cases:
  * For $n = 0$: $|\frac{\cos(0)}{\sqrt{2\pi}}| = \frac{1}{\sqrt{2\pi}} \leq 1$ since $\sqrt{2\pi} > 1$
  * For $n = 2k+1$: $|\frac{\sin((k+1)x)}{\sqrt{\pi}}| \leq \frac{1}{\sqrt{\pi}}$ because $|\sin| \leq 1$
  * For $n = 2k+2$: $|\frac{\cos((k+1)x)}{\sqrt{\pi}}| \leq \frac{1}{\sqrt{\pi}}$ because $|\cos| \leq 1$
* Since $\pi > 1$, we have $\frac{1}{\sqrt{\pi}} < 1$, which completes the bound.

Since $\text{trigonometric\_set}(n, x)$ is both measurable and bounded, and $f$ is absolutely integrable, their product is absolutely integrable.

### Mathematical insight
This theorem establishes that Fourier coefficients are well-defined for absolutely integrable functions. The Fourier coefficient of $f$ corresponding to basis function $\text{trigonometric\_set}(n, x)$ is computed by integrating their product.

This is an important prerequisite for the Riemann-Lebesgue lemma (mentioned in the comment), which states that Fourier coefficients of integrable functions approach zero as the frequency increases. The theorem ensures these integrals exist and are finite.

The orthonormal basis functions $\text{trigonometric\_set}(n, x)$ are specifically normalized to have unit norm in $L^2[-\pi, \pi]$, which is important for the theory of Fourier series.

### Dependencies
- `trigonometric_set`: Defines the normalized Fourier basis functions
- `ODD_EVEN_INDUCT_LEMMA`: Lemma for induction with separate cases for even and odd numbers
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`: (Not shown in dependencies but used) States that product of bounded measurable function and absolutely integrable function is absolutely integrable

### Porting notes
- The proof relies on HOL Light's automation for differentiability (`REAL_DIFFERENTIABLE_TAC`), which may need different tactics in other systems.
- Care should be taken with the definition of `trigonometric_set` to ensure the normalization factors are preserved exactly.
- The proof uses a specific approximation of π (via `PI_APPROX_32`) to show that $\frac{1}{\sqrt{\pi}} < 1$, which might be handled differently in other proof assistants.

---

## TRIGONOMETRIC_SET_MUL_INTEGRABLE

### TRIGONOMETRIC_SET_MUL_INTEGRABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_MUL_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             real_integrable_on real_interval[--pi,pi]`,
  SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE]);;
```

### Informal statement
For any function $f$ and natural number $n$, if $f$ is absolutely integrable on the real interval $[-\pi, \pi]$, then the product of $f$ and the $n$-th trigonometric basis function $\text{trigonometric\_set}\ n$ is integrable on $[-\pi, \pi]$. Formally:

$$\forall f, n.\ f \text{ absolutely real integrable on } [-\pi, \pi] \Rightarrow (\lambda x.\ \text{trigonometric\_set}\ n\ x \cdot f(x)) \text{ real integrable on } [-\pi, \pi]$$

### Informal proof
The proof follows immediately from two facts:
- If a function is absolutely integrable, then it is integrable
- The product of $f$ with the $n$-th trigonometric basis function is absolutely integrable (by theorem `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`)

The proof simply applies these two theorems using the simplification tactic.

### Mathematical insight
This theorem is a key component in Fourier analysis, establishing that when working with functions that are absolutely integrable on $[-\pi, \pi]$, we can form products with the trigonometric basis functions (sines and cosines) and these products remain integrable. This property is essential for defining Fourier coefficients and developing Fourier series expansions.

The trigonometric basis functions are defined as:
- $\text{trigonometric\_set}\ 0(x) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}} = \frac{1}{\sqrt{2\pi}}$
- $\text{trigonometric\_set}\ (2n+1)(x) = \frac{\sin((n+1)x)}{\sqrt{\pi}}$
- $\text{trigonometric\_set}\ (2n+2)(x) = \frac{\cos((n+1)x)}{\sqrt{\pi}}$

This theorem ensures we can integrate against these basis functions when computing Fourier coefficients.

### Dependencies
- Theorems:
  - `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`: Shows that absolute integrability implies integrability
  - `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`: Shows that the product of a function with a trigonometric basis function is absolutely integrable
  - `trigonometric_set`: Defines the trigonometric basis functions

### Porting notes
When porting this theorem, ensure that the definitions of trigonometric basis functions match exactly, particularly regarding the normalization factors of $\sqrt{\pi}$ and $\sqrt{2\pi}$. These normalization factors ensure orthonormality of the basis, which is crucial for Fourier analysis.

---

## ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT

### Name of formal statement
ABSOLUTELY_INTEGRABLE_SIN_PRODUCT, ABSOLUTELY_INTEGRABLE_COS_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT =
 (CONJ_PAIR o prove)
 (`(!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. sin(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi]) /\
   (!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. cos(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
     MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
     MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
     REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; real_div] THEN
     REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
     REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; COS_BOUND; SIN_BOUND]]));;
```

### Informal statement
This theorem consists of two parts:

1. For any real function $f$ and number $k$, if $f$ is absolutely integrable on the interval $[-\pi, \pi]$, then the function $x \mapsto \sin(kx) \cdot f(x)$ is also absolutely integrable on $[-\pi, \pi]$.

2. For any real function $f$ and number $k$, if $f$ is absolutely integrable on the interval $[-\pi, \pi]$, then the function $x \mapsto \cos(kx) \cdot f(x)$ is also absolutely integrable on $[-\pi, \pi]$.

### Informal proof
The proof is the same for both parts and proceeds as follows:

We apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`, which states that the product of an absolutely integrable function with a bounded measurable function is absolutely integrable. Since we already know that $f$ is absolutely integrable, we need to show that:

1. The trigonometric functions $\sin(kx)$ and $\cos(kx)$ are measurable on $[-\pi, \pi]$
2. These trigonometric functions are bounded

For the measurability part:
- We show that the trigonometric functions are measurable on $\mathbb{R}$ (not just on $[-\pi, \pi]$)
- We do this by proving they are continuous, which follows from them being differentiable
- To prove differentiability, we use the `ODD_EVEN_INDUCT_LEMMA` to perform induction
- We use the properties of the trigonometric functions from `trigonometric_set`
- Finally, we apply `REAL_DIFFERENTIABLE_TAC` to complete the differentiability proof

For the boundedness part:
- We show that both $\sin(kx)$ and $\cos(kx)$ are bounded by 1
- Again using `ODD_EVEN_INDUCT_LEMMA` for case analysis
- And applying the standard bounds `SIN_BOUND` and `COS_BOUND` which state that $|\sin(x)| \leq 1$ and $|\cos(x)| \leq 1$ for all $x$

### Mathematical insight
This theorem is important for Fourier analysis, where we often need to integrate products of functions with sines and cosines. It ensures that when working with absolutely integrable functions on $[-\pi, \pi]$, multiplying them by sine or cosine terms preserves absolute integrability.

This result is a fundamental building block for proving the existence of Fourier coefficients for absolutely integrable functions. It's essential because it guarantees that when decomposing functions into Fourier series, the integrals used to compute the Fourier coefficients actually exist.

### Dependencies
- `ODD_EVEN_INDUCT_LEMMA`: A lemma for induction on numbers classified as 0, odd, or even.
- `trigonometric_set`: Definitions of trigonometric functions.
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`: Theorem stating that the product of an absolutely integrable function and a bounded measurable function is absolutely integrable.
- `REAL_MEASURABLE_ON_MEASURABLE_SUBSET`: Property of measurable functions on subsets.
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`: Continuous functions are measurable.
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`: Differentiable functions are continuous.
- `SIN_BOUND`, `COS_BOUND`: Bounds on sine and cosine functions.

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-developed theory of measurability and absolute integrability.
2. The proof relies on differentiability implying measurability, which might require different tactics in other systems.
3. The odd/even induction pattern might need to be implemented differently depending on the system's induction tactics.
4. Check that the boundedness of sine and cosine functions is already established in the target system.

---

## FOURIER_PRODUCTS_INTEGRABLE_STRONG

### FOURIER_PRODUCTS_INTEGRABLE_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_PRODUCTS_INTEGRABLE_STRONG = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
           ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```

### Informal statement
For all real-valued functions $f$ that are absolutely integrable on the interval $[-\pi, \pi]$, the following statements hold:
- $f$ is integrable on $[-\pi, \pi]$
- For all $k$, the function $x \mapsto \cos(kx) \cdot f(x)$ is integrable on $[-\pi, \pi]$
- For all $k$, the function $x \mapsto \sin(kx) \cdot f(x)$ is integrable on $[-\pi, \pi]$

### Informal proof
This theorem follows directly from applying three results from the theory of integrability:

- First, we know that an absolutely integrable function is also integrable, which addresses the first claim about $f$ being integrable on $[-\pi, \pi]$.

- For the second claim, we use the fact that if $f$ is absolutely integrable on $[-\pi, \pi]$, then the product of $f$ with $\cos(kx)$ is integrable on that interval for any $k$.

- Similarly, for the third claim, we use the fact that if $f$ is absolutely integrable on $[-\pi, \pi]$, then the product of $f$ with $\sin(kx)$ is integrable on that interval for any $k$.

The theorem follows by applying these three facts using simplification tactics.

### Mathematical insight
This theorem is a foundational result for Fourier analysis. It ensures that when calculating Fourier coefficients of an absolutely integrable function, all the relevant integrals involving products with sin and cosine terms are well-defined.

The result is stronger than might initially appear - it guarantees integrability of the product functions for all frequencies $k$, not just for specific values. This provides the mathematical basis for representing a function as an infinite Fourier series.

Absolute integrability is a sufficient condition that ensures the existence of all the integrals needed for Fourier analysis. This theorem establishes that we can safely work with the products of an absolutely integrable function with the trigonometric basis functions.

### Dependencies
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`: Ensures that the product of an absolutely integrable function and sine is integrable
- `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`: Ensures that the product of an absolutely integrable function and cosine is integrable
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`: States that absolute integrability implies integrability

### Porting notes
When porting this theorem:
- Ensure that the notion of absolute integrability in the target system matches HOL Light's definition
- Check how the target system handles products of functions, particularly when one factor is a trigonometric function
- The proof is straightforward by applying the three dependencies, so an analogous simplification approach should work in most systems

---

## FOURIER_PRODUCTS_INTEGRABLE

### FOURIER_PRODUCTS_INTEGRABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_PRODUCTS_INTEGRABLE = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FOURIER_PRODUCTS_INTEGRABLE_STRONG THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_REAL_INTERVAL;
               SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE]);;
```

### Informal statement
For any function $f$, if $f$ is square integrable on the real interval $[-\pi, \pi]$ (i.e., $f$ is real measurable and $f^2$ is real integrable on this interval), then:
- $f$ is real integrable on $[-\pi, \pi]$
- For all $k$, the function $x \mapsto \cos(k \cdot x) \cdot f(x)$ is real integrable on $[-\pi, \pi]$
- For all $k$, the function $x \mapsto \sin(k \cdot x) \cdot f(x)$ is real integrable on $[-\pi, \pi]$

### Informal proof
The proof follows from two key facts:
1. Square integrable functions on a measurable set are absolutely integrable (by the theorem `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`)
2. Absolutely integrable functions on $[-\pi, \pi]$ satisfy the desired properties (by the theorem `FOURIER_PRODUCTS_INTEGRABLE_STRONG`)

Specifically:
- Given that $f$ is square integrable on $[-\pi, \pi]$
- We know that $[-\pi, \pi]$ is real measurable (using `REAL_MEASURABLE_REAL_INTERVAL`)
- Therefore, $f$ is absolutely real integrable on $[-\pi, \pi]$ (by `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`)
- From `FOURIER_PRODUCTS_INTEGRABLE_STRONG`, we conclude that:
  - $f$ is real integrable on $[-\pi, \pi]$
  - For all $k$, $\cos(k \cdot x) \cdot f(x)$ is real integrable on $[-\pi, \pi]$
  - For all $k$, $\sin(k \cdot x) \cdot f(x)$ is real integrable on $[-\pi, \pi]$

### Mathematical insight
This theorem is important for Fourier analysis as it establishes the integrability of products of trigonometric functions with square integrable functions. This is a fundamental requirement for defining Fourier coefficients, as they involve integrals of precisely such products.

The result gives us a sufficient condition (square integrability) for ensuring that a function and its products with the Fourier basis functions are all integrable. Square integrability is a convenient condition to work with in many applications, and this theorem allows us to smoothly transition between different classes of functions in Fourier theory.

### Dependencies
- **Theorems**:
  - `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`: If a function is square integrable on a real measurable set, then it is absolutely real integrable on that set
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: If a function is absolutely real integrable on $[-\pi, \pi]$, then it and its products with sines and cosines are real integrable on that interval
  - `REAL_MEASURABLE_REAL_INTERVAL` (implied): Real intervals are real measurable sets

- **Definitions**:
  - `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is real measurable on $s$ and $f^2$ is real integrable on $s$

### Porting notes
When porting this theorem:
1. Ensure that your target system has appropriate notions of square integrability, absolute integrability, and measurability
2. The proof is quite direct, relying mostly on basic properties of these integration concepts
3. The square integrability condition might be represented differently in other systems (e.g., as membership in $L^2$ space)

---

## ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Name of formal statement
ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f absolutely_real_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g absolutely_real_integrable_on s /\
                   real_integral s (\x. abs(f x - g x)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&1:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LSPACE_1; GSYM ABSOLUTELY_REAL_INTEGRABLE_ON; REAL_OF_NUM_LE;
                  ARITH; GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[lnorm; REAL_INV_1; RPOW_POW; REAL_POW_1] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `(\x. f x - (drop o g o lift) x) absolutely_real_integrable_on s`
      MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_real_integrable_on]] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ETA_AX];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[o_DEF; NORM_LIFT; LIFT_DROP; NORM_REAL; GSYM drop;
                  DROP_SUB; LIFT_SUB]]]);;
```

### Informal statement
For any real-valued function $f$ on the real line, any measurable set $s \subseteq \mathbb{R}$, and any positive real number $e > 0$, if $f$ is absolutely integrable on $s$, then there exists a continuous function $g$ on the entire real line such that:
1. $g$ is absolutely integrable on $s$
2. $\int_s |f(x) - g(x)| \, dx < e$

### Informal proof
We approach this by lifting the problem to vector spaces and applying a more general result.

* Given a real-valued function $f$, measurable set $s$, and $e > 0$ with $f$ absolutely integrable on $s$
* We apply the theorem `LSPACE_APPROXIMATE_CONTINUOUS` to the lifted function $\operatorname{lift} \circ f \circ \operatorname{drop}$ on the set $\operatorname{IMAGE} \operatorname{lift} s$ with $p = 1$ and the given $e$
* Note that $\operatorname{lift}$ maps real numbers to $\mathbb{R}^1$ and $\operatorname{drop}$ does the reverse
* The application is valid because:
  * $p = 1 \geq 1$
  * $s$ being measurable implies $\operatorname{IMAGE} \operatorname{lift} s$ is measurable
  * $f$ being absolutely integrable on $s$ is equivalent to $\operatorname{lift} \circ f \circ \operatorname{drop} \in \operatorname{lspace} (\operatorname{IMAGE} \operatorname{lift} s) 1$ (by `LSPACE_1`)
* This gives us a function $g: \mathbb{R}^1 \to \mathbb{R}^1$ that is continuous on $\mathbb{R}^1$, in $\operatorname{lspace} (\operatorname{IMAGE} \operatorname{lift} s) 1$, and with $\operatorname{lnorm} (\operatorname{IMAGE} \operatorname{lift} s) 1 (\lambda x. (\operatorname{lift} \circ f \circ \operatorname{drop})(x) - g(x)) < e$
* We define our desired function as $\operatorname{drop} \circ g \circ \operatorname{lift}$
* This function is continuous on $\mathbb{R}$ (using the definition of real continuity via lifted functions)
* It is absolutely integrable on $s$ (following from $g$ being in the $L^1$ space)
* Finally, we show that $\int_s |f(x) - (\operatorname{drop} \circ g \circ \operatorname{lift})(x)| \, dx < e$ by:
  * Showing this integral equals the $L^1$ norm of the difference in the lifted space
  * Using properties of absolute integrability for differences of functions
  * Applying the integral equivalence between the real and lifted representations

### Mathematical insight
This theorem is a density result showing that continuous functions are dense in the space of absolutely integrable functions with respect to the $L^1$ norm. This is a fundamental approximation result in measure and integration theory.

The approximation property means that for any absolutely integrable function, we can find a continuous function that is arbitrarily close to it in the $L^1$ sense. This provides a bridge between the well-behaved continuous functions and the more general class of integrable functions.

This result is particularly important because:
1. It allows us to extend results from continuous functions to absolutely integrable functions
2. It justifies certain numerical approximation methods in analysis
3. It's part of a broader theme in functional analysis where "nice" functions (continuous, smooth, etc.) are dense in various function spaces

### Dependencies
- Theorems:
  - `LSPACE_1`: Establishes that a function is in the $L^1$ space if and only if it is absolutely integrable
  - `LSPACE_APPROXIMATE_CONTINUOUS`: The more general approximation result for $L^p$ spaces with $p \geq 1$
- Definitions:
  - `lnorm`: Defines the $L^p$ norm of a function

### Porting notes
When porting this theorem:
1. Pay attention to the handling of real vs. vector-valued functions - HOL Light uses lifting and dropping between $\mathbb{R}$ and $\mathbb{R}^1$
2. The proof relies on the more general $L^p$ approximation result, so that should be ported first
3. Ensure that the target system's notion of absolute integrability aligns with HOL Light's definition

---

## RIEMANN_LEBESGUE_SQUARE_INTEGRABLE

### RIEMANN_LEBESGUE_SQUARE_INTEGRABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SQUARE_INTEGRABLE = prove
 (`!s w f.
        orthonormal_system s w /\
        (!i. w i square_integrable_on s) /\
        f square_integrable_on s
        ==> (orthonormal_coefficient s w f ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(:num)` o
    MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMMABLE_IMP_TOZERO) THEN
  SIMP_TAC[IN_UNIV; REALLIM_NULL_POW_EQ; ARITH; ETA_AX]);;
```

### Informal statement
For any set $s$, orthonormal system $w$, and function $f$, if:
1. $w$ forms an orthonormal system on $s$,
2. For all indices $i$, the function $w(i)$ is square integrable on $s$,
3. The function $f$ is square integrable on $s$,

then the sequence of orthonormal coefficients $\langle f, w(n) \rangle$ tends to zero as $n$ approaches infinity.

Formally, $(orthonormal\_coefficient~s~w~f \to 0)$ sequentially.

### Informal proof
This theorem is a version of the Riemann-Lebesgue lemma for square integrable functions. The proof proceeds as follows:

1. We begin with the premise that $w$ is an orthonormal system on $s$, each $w(i)$ is square integrable on $s$, and $f$ is square integrable on $s$.

2. We apply the theorem `FOURIER_SERIES_SQUARE_SUMMABLE` with the full set of natural numbers $\mathbb{N}$ (represented as `(:num)` in HOL Light).
   - This theorem states that under our assumptions, the series $\sum_{i \in \mathbb{N}} (orthonormal\_coefficient~s~w~f~i)^2$ is summable.

3. Since the series $\sum_{i=0}^{\infty} |c_i|^2$ is summable (where $c_i = orthonormal\_coefficient~s~w~f~i$), we can apply the result that for any summable series of non-negative terms, the general term must approach zero.

4. This is formalized using `REAL_SUMMABLE_IMP_TOZERO`, which states that if a sequence of squares is summable, then the sequence itself must converge to zero.

5. After simplification using `REALLIM_NULL_POW_EQ`, we conclude that $(orthonormal\_coefficient~s~w~f \to 0)$ sequentially, which is precisely the Riemann-Lebesgue lemma for square integrable functions.

### Mathematical insight
This theorem is a form of the Riemann-Lebesgue lemma, which is fundamental in Fourier analysis. It states that the Fourier coefficients of a square integrable function tend to zero as the frequency increases. 

The result is intuitive: if a function $f$ is square integrable, its energy (measured by $\|f\|_2^2$) is finite. Since the coefficients in an orthonormal expansion represent how much "energy" or "information" is contained at each frequency, and the total energy is finite, the contribution from higher frequencies must eventually diminish to zero.

This theorem has important applications in various areas:
- In signal processing, it implies that higher-frequency components of a finite-energy signal become negligible.
- In quantum mechanics, it relates to the decay of probability amplitude for high-energy states.
- In approximation theory, it helps establish convergence rates for orthogonal expansions.

### Dependencies
- **Theorems:**
  - `FOURIER_SERIES_SQUARE_SUMMABLE`: Shows that the squares of orthonormal coefficients form a summable series when $f$ is square integrable
  - `REAL_SUMMABLE_IMP_TOZERO`: States that if a sequence of squares is summable, the sequence itself tends to zero

- **Definitions:**
  - `square_integrable_on`: A function $f$ is square integrable on a set $s$ if $f$ is measurable on $s$ and $f^2$ is integrable on $s$
  - `orthonormal_system`: A system of functions $w$ is orthonormal on $s$ if the L2-product of any two functions equals 1 when they're the same and 0 otherwise
  - `orthonormal_coefficient`: The inner product $\langle w(n), f \rangle$ in the L2 space

### Porting notes
When porting this theorem:
1. Ensure your system has a suitable representation for orthonormal systems and L2 spaces.
2. The concept of "square integrable functions" should be defined precisely, potentially requiring Lebesgue integration theory.
3. The theorem relies on Bessel's inequality (through `FOURIER_SERIES_SQUARE_SUMMABLE`), so this or an equivalent will need to be available.
4. The key insight that summability of squares implies convergence to zero of the sequence is a standard result that should be available in most libraries.

---

## RIEMANN_LEBESGUE

### RIEMANN_LEBESGUE
- Riemann-Lebesgue lemma

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> (fourier_coefficient f ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real->real`; `real_interval[--pi,pi]`; `e / &2`]
   ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL;
               LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_interval[--pi,pi]`; `trigonometric_set`; `g:real->real`]
        RIEMANN_LEBESGUE_SQUARE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                SQUARE_INTEGRABLE_TRIGONOMETRIC_SET] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `N:num <= n` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 ==> abs(y - z) <= x ==> y < e / &2 ==> z < e`)) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y) <= r ==> abs(abs x - abs y) <= r`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE];
    SUBGOAL_THEN `(\x. (f:real->real) x - g x) absolutely_real_integrable_on
                  real_interval[--pi,pi]`
    MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB]; ALL_TAC] THEN
    SIMP_TAC[absolutely_real_integrable_on];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SUB] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```

### Informal statement
The Riemann-Lebesgue lemma states that for any absolutely integrable function $f$ on the interval $[-\pi, \pi]$, the Fourier coefficients of $f$ tend to zero as the frequency increases:

$$\forall f. \; f \text{ absolutely integrable on } [-\pi, \pi] \Rightarrow \lim_{n \to \infty} \hat{f}(n) = 0$$

where $\hat{f}(n)$ denotes the $n$-th Fourier coefficient of $f$.

### Informal proof
The proof proceeds as follows:

1. Given an absolutely integrable function $f$ on $[-\pi, \pi]$, and any $\varepsilon > 0$, we need to show that the Fourier coefficients eventually become smaller than $\varepsilon$.

2. By the theorem `ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS`, we can approximate $f$ with a continuous function $g$ such that:
   $$\int_{-\pi}^{\pi} |f(x) - g(x)| \, dx < \frac{\varepsilon}{2}$$

3. Since $g$ is continuous on $[-\pi, \pi]$, it is square integrable by `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`.

4. Apply the Riemann-Lebesgue lemma for square integrable functions (`RIEMANN_LEBESGUE_SQUARE_INTEGRABLE`) to $g$, using the fact that the trigonometric system forms an orthonormal basis:
   $$\lim_{n \to \infty} \hat{g}(n) = 0$$

5. This means there exists $N$ such that for all $n \geq N$, we have $|\hat{g}(n)| < \frac{\varepsilon}{2}$.

6. For the difference between Fourier coefficients of $f$ and $g$:
   $$|\hat{f}(n) - \hat{g}(n)| = \left|\int_{-\pi}^{\pi} (f(x) - g(x)) \cdot \text{trigonometric\_set}(n)(x) \, dx \right|$$

7. Using the properties of the trigonometric set (sines and cosines), we note that $|\text{trigonometric\_set}(n)(x)| \leq 1$ for all $n$ and $x$, which gives:
   $$|\hat{f}(n) - \hat{g}(n)| \leq \int_{-\pi}^{\pi} |f(x) - g(x)| \, dx < \frac{\varepsilon}{2}$$

8. By the triangle inequality:
   $$|\hat{f}(n)| \leq |\hat{f}(n) - \hat{g}(n)| + |\hat{g}(n)| < \frac{\varepsilon}{2} + \frac{\varepsilon}{2} = \varepsilon$$

9. Therefore, for all $n \geq N$, $|\hat{f}(n)| < \varepsilon$, proving that $\lim_{n \to \infty} \hat{f}(n) = 0$.

### Mathematical insight
The Riemann-Lebesgue lemma is a foundational result in Fourier analysis, stating that the Fourier coefficients of an integrable function must decay to zero as the frequency increases. This result has several important implications:

1. It demonstrates that high-frequency components contribute less to the overall representation of an integrable function.

2. The result holds for both absolutely integrable and square integrable functions, with the proof for square integrable functions often being more straightforward.

3. This theorem is crucial for convergence results in Fourier theory and plays a key role in the study of partial differential equations and harmonic analysis.

4. The proof strategy—approximating a general integrable function by a continuous one—is a common and powerful technique in analysis.

The lemma is named after Bernhard Riemann and Henri Lebesgue, reflecting its importance in the development of integration theory.

### Dependencies
- **Theorems**:
  - `ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS`: Approximation of absolutely integrable functions by continuous functions
  - `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`: Continuous functions are square integrable
  - `ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET`: The trigonometric system forms an orthonormal basis
  - `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`: Each trigonometric function is square integrable
  - `TRIGONOMETRIC_SET_MUL_INTEGRABLE`: Product of trigonometric function with absolutely integrable function is integrable
  - `RIEMANN_LEBESGUE_SQUARE_INTEGRABLE`: Riemann-Lebesgue lemma for square integrable functions
  - `ODD_EVEN_INDUCT_LEMMA`: Induction principle for natural numbers using cases 0, odd, even
  - `trigonometric_set`: Properties of trigonometric basis functions

- **Definitions**:
  - `l2product`: Inner product in L² space
  - `orthonormal_coefficient`: Coefficients with respect to an orthonormal system
  - `fourier_coefficient`: Fourier coefficients with the trigonometric system

### Porting notes
When porting this theorem:

1. Ensure your system has a well-defined notion of absolute integrability and the corresponding approximation theorems.

2. The proof relies on explicit bounds of trigonometric functions (sines and cosines) and the structure of the trigonometric basis. Make sure these properties are available.

3. The proof structure involving approximation of integrable functions by continuous ones is standard, but the details of implementing this approach may vary between proof assistants.

4. Special care should be taken with the orthonormal system formalization, as different systems might represent function spaces and inner products differently.

5. The value of π and its properties (like positivity) are used in the proof and should be appropriately declared in the target system.

---

## RIEMANN_LEBESGUE_SIN

### RIEMANN_LEBESGUE_SIN
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SIN = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. sin(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function $f$ that is absolutely real integrable on the interval $[-\pi,\pi]$, the sequence $\left\{\int_{-\pi}^{\pi} \sin(nx) \cdot f(x) \, dx\right\}_{n=1}^{\infty}$ converges to 0.

Formally, if $f$ is absolutely real integrable on $[-\pi,\pi]$, then:
$$\lim_{n \to \infty} \int_{-\pi}^{\pi} \sin(nx) \cdot f(x) \, dx = 0$$

### Informal proof
This theorem is a specific case of the Riemann-Lebesgue lemma applied to sine functions. The proof proceeds as follows:

* We start with the general Riemann-Lebesgue lemma (`RIEMANN_LEBESGUE`), which states that Fourier coefficients of absolutely integrable functions vanish at infinity.

* For any positive real $\varepsilon$, we need to find $M$ such that for all $n \geq M$, $|\int_{-\pi}^{\pi} \sin(nx)f(x)dx| < \varepsilon$.

* We use `RIEMANN_LEBESGUE` with $\varepsilon/4$ to find an $N$ such that for all $n \geq N$, the Fourier coefficient $|c_n| < \varepsilon/4$.

* We choose $M = N + 1$ and proceed by induction.

* For $n \geq N + 1$, we connect the integral $\int_{-\pi}^{\pi} \sin(nx)f(x)dx$ to the Fourier coefficient $c_{2n+1}$.

* From the definition of the trigonometric system, we know that $c_{2n+1}$ is related to $\sin((n+1)x)$, so we need to carefully handle the indices.

* We leverage the following relationships:
  - The Fourier coefficient $c_{2n+1}$ corresponds to $\frac{1}{\sqrt{\pi}}\int_{-\pi}^{\pi}\sin((n+1)x)f(x)dx$
  - For $n \geq N + 1$, $|c_{2n+1}| < \frac{\varepsilon}{4}$

* After algebraic manipulations and normalization by $\sqrt{\pi}$, we can show that:
  $$\left|\int_{-\pi}^{\pi}\sin(nx)f(x)dx\right| < \varepsilon\sqrt{\pi} \cdot \frac{1}{4} \leq \varepsilon$$

* The final inequality holds because $\sqrt{\pi} \leq 4$, which can be verified using the approximation $\pi \approx 3.14159... < 16$.

### Mathematical insight
The Riemann-Lebesgue lemma is a fundamental result in Fourier analysis stating that the Fourier coefficients of an integrable function tend to zero as the frequency increases. This theorem specifically addresses the sine terms of the Fourier series.

The result has important implications:
- It demonstrates that high-frequency components have diminishing contribution to the Fourier representation of an integrable function
- It confirms that Fourier series capture the behavior of integrable functions effectively
- It is a key component in the theory of Fourier transforms and harmonic analysis

The proof strategy leverages the general Riemann-Lebesgue lemma and connects it to the specific case of sine functions through careful index manipulation and the trigonometric system definition.

### Dependencies
- Theorems:
  - `RIEMANN_LEBESGUE`: The general Riemann-Lebesgue lemma for Fourier coefficients
  - `trigonometric_set`: Definition of the trigonometric basis functions
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Integrability of products of trigonometric functions with integrable functions

- Definitions:
  - `fourier_coefficient`: The Fourier coefficients of a function
  - `orthonormal_coefficient`: Coefficients of a function with respect to an orthonormal system
  - `l2product`: The inner product in L² space

### Porting notes
When porting this theorem:
1. Ensure your system has a formalization of the Riemann-Lebesgue lemma for general Fourier coefficients first.
2. Pay attention to the indexing of the trigonometric system, as different formalizations might use different conventions.
3. The proof relies on bounds for π; ensure your system has available approximations or bounds for π (specifically that √π ≤ 4).
4. The induction principle used here is relatively simple but might need to be adapted to the target system's induction tactics.

---

## RIEMANN_LEBESGUE_COS

### RIEMANN_LEBESGUE_COS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_COS = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. cos(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function $f$ that is absolutely real integrable on the interval $[-\pi, \pi]$, the sequence of Fourier cosine coefficients $\left(\int_{-\pi}^{\pi} \cos(nx) \cdot f(x) \, dx\right)_{n=0}^{\infty}$ converges to $0$ as $n$ approaches infinity.

More formally, if $f$ is absolutely real integrable on $[-\pi, \pi]$, then:

$$\lim_{n \to \infty} \int_{-\pi}^{\pi} \cos(nx) \cdot f(x) \, dx = 0$$

### Informal proof
This theorem is a direct consequence of the Riemann-Lebesgue lemma. The proof proceeds as follows:

- Start with a function $f$ that is absolutely real integrable on $[-\pi, \pi]$.
- Apply the Riemann-Lebesgue lemma (theorem `RIEMANN_LEBESGUE`), which states that the Fourier coefficients of such a function converge to 0.
- For any $\varepsilon > 0$, find $N$ such that for all $n \geq N$, the Fourier coefficient $\hat{f}(n) < \frac{\varepsilon}{4}$.
- Use induction to show that for $n \geq N+1$, the cosine integral $\int_{-\pi}^{\pi} \cos(nx) \cdot f(x) \, dx$ is less than $\varepsilon$.
- The key step is to relate the cosine integral to the Fourier coefficients by using the definition of trigonometric set.
- Specifically, from the definition of `trigonometric_set`, we know that for $n \geq 1$:
  - $\text{trigonometric\_set}(2n+2) = \frac{\cos((n+1)x)}{\sqrt{\pi}}$
- This shows that the cosine integral $\int_{-\pi}^{\pi} \cos((n+1)x) \cdot f(x) \, dx$ is related to the Fourier coefficient for index $2n+2$.
- After applying some algebraic manipulations and bounds related to $\pi$, we establish that the cosine integral is less than $\varepsilon$.

### Mathematical insight
The Riemann-Lebesgue lemma is a fundamental result in Fourier analysis, stating that the Fourier coefficients of an integrable function tend to zero as the frequency increases. This theorem focuses specifically on the cosine terms of the Fourier series.

The result is important because:
1. It demonstrates that high-frequency components of a Fourier series become negligible for integrable functions
2. It characterizes the behavior of Fourier expansions at infinity
3. It provides a necessary condition for a function to be integrable

This particular formulation isolates the cosine coefficients, which is useful for applications where only the even (cosine) part of the Fourier series is needed.

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Defines the orthonormal basis for Fourier series in the interval $[-\pi, \pi]$
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Shows that products of trigonometric functions with an integrable function are integrable
  - `RIEMANN_LEBESGUE`: The general Riemann-Lebesgue lemma for Fourier coefficients

- **Definitions**:
  - `l2product`: The inner product in $L^2$ space defined as the integral of the product
  - `orthonormal_coefficient`: The coefficient of a function in an orthonormal basis
  - `fourier_coefficient`: Specializes the orthonormal coefficient to the Fourier basis

### Porting notes
When porting this theorem:
1. Ensure the underlying integration theory is compatible, especially for absolute integrability
2. Verify that the trigonometric basis is appropriately normalized in the target system
3. The proof relies on specific real number approximations of $\pi$, which might need adjustment in other systems
4. The induction step might need restructuring depending on how induction is handled in the target system

---

## RIEMANN_LEBESGUE_SIN_HALF

### Name of formal statement
RIEMANN_LEBESGUE_SIN_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SIN_HALF = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                               (\x. sin((&n + &1 / &2) * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SIN_ADD; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(\n. real_integral (real_interval[--pi,pi])
                          (\x. sin(&n * x) * cos(&1 / &2 * x) * f x) +
                   real_integral (real_interval[--pi,pi])
                          (\x. cos(&n * x) * sin(&1 / &2 * x) * f x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INTEGRAL_ADD;
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANN_LEBESGUE_SIN;
      MATCH_MP_TAC RIEMANN_LEBESGUE_COS]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
               ABSOLUTELY_INTEGRABLE_COS_PRODUCT]);;
```

### Informal statement
For any function $f$ that is absolutely real integrable on the interval $[-\pi, \pi]$, the sequence
$$\left(\int_{-\pi}^{\pi} \sin\left((n + \frac{1}{2})x\right) \cdot f(x) \, dx\right)_{n=1}^{\infty}$$
converges to 0 as $n$ approaches infinity.

### Informal proof
The proof applies the trigonometric identity for the sine of a sum to transform the integrand:

$$\sin\left((n + \frac{1}{2})x\right) = \sin(nx)\cos(\frac{1}{2}x) + \cos(nx)\sin(\frac{1}{2}x)$$

Therefore, the integral can be rewritten as the sum of two integrals:

$$\int_{-\pi}^{\pi} \sin\left((n + \frac{1}{2})x\right) \cdot f(x) \, dx = \int_{-\pi}^{\pi} \sin(nx)\cos(\frac{1}{2}x) \cdot f(x) \, dx + \int_{-\pi}^{\pi} \cos(nx)\sin(\frac{1}{2}x) \cdot f(x) \, dx$$

The proof then applies:
- The Riemann-Lebesgue lemma for sine (`RIEMANN_LEBESGUE_SIN`) to show that the first integral approaches 0 as $n$ approaches infinity.
- The Riemann-Lebesgue lemma for cosine (`RIEMANN_LEBESGUE_COS`) to show that the second integral approaches 0 as $n$ approaches infinity.

These applications are valid because if $f$ is absolutely integrable on $[-\pi, \pi]$, then the products $\cos(\frac{1}{2}x) \cdot f(x)$ and $\sin(\frac{1}{2}x) \cdot f(x)$ are also absolutely integrable.

Since both integrals approach 0, their sum also approaches 0.

### Mathematical insight
This theorem extends the Riemann-Lebesgue lemma to handle the case where we have a half-integer multiple of the argument in the sine function. The Riemann-Lebesgue lemma is a fundamental result in Fourier analysis that states that the Fourier coefficients of an integrable function tend to zero as the frequency increases. This particular variant is useful for analyzing the behavior of Fourier series with half-integer frequencies.

The proof elegantly decomposes the problem into cases that can be handled by the standard Riemann-Lebesgue lemmas for sine and cosine functions. This approach is a common strategy in Fourier analysis: transform a complex expression into simpler components that have known behaviors.

### Dependencies
#### Theorems
- `RIEMANN_LEBESGUE_SIN`: The Riemann-Lebesgue lemma for sine functions, stating that for any absolutely integrable function $f$ on $[-\pi,\pi]$, the sequence $\int_{-\pi}^{\pi} \sin(nx)f(x)dx$ approaches 0 as $n$ approaches infinity.
- `RIEMANN_LEBESGUE_COS`: The Riemann-Lebesgue lemma for cosine functions, stating that for any absolutely integrable function $f$ on $[-\pi,\pi]$, the sequence $\int_{-\pi}^{\pi} \cos(nx)f(x)dx$ approaches 0 as $n$ approaches infinity.

#### Other functions and lemmas used
- `SIN_ADD`: The trigonometric identity for the sine of a sum
- `REAL_INTEGRAL_ADD`: Theorem about the additivity of integrals
- `REALLIM_NULL_ADD`: Theorem stating that if two sequences approach 0, their sum also approaches 0
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`, `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`: Theorems about the absolute integrability of products with sine and cosine functions

### Porting notes
When porting this theorem to other proof assistants, ensure:
1. The trigonometric identity for sine of a sum is available
2. The Riemann-Lebesgue lemmas for sine and cosine functions are already implemented
3. The system has a suitable way to express convergence of sequences of real numbers
4. The system can handle real integrals and absolute integrability of functions

The proof is relatively straightforward once the dependencies are in place, as it relies mainly on basic properties of trigonometric functions and core results from Fourier analysis.

---

## FOURIER_SUM_LIMIT_PAIR

### Name of formal statement
FOURIER_SUM_LIMIT_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_PAIR = prove
 (`!f n t l.
        f absolutely_real_integrable_on real_interval [--pi,pi]
        ==> (((\n. sum(0..2*n) (\k. fourier_coefficient f k *
                                    trigonometric_set k t)) ---> l)
             sequentially <=>
             ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                  trigonometric_set k t)) ---> l)
             sequentially)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
    SUBGOAL_THEN `&0 < e / &2` (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "2")) THEN
    EXISTS_TAC `N1 + 2 * N2 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    DISJ_CASES_THEN SUBST1_TAC
     (ARITH_RULE `n = 2 * n DIV 2 \/ n = SUC(2 * n DIV 2)`) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x < e / &2 ==> abs x < e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `abs(x - l) < e / &2 /\ abs y < e / &2 ==> abs((x + y) - l) < e`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x * y) <= abs(x) * &1 /\ abs(x) < e ==> abs(x * y) < e`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN
        SPEC_TAC(`SUC(2 * n DIV 2)`,`r:num`) THEN
        MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
        REWRITE_TAC[ADD1; trigonometric_set; REAL_ABS_DIV] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
                 SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
        SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
```

### Informal statement
For any function $f$ that is absolutely real integrable on the interval $[-\pi, \pi]$, and for any real number $t$ and limit $l$, the following statements are equivalent:

1. The sequence of partial sums $\left(\sum_{k=0}^{2n} \hat{f}(k) \cdot \phi_k(t)\right)_{n=0}^{\infty}$ converges to $l$.
2. The sequence of partial sums $\left(\sum_{k=0}^{n} \hat{f}(k) \cdot \phi_k(t)\right)_{n=0}^{\infty}$ converges to $l$.

Where $\hat{f}(k)$ denotes the $k$-th Fourier coefficient of $f$, and $\phi_k(t)$ represents the $k$-th trigonometric basis function evaluated at point $t$.

### Informal proof
The proof shows that the two different summing methods (summing up to $2n$ versus summing up to $n$) both converge to the same limit if either converges.

* First, we prove that if the sequence summing to $2n$ converges to $l$, then the sequence summing to $n$ also converges to $l$:
  - By the Riemann-Lebesgue lemma (`RIEMANN_LEBESGUE`), we know that $\hat{f}(n) \to 0$ as $n \to \infty$, since $f$ is absolutely integrable.
  - Given $\varepsilon > 0$, there exists $N_1$ such that $|\hat{f}(n)| < \varepsilon/2$ for all $n \geq N_1$.
  - Also, there exists $N_2$ such that $|\sum_{k=0}^{2n}\hat{f}(k)\phi_k(t) - l| < \varepsilon/2$ for all $n \geq N_2$.
  - We take $N = N_1 + 2N_2 + 1$ and consider $n \geq N$.
  - We split the analysis into two cases based on whether $n$ is even or odd.
  - When $n = 2(n \text{ DIV } 2)$ (even case), the sum up to $n$ matches a sum up to $2m$ for some $m$, so the result follows directly.
  - When $n = 1 + 2(n \text{ DIV } 2)$ (odd case), we can write:
    $\sum_{k=0}^{n}\hat{f}(k)\phi_k(t) = \sum_{k=0}^{n-1}\hat{f}(k)\phi_k(t) + \hat{f}(n)\phi_n(t)$
  - The first term is within $\varepsilon/2$ of $l$ by our assumption, and $|\hat{f}(n)\phi_n(t)| < \varepsilon/2$ since $|\phi_n(t)| \leq 1$ for trigonometric functions.
  - Thus the sum up to $n$ is within $\varepsilon$ of $l$.

* For the converse direction, we prove that if the sequence summing to $n$ converges to $l$, then the sequence summing to $2n$ also converges to $l$:
  - This direction is simpler. Given $\varepsilon > 0$, there exists $N$ such that $|\sum_{k=0}^{n}\hat{f}(k)\phi_k(t) - l| < \varepsilon$ for all $n \geq N$.
  - Since $2n \geq n$ for all $n$, the sum up to $2n$ is also within $\varepsilon$ of $l$ whenever $n \geq N$.

### Mathematical insight
This theorem establishes that when studying the convergence of Fourier series, it doesn't matter whether we use partial sums up to indices of the form $2n$ or up to arbitrary indices $n$ - both sequences converge to the same limit when either converges. This is useful because it gives flexibility in how we analyze Fourier series convergence.

The key insight is that the Fourier coefficients eventually become very small (by the Riemann-Lebesgue lemma), so the difference between summing up to $n$ or $2n$ becomes negligible as $n$ increases. This result simplifies the analysis of Fourier series by showing that different summation patterns lead to the same limit.

### Dependencies
- **Theorems**:
  - `RIEMANN_LEBESGUE`: States that if a function is absolutely integrable on $[-\pi, \pi]$, then its Fourier coefficients approach zero.
  - `trigonometric_set`: Defines the trigonometric basis functions.
  - `ODD_EVEN_INDUCT_LEMMA`: A number theory induction principle for handling both odd and even cases.

- **Definitions**:
  - `fourier_coefficient`: Defines the Fourier coefficients in terms of orthonormal coefficients.

### Porting notes
When porting this theorem:
- Ensure that the trigonometric basis functions are properly normalized in the target system.
- The Riemann-Lebesgue lemma is a key dependency and should be ported first.
- The proof relies on properties of trigonometric functions (bounds for sine and cosine), which should be available in most proof assistants.
- The handling of odd and even cases might require different approaches in other systems, depending on how natural number arithmetic is formalized.

---

## FOURIER_SUM_0

### Name of formal statement
FOURIER_SUM_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0 = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     sum (0..n DIV 2)
         (\k. fourier_coefficient f (2 * k) * trigonometric_set (2 * k) (&0))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (2 * 0..2 * (n DIV 2) + 1)
                 (\k. fourier_coefficient f k * trigonometric_set k (&0))` THEN
  CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[IN_NUMSEG; SUBSET; LE_0] THEN
    CONJ_TAC THENL [ARITH_TAC; GEN_TAC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x <= 2 * n DIV 2 + 1 /\ ~(x <= n) ==> x = 2 * n DIV 2 + 1`));
    REWRITE_TAC[SUM_PAIR]] THEN
  REWRITE_TAC[trigonometric_set;  real_div; REAL_MUL_RZERO; SIN_0;
              REAL_MUL_LZERO; REAL_ADD_RID]);;
```

### Informal statement
For any function $f$ and natural number $n$, the sum of Fourier coefficients multiplied by the trigonometric basis functions evaluated at $0$ can be simplified as:

$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f)(k) \cdot \text{trigonometric\_set}(k)(0) = \sum_{k=0}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f)(2k) \cdot \text{trigonometric\_set}(2k)(0)$$

This shows that when evaluating the Fourier sum at the origin, only the even-indexed terms ($2k$) contribute to the sum, as the odd-indexed terms vanish.

### Informal proof
We prove that the sum over all indices $0$ to $n$ equals the sum over just the even indices from $0$ to $n$.

First, we rewrite the left-hand side as a sum over the range $[0, 2\lfloor n/2 \rfloor + 1]$, which is equal to the original sum over $[0,n]$ by the properties of integer division.

For this equality, we use the `SUM_SUPERSET` theorem, showing that:
1. The range $[0,n]$ is a subset of $[0, 2\lfloor n/2 \rfloor + 1]$
2. Any element in the larger set but not in $[0,n]$ must equal $2\lfloor n/2 \rfloor + 1$

Next, we apply `SUM_PAIR` to split the sum over $[0, 2\lfloor n/2 \rfloor + 1]$ into sums over even and odd indices.

Finally, we use the definition of `trigonometric_set` and the fact that:
- For odd indices (of the form $2k+1$), the basis function evaluates to $\sin((k+1) \cdot 0)/\sqrt{\pi} = 0$ since $\sin(0) = 0$
- Only the even-indexed terms (of the form $2k$) remain, giving us the right-hand side of the equation

### Mathematical insight
This theorem reveals an important property of Fourier series evaluated at the origin: only the cosine terms (corresponding to even indices) contribute to the sum, while all sine terms (corresponding to odd indices) vanish. This is because sine functions evaluate to zero at the origin.

The result simplifies computations of Fourier series at $x = 0$ by allowing us to consider only half the terms. It's particularly useful in applications where the behavior of a function at the origin is of special interest, such as in signal processing or differential equations.

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Defines the trigonometric basis functions used in Fourier series

- **Definitions**:
  - `fourier_coefficient`: Defined as the orthonormal coefficient with respect to the trigonometric set on the interval $[-\pi, \pi]$

### Porting notes
When porting this theorem:
- Ensure that the `trigonometric_set` is correctly defined with the appropriate normalization factors
- The proof relies on properties of summation and trigonometric functions at the origin
- The notation for integer division ($n$ DIV $2$) might need adjustment depending on the target system

---

## FOURIER_SUM_0_EXPLICIT

### Name of formal statement
FOURIER_SUM_0_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_EXPLICIT = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     (fourier_coefficient f 0 / sqrt(&2) +
      sum (1..n DIV 2) (\k. fourier_coefficient f (2 * k))) / sqrt pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FOURIER_SUM_0] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; real_div;
           REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[MULT_CLAUSES; trigonometric_set;
              REAL_MUL_LZERO; COS_0; real_div] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID; SQRT_MUL; REAL_INV_MUL; GSYM REAL_MUL_ASSOC];
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID]]);;
```

### Informal statement
For all functions $f$ and natural numbers $n$, the following equation holds:

$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, 0) = \frac{\text{fourier\_coefficient}(f, 0) / \sqrt{2} + \sum_{k=1}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f, 2k)}{\sqrt{\pi}}$$

where $\text{fourier\_coefficient}(f, k)$ represents the $k$-th Fourier coefficient of function $f$ on the interval $[-\pi, \pi]$, and $\text{trigonometric\_set}(k, 0)$ is the $k$-th function from the trigonometric basis evaluated at $0$.

### Informal proof
The proof begins by applying the theorem `FOURIER_SUM_0`, which states that:

$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, 0) = \sum_{k=0}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f, 2k) \cdot \text{trigonometric\_set}(2k, 0)$$

Next, we simplify the right-hand side by:

1. Applying the sum clauses to separate the term with $k = 0$ from the rest of the sum:
   $$\text{fourier\_coefficient}(f, 0) \cdot \text{trigonometric\_set}(0, 0) + \sum_{k=1}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f, 2k) \cdot \text{trigonometric\_set}(2k, 0)$$

2. Using the definition of $\text{trigonometric\_set}$ to substitute:
   
   - $\text{trigonometric\_set}(0, x) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$
   - $\text{trigonometric\_set}(2k, x) = \frac{\cos(k \cdot x)}{\sqrt{\pi}}$ for $k \geq 1$

3. Evaluating at $x = 0$, where $\cos(0) = 1$, we get:
   
   - $\text{trigonometric\_set}(0, 0) = \frac{1}{\sqrt{2\pi}}$
   - $\text{trigonometric\_set}(2k, 0) = \frac{1}{\sqrt{\pi}}$ for $k \geq 1$

4. Therefore, our sum becomes:
   
   $$\text{fourier\_coefficient}(f, 0) \cdot \frac{1}{\sqrt{2\pi}} + \sum_{k=1}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f, 2k) \cdot \frac{1}{\sqrt{\pi}}$$

5. Distributing terms and factoring out $\frac{1}{\sqrt{\pi}}$:
   
   $$\frac{\text{fourier\_coefficient}(f, 0) \cdot \frac{1}{\sqrt{2}} + \sum_{k=1}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f, 2k)}{\sqrt{\pi}}$$

Which is exactly the right-hand side of the equation to be proved.

### Mathematical insight
This theorem provides an explicit formula for computing the sum of Fourier coefficients multiplied by their corresponding trigonometric basis functions evaluated at zero. The result shows that only the even-indexed coefficients contribute to this sum because the odd-indexed trigonometric functions (sine functions) evaluate to zero at $x = 0$.

This formula is useful in Fourier analysis when evaluating the value of a Fourier series at $x = 0$. The theorem effectively simplifies the calculation by eliminating terms that don't contribute and reorganizing the remaining terms into a cleaner formula.

Conceptually, this reflects how the Fourier series representation behaves at the origin, and connects the function value at that point to its Fourier coefficients.

### Dependencies
- Theorems:
  - `FOURIER_SUM_0`: Shows that the sum of Fourier coefficients times trigonometric functions at zero equals the sum of just the even-indexed terms
  - `trigonometric_set`: Defines the trigonometric basis functions

- Definitions:
  - `fourier_coefficient`: Defined as the orthonormal coefficient with respect to the trigonometric basis on the interval [-π,π]

### Porting notes
When implementing this theorem in other systems:
1. Ensure the definition of `trigonometric_set` matches the HOL Light definition, particularly regarding normalization factors
2. The formula relies on the evaluation of trigonometric functions at 0, which should be consistent across systems
3. Pay attention to the handling of integer division (DIV operator) in the upper bound of the summation, as this represents the floor of n/2

---

## FOURIER_SUM_0_INTEGRALS

### Name of formal statement
FOURIER_SUM_0_INTEGRALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_INTEGRALS = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          (real_integral(real_interval[--pi,pi]) f / &2 +
           sum(1..n DIV 2) (\k. real_integral (real_interval[--pi,pi])
                                              (\x. cos(&k * x) * f x))) / pi`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FOURIER_SUM_0_EXPLICIT] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[trigonometric_set] THEN BINOP_TAC THENL
   [REWRITE_TAC[COS_0; REAL_MUL_LZERO; real_div; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    REWRITE_TAC[REAL_ARITH `((a * b) * c) * d:real = b * a * c * d`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    SIMP_TAC[GSYM SQRT_MUL; REAL_POS; PI_POS_LE; REAL_LE_MUL] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC POW_2_SQRT THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(i * x) * i:real = x * i * i`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[PI_POS_LE]]);;
```

### Informal statement
For any function $f$ that is absolutely real integrable on the interval $[-\pi, \pi]$ and for any natural number $n$, the finite sum of Fourier coefficients multiplied by the corresponding trigonometric basis functions evaluated at $0$ can be expressed as:

$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f)(k) \cdot \text{trigonometric\_set}(k)(0) = \frac{1}{\pi} \left(\frac{1}{2} \int_{-\pi}^{\pi} f(x) \, dx + \sum_{k=1}^{\lfloor n/2 \rfloor} \int_{-\pi}^{\pi} \cos(k x) \cdot f(x) \, dx \right)$$

This relates the finite Fourier series at zero to direct integrals of the function and its products with cosines.

### Informal proof
We prove this by relating the Fourier sum expression to explicit integrals.

* Begin with the formula from `FOURIER_SUM_0_EXPLICIT` which states:
  $$\sum_{k=0}^{n} \text{fourier\_coefficient}(f)(k) \cdot \text{trigonometric\_set}(k)(0) = \frac{1}{\sqrt{\pi}}\left(\frac{\text{fourier\_coefficient}(f)(0)}{\sqrt{2}} + \sum_{k=1}^{\lfloor n/2 \rfloor} \text{fourier\_coefficient}(f)(2k)\right)$$

* Expand the Fourier coefficients using their definitions:
  - `fourier_coefficient = orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`
  - `orthonormal_coefficient s w f n = l2product s (w n) f`
  - `l2product s f g = real_integral s (λx. f(x) * g(x))`

* For the first term in the sum (k=0):
  - From `trigonometric_set`, we know `trigonometric_set 0 = (λx. cos(0*x)/sqrt(2*π))`
  - At x=0, cos(0) = 1
  - After distributing and simplifying, the first term becomes `real_integral(real_interval[--pi,pi]) f / (2*π)`

* For the remaining terms (k≥1):
  - For even indices 2k, we have `trigonometric_set (2*k) = (λx. cos(k*x)/sqrt(π))`
  - Each term in the sum becomes `real_integral(real_interval[--pi,pi]) (λx. cos(k*x)*f(x)) / π`

* The result follows by combining these terms and simplifying the square roots using algebraic manipulations.

### Mathematical insight
This theorem provides an explicit relationship between a partial Fourier series evaluated at zero and direct integrals of the function. The connection is particularly important for computational aspects of Fourier analysis, as it provides a way to compute the value of a truncated Fourier series at the specific point x=0 without having to compute all the coefficients and then evaluate the series.

The formula effectively shows that the value of a partial Fourier series at zero is determined by the average value of the function (the first integral term) plus a weighted sum of cosine-modulated integrals. This highlights the specific contributions of the even-indexed Fourier coefficients to the value at zero, which is a consequence of the fact that sine terms (associated with odd indices) evaluate to zero at x=0.

### Dependencies
- Definitions:
  - `l2product`: The L² inner product of two functions
  - `orthonormal_coefficient`: Generalizes Fourier coefficients for orthonormal systems
  - `fourier_coefficient`: Specializes to the trigonometric system on [-π,π]

- Theorems:
  - `trigonometric_set`: Defines the trigonometric basis functions
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Ensures integrability of products with trigonometric functions
  - `FOURIER_SUM_0_EXPLICIT`: Gives an explicit formula for the Fourier sum at zero

### Porting notes
When porting to other proof assistants, pay attention to:
1. The handling of real integrals and the notion of absolute integrability
2. The representation of trigonometric functions and their evaluation at specific points
3. The definition of the Fourier basis and coefficients, which may vary slightly between systems

---

## FOURIER_SUM_0_INTEGRAL

### FOURIER_SUM_0_INTEGRAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_INTEGRAL = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum(0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          real_integral(real_interval[--pi,pi])
           (\x. (&1 / &2 + sum(1..n DIV 2) (\k. cos(&k * x))) * f x) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_0_INTEGRALS] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
               FOURIER_PRODUCTS_INTEGRABLE_STRONG; real_div;
               GSYM REAL_INTEGRAL_ADD;
               GSYM REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_RMUL; ETA_AX;
               REAL_INTEGRABLE_SUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; SUM_RMUL] THEN REAL_ARITH_TAC);;
```

### Informal statement

For any function $f$ that is absolutely real integrable on the interval $[-\pi,\pi]$ and any natural number $n$, the following equality holds:

$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, 0) = \frac{1}{\pi} \int_{-\pi}^{\pi} \left(\frac{1}{2} + \sum_{k=1}^{\lfloor n/2 \rfloor} \cos(k \cdot x)\right) \cdot f(x) \, dx$$

This equation relates the sum of Fourier coefficients multiplied by trigonometric basis functions (evaluated at 0) to an integral involving the original function $f$ multiplied by a specific trigonometric expression.

### Informal proof

The proof proceeds as follows:

* We start by applying the theorem `FOURIER_SUM_0_INTEGRALS`, which gives us:

  $$\sum_{k=0}^{n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, 0) = \frac{1}{\pi}\left(\frac{1}{2}\int_{-\pi}^{\pi} f(x) \, dx + \sum_{k=1}^{\lfloor n/2 \rfloor} \int_{-\pi}^{\pi} \cos(k \cdot x) \cdot f(x) \, dx\right)$$

* Next, we use several integral properties to simplify the right-hand side:
  - `GSYM REAL_INTEGRAL_SUM` to bring the sum inside the integral
  - `GSYM REAL_INTEGRAL_ADD` to combine the integrals
  - `GSYM REAL_INTEGRAL_RMUL` to handle the constant factor $\frac{1}{2}$

* These transformations allow us to rewrite the right-hand side as:
  $$\frac{1}{\pi} \int_{-\pi}^{\pi} \left(\frac{1}{2} + \sum_{k=1}^{\lfloor n/2 \rfloor} \cos(k \cdot x)\right) \cdot f(x) \, dx$$

* The proof concludes with some function equality reasoning and arithmetic simplification.

### Mathematical insight

This theorem provides a key relationship in Fourier analysis, showing how the partial sum of Fourier coefficients at $x=0$ can be expressed as an integral involving the original function $f$ and a specific trigonometric kernel (the Dirichlet kernel plus a constant term).

The result is particularly important for understanding the behavior of Fourier series at specific points and for analyzing the convergence of Fourier series. The right side of the equation essentially represents a convolution of the function $f$ with a truncated Dirichlet kernel, which approximates the function's value at zero as $n$ increases.

This is a concrete instance of the more general phenomenon where partial sums of Fourier series can be represented as convolutions with Dirichlet kernels, which is fundamental to the study of Fourier analysis and its applications.

### Dependencies

- **Theorems**:
  - `trigonometric_set`: Defines the trigonometric basis functions used in Fourier series
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Shows that products of trigonometric functions with absolutely integrable functions are integrable
  - `FOURIER_SUM_0_INTEGRALS`: Provides a form of the Fourier sum at 0 in terms of integrals

- **Definitions**:
  - `fourier_coefficient`: Defines Fourier coefficients as orthonormal coefficients with respect to the trigonometric basis

### Porting notes

When porting this theorem:
- The Fourier coefficient and trigonometric set definitions should be ported first.
- The integral libraries in the target system need to support operations on absolutely integrable functions.
- Care should be taken with the specific normalization constants (involving π) used in HOL Light's Fourier series definition, as these can differ between mathematical libraries.

---

## FOURIER_COEFFICIENT_ADD

### FOURIER_COEFFICIENT_ADD
- `FOURIER_COEFFICIENT_ADD`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_ADD = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x + g x) i =
                fourier_coefficient f i + fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_ADD_LDISTRIB;
           REAL_INTEGRAL_ADD]);;
```

### Informal statement
For any functions $f$ and $g$ that are absolutely real integrable on the interval $[-\pi, \pi]$ and any natural number $i$, the Fourier coefficient of the sum $(f + g)$ at index $i$ equals the sum of the individual Fourier coefficients:

$$\text{fourier\_coefficient}(f + g, i) = \text{fourier\_coefficient}(f, i) + \text{fourier\_coefficient}(g, i)$$

where $\text{fourier\_coefficient}(f, i)$ represents the $i$-th Fourier coefficient of function $f$.

### Informal proof
The theorem follows from the linearity of integration and properties of Fourier coefficients.

Starting with the definition of Fourier coefficients:

- Fourier coefficients are defined as `fourier_coefficient = orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`
- `orthonormal_coefficient s w f n = l2product s (w n) f`
- `l2product s f g = real_integral s (λx. f(x) * g(x))`

So, `fourier_coefficient f i` expands to:
$$\text{fourier\_coefficient}(f, i) = \int_{-\pi}^{\pi} f(x) \cdot \text{trigonometric\_set}(i, x) \, dx$$

For the sum $(f + g)$, we have:
$$\text{fourier\_coefficient}(f + g, i) = \int_{-\pi}^{\pi} (f(x) + g(x)) \cdot \text{trigonometric\_set}(i, x) \, dx$$

By distributivity of multiplication over addition:
$$= \int_{-\pi}^{\pi} (f(x) \cdot \text{trigonometric\_set}(i, x) + g(x) \cdot \text{trigonometric\_set}(i, x)) \, dx$$

The functions $f$ and $g$ are absolutely real integrable on $[-\pi, \pi]$, which implies that $\text{trigonometric\_set}(i) \cdot f$ and $\text{trigonometric\_set}(i) \cdot g$ are real integrable (by theorem `TRIGONOMETRIC_SET_MUL_INTEGRABLE`).

Therefore, by the linearity of integration (`REAL_INTEGRAL_ADD`):
$$= \int_{-\pi}^{\pi} f(x) \cdot \text{trigonometric\_set}(i, x) \, dx + \int_{-\pi}^{\pi} g(x) \cdot \text{trigonometric\_set}(i, x) \, dx$$
$$= \text{fourier\_coefficient}(f, i) + \text{fourier\_coefficient}(g, i)$$

### Mathematical insight
This theorem establishes one of the fundamental properties of Fourier coefficients: linearity with respect to function addition. This property is an immediate consequence of the linearity of integration and is essential for analyzing combinations of functions via their Fourier series.

The linearity property allows us to analyze complex functions by breaking them down into simpler components. For instance, if we know the Fourier series of functions $f$ and $g$, we can easily compute the Fourier series of their sum without recomputing all the coefficients from scratch.

This result forms part of a larger family of theorems about how Fourier coefficients behave under different operations (addition, scalar multiplication, etc.), which collectively characterize the linearity of the Fourier transform.

### Dependencies
- Definitions:
  - `fourier_coefficient`
  - `orthonormal_coefficient`
  - `l2product`
  
- Theorems:
  - `TRIGONOMETRIC_SET_MUL_INTEGRABLE` - Ensures that products of trigonometric sets and absolutely integrable functions are integrable
  - `REAL_ADD_LDISTRIB` - Left distributivity of multiplication over addition for real numbers
  - `REAL_INTEGRAL_ADD` - Additivity of integration

### Porting notes
When porting this theorem, ensure that the definitions of Fourier coefficients and trigonometric sets match the HOL Light definitions. In particular:

1. Check that the Fourier coefficients are defined using the same normalization constants
2. Verify that the target system's definition of absolute integrability is equivalent
3. The theorem relies on the linearity of integration, which should be available in most proof assistants with real analysis libraries

---

## FOURIER_COEFFICIENT_SUB

### Name of formal statement
FOURIER_COEFFICIENT_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_SUB = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x - g x) i =
                fourier_coefficient f i - fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_SUB_LDISTRIB;
           REAL_INTEGRAL_SUB]);;
```

### Informal statement
For any functions $f$ and $g$ that are absolutely real integrable on the interval $[-\pi,\pi]$, and for any index $i$, the Fourier coefficient of the difference $f - g$ at index $i$ equals the difference of the respective Fourier coefficients:

$$\text{fourier\_coefficient}(f - g)(i) = \text{fourier\_coefficient}(f)(i) - \text{fourier\_coefficient}(g)(i)$$

### Informal proof
The proof follows from the linearity properties of integration and the definition of Fourier coefficients:

1. We begin by expanding the definition of `fourier_coefficient` using its definition as `orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`.

2. Next, we expand `orthonormal_coefficient` to its definition involving `l2product`.

3. We further expand `l2product` to reveal the integral representation:
   $$\text{l2product}(s, f, g) = \int_s f(x) \cdot g(x) \, dx$$

4. After these expansions, we can apply:
   - The distributive property of multiplication over subtraction (`REAL_SUB_LDISTRIB`)
   - The linearity of the integral with respect to subtraction (`REAL_INTEGRAL_SUB`)
   - The fact that the product of a trigonometric set function with an absolutely integrable function is integrable (`TRIGONOMETRIC_SET_MUL_INTEGRABLE`)

5. This allows us to separate the integral of the difference into the difference of the integrals, giving us the desired result.

### Mathematical insight
This theorem demonstrates the linearity of Fourier coefficients with respect to function subtraction, which is a fundamental property for working with Fourier series. This linearity property is crucial for manipulating and analyzing Fourier series in many applications, such as signal processing, differential equations, and harmonic analysis. The result follows directly from the linearity of integration and is expected behavior for any inner product-based coefficient calculation.

### Dependencies
- **Definitions**:
  - `fourier_coefficient`: Defines the Fourier coefficient as the orthonormal coefficient with respect to the trigonometric set on $[-\pi,\pi]$
  - `orthonormal_coefficient`: Defines how coefficients are calculated with respect to an orthonormal basis
  - `l2product`: Defines the L² inner product of two functions as their integrated product

- **Theorems**:
  - `TRIGONOMETRIC_SET_MUL_INTEGRABLE`: Shows that multiplying a trigonometric basis function by an absolutely integrable function yields an integrable function
  - `REAL_SUB_LDISTRIB`: The distributive property of multiplication over subtraction for real numbers
  - `REAL_INTEGRAL_SUB`: The linearity of integration with respect to subtraction

### Porting notes
When implementing this theorem in other proof assistants, ensure that:
1. The definitions of Fourier coefficients match HOL Light's structure, particularly with respect to how inner products and the trigonometric basis are defined
2. The underlying integration theory supports linearity properties
3. The appropriate integrability conditions are maintained throughout the proof

---

## FOURIER_COEFFICIENT_CONST

### FOURIER_COEFFICIENT_CONST
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_CONST = prove
 (`!c i. fourier_coefficient (\x. c) i =
         if i = 0 then c * sqrt(&2 * pi) else &0`,
  GEN_TAC THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product;
              trigonometric_set] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `0` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2 * pi)) * c` o
     MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC(REAL_FIELD
     `&0 < s /\ s pow 2 = &2 * pi ==> &2 * pi * inv(s) * c = c * s`) THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_MUL; REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT;
             ARITH; SQRT_POS_LT; PI_POS; REAL_LT_IMP_LE];
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_SIN_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE];
     X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE; REAL_MUL_LZERO]]);;
```

### Informal statement
For any constant $c$ and natural number $i$, the Fourier coefficient of the constant function $f(x) = c$ is:
$$\text{fourier\_coefficient}(f, i) = \begin{cases}
c \cdot \sqrt{2\pi} & \text{if } i = 0 \\
0 & \text{otherwise}
\end{cases}$$

This means that when computing the Fourier coefficients of a constant function, only the zeroth coefficient is non-zero, and it equals the constant value multiplied by $\sqrt{2\pi}$.

### Informal proof
The proof uses case analysis on the index $i$, considering three cases: $i=0$, $i=2n+1$ (odd indices), and $i=2n+2$ (even indices greater than 0).

For $i = 0$:
- We use the result that $\int_{-\pi}^{\pi} \cos(0 \cdot x) dx = 2\pi$
- The zeroth trigonometric function is $\frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$
- The Fourier coefficient is $\int_{-\pi}^{\pi} c \cdot \frac{\cos(0 \cdot x)}{\sqrt{2\pi}} dx = c \cdot \frac{2\pi}{\sqrt{2\pi}} = c \cdot \sqrt{2\pi}$

For $i = 2n+1$ (odd indices):
- We use the result that $\int_{-\pi}^{\pi} \sin((n+1) \cdot x) dx = 0$
- The odd-indexed trigonometric functions are $\frac{\sin((n+1) \cdot x)}{\sqrt{\pi}}$
- Therefore, all odd-indexed Fourier coefficients of a constant function are zero

For $i = 2n+2$ (even indices greater than 0):
- We use the result that $\int_{-\pi}^{\pi} \cos((n+1) \cdot x) dx = 0$ when $n+1 \neq 0$
- The even-indexed trigonometric functions are $\frac{\cos((n+1) \cdot x)}{\sqrt{\pi}}$
- Therefore, all even-indexed Fourier coefficients (except for $i=0$) of a constant function are zero

By induction on $i$ using the lemma `ODD_EVEN_INDUCT_LEMMA`, this covers all possible values of $i$.

### Mathematical insight
This theorem captures a fundamental property of Fourier series: a constant function is represented purely by its DC component (the zeroth coefficient), while all other (oscillatory) components have zero coefficients. 

This makes intuitive sense because a constant function has no variation or oscillation, so it can be fully represented by just the constant term in a Fourier series. The factor of $\sqrt{2\pi}$ comes from the normalization of the trigonometric basis functions.

This result is important as it provides a simple test case for Fourier analysis and is often used as a building block when analyzing more complex functions.

### Dependencies
- **Theorems**: 
  - `HAS_REAL_INTEGRAL_SIN_NX`: Shows that the integral of $\sin(nx)$ over $[-\pi,\pi]$ is 0
  - `HAS_REAL_INTEGRAL_COS_NX`: Shows that the integral of $\cos(nx)$ over $[-\pi,\pi]$ is $2\pi$ if $n=0$ and 0 otherwise
  - `trigonometric_set`: Defines the orthogonal set of trigonometric functions
  - `ODD_EVEN_INDUCT_LEMMA`: Provides induction for cases of 0, odd numbers, and even numbers

- **Definitions**:
  - `l2product`: Defines the inner product of two functions as their integral product
  - `orthonormal_coefficient`: Defines coefficients with respect to an orthonormal basis
  - `fourier_coefficient`: Specializes orthonormal coefficients to the trigonometric basis on $[-\pi,\pi]$

### Porting notes
When porting this theorem:
1. Ensure your system has a representation of the trigonometric basis functions with proper normalization
2. The integration theorems for trigonometric functions are critical dependencies
3. Consider using a simpler proof approach directly using the three cases rather than explicit induction, if your system has good support for case analysis
4. Pay attention to the normalization constants ($\sqrt{2\pi}$ and $\sqrt{\pi}$) which may differ in alternative formulations of Fourier analysis

---

## REAL_PERIODIC_INTEGER_MULTIPLE

### Name of formal statement
REAL_PERIODIC_INTEGER_MULTIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_PERIODIC_INTEGER_MULTIPLE = prove
 (`!f:real->real a.
        (!x. f(x + a) = f x) <=> (!x n. integer n ==> f(x + n * a) = f x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGER_CLOSED; REAL_MUL_LID]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x n. f(x + &n * a) = (f:real->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
                    REAL_ADD_ASSOC; REAL_MUL_LID];
    REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ARITH `(x + -- &n * a) + &n * a = x`]]);;
```

### Informal statement
For any function $f: \mathbb{R} \to \mathbb{R}$ and any real number $a$, the following statements are equivalent:
1. For all real $x$, $f(x + a) = f(x)$
2. For all real $x$ and all integers $n$, $f(x + n \cdot a) = f(x)$

This theorem states that a function being periodic with period $a$ is equivalent to that function being invariant under shifts by integer multiples of $a$.

### Informal proof
We need to prove both directions of the equivalence:

First, prove that (2) implies (1):
- This direction is straightforward because $n = 1$ is an integer.
- If $f(x + n \cdot a) = f(x)$ holds for all integers $n$, then in particular it holds for $n = 1$.
- Therefore, $f(x + a) = f(x + 1 \cdot a) = f(x)$ for all real $x$.

Now, prove that (1) implies (2):
- We first prove by induction on $n$ that $f(x + n \cdot a) = f(x)$ for all natural numbers $n$.
  * Base case ($n = 0$): $f(x + 0 \cdot a) = f(x + 0) = f(x)$
  * Inductive step: Assume $f(x + n \cdot a) = f(x)$ for some natural number $n$
  * For $n + 1$: $f(x + (n+1) \cdot a) = f(x + n \cdot a + a) = f(x + n \cdot a) = f(x)$
    where we used the periodicity assumption $f(y + a) = f(y)$ with $y = x + n \cdot a$
- For the general case with an arbitrary integer $n$, we consider two cases:
  * If $n \geq 0$, we use the result we just proved for natural numbers
  * If $n < 0$, then $n = -m$ for some natural number $m > 0$
  * For any $x$, let $y = x - m \cdot a$
  * Then $y + m \cdot a = x$, so $f(y + m \cdot a) = f(x)$
  * By our inductive result, $f(y + m \cdot a) = f(y)$
  * Therefore $f(x) = f(y) = f(x - m \cdot a)$
  * Substituting $x' = x - m \cdot a$, we get $f(x' + m \cdot a) = f(x')$
  * Since $n = -m$, we have $f(x' + n \cdot a) = f(x')$, completing the proof

### Mathematical insight
This theorem formalizes a fundamental property of periodic functions: a function with period $a$ maintains its values after any number of complete periods. This is useful for simplifying calculations with periodic functions and is essential for developing Fourier analysis.

The result may seem trivial, but it explicitly connects the basic definition of periodicity (shifting by one period) to the more general notion of invariance under integer multiple shifts. This connection is particularly important when working with integrals of periodic functions, as mentioned in the comment, where shifting the domain of integration by multiples of the period can simplify calculations.

### Dependencies
None explicitly listed in the provided information, but the proof uses:
- Arithmetic properties of real numbers
- The principle of mathematical induction
- Properties of integers

### Porting notes
When porting this theorem:
- Ensure that your system has appropriate definitions for real numbers, integer values, and periodicity
- The proof relies on straightforward induction over natural numbers, which should be readily available in most proof assistants
- The use of MESON_TAC suggests some automated reasoning, but the proof structure is direct enough that it could be replicated with standard tactics in other systems

---

## HAS_REAL_INTEGRAL_OFFSET

### HAS_REAL_INTEGRAL_OFFSET
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_OFFSET = prove
 (`!f i a b c. (f has_real_integral i) (real_interval[a,b])
                ==> ((\x. f(x + c)) has_real_integral i)
                    (real_interval[a - c,b - c])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `c:real`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_LID; REAL_INV_1] THEN
  REWRITE_TAC[REAL_ABS_1; REAL_MUL_LID; REAL_INV_1] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_REAL_INTERVAL; EXISTS_REFL;
              REAL_ARITH `x - c:real = y <=> x = y + c`] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any function $f$, real number $i$, and real numbers $a$, $b$, and $c$:

If the function $f$ has a real integral $i$ over the interval $[a,b]$, then the translated function $f(x+c)$ has the same real integral $i$ over the interval $[a-c,b-c]$.

Formally:
$$\forall f,i,a,b,c.\ (f \text{ has_real_integral } i)([a,b]) \Rightarrow ((\lambda x.\ f(x+c)) \text{ has_real_integral } i)([a-c,b-c])$$

### Informal proof
The proof shows that translating a function by $c$ and shifting the integration interval by the same amount preserves the value of the integral:

1. We apply the theorem `HAS_REAL_INTEGRAL_AFFINITY` with the specific values $1$ and $c$ as parameters and simplify.
   - `HAS_REAL_INTEGRAL_AFFINITY` deals with affine transformations of the form $f(mx + c)$
   - By setting $m=1$, we get exactly the translation we need

2. After rewriting with basic arithmetic rules (like $1 \cdot x = x$ and $|1| = 1$), we need to show the resulting intervals are equivalent.

3. The proof argues that the image of $[a-c,b-c]$ under the mapping $x \mapsto x+c$ is exactly $[a,b]$, which means integrating $f(x)$ over $[a,b]$ is equivalent to integrating $f(x+c)$ over $[a-c,b-c]$.

4. The final step uses real arithmetic to verify that the intervals indeed correspond correctly.

### Mathematical insight
This theorem formalizes the intuitive idea that translating a function and shifting its integration interval by the same amount preserves the value of the integral. This is a standard property in calculus, often applied when making substitutions in integrals.

The principle is commonly known as the "change of variables" or "substitution rule" in integration. Specifically, this theorem represents the case of a simple translation $u = x + c$ (or equivalently, $x = u - c$).

The result is important because it allows us to standardize integration problems by shifting the intervals or functions as needed, simplifying many calculations and proofs about integrals.

### Dependencies
- `HAS_REAL_INTEGRAL_AFFINITY`: Theorem about how affine transformations affect real integrals
- Various arithmetic rewrite rules and tactics

### Porting notes
When porting this theorem:
- Ensure your system has a corresponding notion of real integrals
- The translation of functions (shifting by a constant) should be straightforward in most systems
- Most of the complexity is in the real arithmetic reasoning, which may require different tactics in other proof assistants, but the underlying mathematical principle is standard

---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f(x)) /\
        (f has_real_integral i) (real_interval[a,a+c])
        ==> (f has_real_integral i) (real_interval[b,b+c])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
    (MP_TAC o SPEC `a - b:real` o MATCH_MP HAS_REAL_INTEGRAL_OFFSET) THEN
  REWRITE_TAC[REAL_ARITH
   `a - (a - b):real = b /\ (a + c) - (a - b) = b + c`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + a - b:real`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all functions $f$, real number $i$, and real numbers $a$, $b$, and $c$:

If:
- $f$ is periodic with period $(b-a)$, i.e., $\forall x. f(x + (b - a)) = f(x)$
- $f$ has real integral $i$ over the interval $[a, a+c]$, i.e., $(f \text{ has\_real\_integral } i)(\text{real\_interval}[a, a+c])$

Then:
- $f$ has real integral $i$ over the interval $[b, b+c]$, i.e., $(f \text{ has\_real\_integral } i)(\text{real\_interval}[b, b+c])$

### Informal proof
We prove that if a function has a certain integral over an interval, then the same function has the same integral over another interval of the same length that is shifted by the period of the function.

- First, we apply the theorem `HAS_REAL_INTEGRAL_OFFSET` with offset $a-b$ to the hypothesis $(f \text{ has\_real\_integral } i)(\text{real\_interval}[a, a+c])$.

- This gives us that $(\lambda x. f(x + (a-b)))$ has real integral $i$ over the interval $[a-(a-b), (a+c)-(a-b)]$.

- Simplifying the interval bounds:
  - $a-(a-b) = b$
  - $(a+c)-(a-b) = b+c$

- So we have that $(\lambda x. f(x + (a-b)))$ has real integral $i$ over the interval $[b, b+c]$.

- Now we need to show that $f(x) = f(x + (a-b))$ for all $x$ in $[b, b+c]$.

- For any $x$, we know that $f(x + (b-a) + (a-b)) = f(x)$ by the periodicity of $f$.

- Simplifying: $f(x + (b-a) + (a-b)) = f(x + 0) = f(x)$.

- Therefore, by the theorem `HAS_REAL_INTEGRAL_EQ` (which says that if two functions are equal on an interval, they have the same integral on that interval), $f$ has real integral $i$ over $[b, b+c]$.

### Mathematical insight
This lemma demonstrates an important property of integrals of periodic functions: the integral of a periodic function over an interval of the same length as another interval will be the same, provided these intervals are separated by a multiple of the period.

This result is useful in Fourier analysis and when working with periodic functions in general. It allows us to shift the domain of integration by the period of the function without changing the value of the integral, which can simplify calculations involving periodic functions.

### Dependencies
- Theorems:
  - `HAS_REAL_INTEGRAL_OFFSET`: States that if $f$ has real integral $i$ over $[a,b]$, then $\lambda x. f(x+c)$ has real integral $i$ over $[a-c, b-c]$.
  - `HAS_REAL_INTEGRAL_EQ`: States that if two functions are equal on an interval, they have the same integral on that interval.
  - Various arithmetic simplification theorems (`REAL_ARITH`).

### Porting notes
When porting this theorem:
1. Ensure that your target system has equivalent theorems for shifting the domain of integration and for substituting equal functions in integrals.
2. The proof relies heavily on arithmetic simplification. Make sure your target system can handle these simplifcations or be prepared to prove the arithmetic facts explicitly.
3. Pay attention to how periodicity is formalized in the target system, as different systems may use different approaches to express periodicity of functions.

---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ &0 <= c /\ a + c <= b /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  let tac =
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on]; ASM_REAL_ARITH_TAC] in
  REPEAT STRIP_TAC THEN
  CONJUNCTS_THEN SUBST1_TAC
   (REAL_ARITH `a:real = (a + c) - c /\ b = (b + c) - c`) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_OFFSET THEN
  SUBGOAL_THEN
   `((f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[a,a+c]) /\
     (f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b])) /\
    ((f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b]) /\
     (f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[b,b+c]))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY tac THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN tac;
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c /\ d ==> e <=>
                  c /\ d ==> a /\ b ==> e`] HAS_REAL_INTEGRAL_COMBINE))) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; REAL_ADD_SYM]]);;
```

### Informal statement
For a function $f : \mathbb{R} \to \mathbb{R}$, let $i \in \mathbb{R}$ and $a, b, c \in \mathbb{R}$ be such that:
1. $f$ is periodic with period $b-a$, i.e., $\forall x. f(x + (b-a)) = f(x)$
2. $c \geq 0$
3. $a + c \leq b$
4. $f$ has real integral $i$ over the interval $[a,b]$

Then the function $g(x) = f(x+c)$ also has real integral $i$ over the interval $[a,b]$.

### Informal proof
The proof uses properties of real integrals and periodicity of the function to establish the result:

1. First, we divide the integral of $f$ over $[a,b]$ into two parts:
   - The integral of $f$ over $[a, a+c]$
   - The integral of $f$ over $[a+c, b]$

2. We also establish that:
   - The integral of $f$ over $[a+c, b]$ equals the integral of $f$ over $[a+c, b]$
   - The integral of $f$ over $[a, a+c]$ equals the integral of $f$ over $[b, b+c]$ (using the periodicity)

3. To prove the second claim above, we use `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA` which states that for a periodic function $f$ with period $b-a$, if $f$ has integral $i$ over $[a, a+c]$, then it also has integral $i$ over $[b, b+c]$.

4. Since $a+c \leq b$, the intervals $[a+c, b]$ and $[b, b+c]$ are well-defined.

5. Using `HAS_REAL_INTEGRAL_OFFSET`, we can relate the integral of $f(x+c)$ over $[a,b]$ to the integral of $f$ over $[(a+c)-c, (b+c)-c] = [a+c, b+c]$.

6. By `HAS_REAL_INTEGRAL_COMBINE`, since $f$ has the same integral over $[a+c, b]$ and $[b, b+c]$, and these intervals are adjacent, $f$ has integral $i$ over $[a+c, b+c]$.

7. Therefore, $f(x+c)$ has integral $i$ over $[a,b]$.

### Mathematical insight
This theorem extends properties of integrals for periodic functions. It shows that for a periodic function, shifting the function horizontally by some amount $c$ (where $0 \leq c \leq b-a$) preserves the integral over the interval $[a,b]$. This is particularly useful in Fourier analysis and when working with periodic functions in general.

The key insight is that the periodicity of the function allows us to "wrap around" the parts of the integral that would otherwise be shifted outside the original interval. The condition $a+c \leq b$ ensures that the shifted interval has a meaningful overlap with the original interval.

### Dependencies
- `HAS_REAL_INTEGRAL_OFFSET`: Relates the integral of $f$ over $[a,b]$ to the integral of $f(x+c)$ over $[a-c,b-c]$
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA`: Shows that for a periodic function with period $b-a$, if it has integral $i$ over $[a,a+c]$, then it also has integral $i$ over $[b,b+c]$
- `HAS_REAL_INTEGRAL_COMBINE`: Combines two adjacent interval integrals
- `REAL_INTEGRABLE_ON_SUBINTERVAL`: Establishes integrability on subintervals
- `HAS_REAL_INTEGRAL_INTEGRAL`: Relates the `has_real_integral` predicate to the `real_integral` function
- `HAS_REAL_INTEGRAL_UNIQUE`: Establishes uniqueness of integrals
- Various arithmetic and logical rules

### Porting notes
When porting this theorem, pay attention to:
1. How periodicity is defined in the target system
2. The representation of interval integrals
3. The handling of interval combinations and subdivisions
4. The formulation of the main result may need to be adapted to match the conventions of the target system for describing integrals of transformed functions

---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK

### HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ abs(c) <= b - a /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\x. (f:real->real)(--x)`; `i:real`;
                   `--b:real`; `--a:real`; `--c:real`]
          HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS) THEN
    ASM_REWRITE_TAC[REAL_NEG_ADD; HAS_REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x + (a - b):real`) THEN
    REWRITE_TAC[REAL_ARITH `--(--a - --b):real = a - b`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any real-valued function $f$, real value $i$, and real numbers $a$, $b$, and $c$:
- If $f$ is periodic with period $(b-a)$, i.e., $\forall x.\ f(x+(b-a)) = f(x)$,
- And $|c| \leq b-a$,
- And $f$ has a real integral $i$ over the interval $[a,b]$ (i.e., $\int_a^b f(x)\ dx = i$),

Then the shifted function $f(x+c)$ also has the same real integral $i$ over the interval $[a,b]$ (i.e., $\int_a^b f(x+c)\ dx = i$).

### Informal proof
The proof proceeds by case analysis on whether $c \geq 0$ or $c < 0$:

- **Case 1**: $c \geq 0$
  - We directly apply the theorem `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS`, which handles the case when the offset is non-negative.
  - We need to verify that $a + c \leq b$, which follows from $|c| \leq b-a$ and $c \geq 0$.

- **Case 2**: $c < 0$
  - We use a reflection trick. Define $g(x) = f(-x)$ and apply `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS` to $g$ with the interval $[-b,-a]$ and offset $-c$ (which is positive since $c < 0$).
  - First, we verify that $g$ is periodic with period $(-a)-(-b) = b-a$, the same as $f$.
    - For any $x$, $g(x+(b-a)) = f(-(x+(b-a))) = f(-x-(b-a))$
    - From the periodicity of $f$, we have $f(-x-(b-a)+(b-a)) = f(-x)$
    - Therefore $g(x+(b-a)) = g(x)$
  - Using `HAS_REAL_INTEGRAL_REFLECT`, we know that if $f$ has integral $i$ over $[a,b]$, then $g$ has integral $i$ over $[-b,-a]$.
  - We then check that $-b + (-c) \leq -a$, which is equivalent to $c \leq b-a$, which follows from our assumption.
  - Thus, $g(x+(-c))$ has integral $i$ over $[-b,-a]$.
  - Finally, we transform back to $f$ using the relation $g(x+(-c)) = f(-(x+(-c))) = f(-x+c)$.
  - By another application of `HAS_REAL_INTEGRAL_REFLECT`, we conclude that $f(x+c)$ has integral $i$ over $[a,b]$.

### Mathematical insight
This theorem extends the property of periodicity to integrals with shifted functions. It states that for a periodic function, shifting the function by any amount within its period does not change its integral over a full period. 

This result is valuable in Fourier analysis and the study of periodic functions, where it is common to shift functions without wanting to recalculate integrals. The theorem ensures that the integral remains invariant under shifts that don't exceed the period length.

The extension to allow negative shifts (compared to the positive-only version in `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS`) makes this theorem more generally applicable.

### Dependencies
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS`: The theorem for the case of non-negative offset
- `HAS_REAL_INTEGRAL_REFLECT`: Relates the integral of $f(x)$ over $[a,b]$ to the integral of $f(-x)$ over $[-b,-a]$

### Porting notes
When porting this theorem, it's important to:
1. Ensure the target system has the appropriate handling of periodicity and reflection for real integrals
2. Pay attention to how negative case is handled through reflection - this is a common technique in analysis proofs
3. Make sure the prerequisites about integrability and bounds are properly transferred

---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `b <= a \/ a < b`) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NULL_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. f(x + (b - a) * frac(c / (b - a)))) has_real_integral i)
    (real_interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a < b /\ (b - a) * f < (b - a) * &1
      ==> abs(b - a) * f <= b - a`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LMUL_EQ] THEN
    ASM_REWRITE_TAC[real_abs; FLOOR_FRAC];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `a < b ==> x + (b - a) * (c / (b - a) - f) =
                (x + c) + --f * (b - a)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; FLOOR]]);;
```

### Informal statement
For any function $f: \mathbb{R} \to \mathbb{R}$, real number $i$, and real numbers $a$, $b$, and $c$, if:
1. $f$ is periodic with period $b - a$, i.e., $\forall x. f(x + (b - a)) = f(x)$, and
2. $f$ has real integral $i$ over the interval $[a, b]$, i.e., $(f \text{ has\_real\_integral } i)(\text{real\_interval}[a,b])$,

then the function $g(x) = f(x + c)$ also has real integral $i$ over the interval $[a, b]$, i.e., $((\lambda x. f(x + c)) \text{ has\_real\_integral } i)(\text{real\_interval}[a,b])$.

### Informal proof
The proof proceeds as follows:

- We first consider two cases: $b \leq a$ or $a < b$.
  
- In the case where $b \leq a$, the interval $[a, b]$ is either empty or a singleton, making the integral trivially equal to 0. This is handled by `HAS_REAL_INTEGRAL_NULL_EQ`.

- For the non-trivial case where $a < b$:
  1. We first show that $f(x + (b-a) \cdot \text{frac}(\frac{c}{b-a}))$ has real integral $i$ over $[a,b]$, where $\text{frac}(y)$ is the fractional part of $y$.
     - We use `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`, which requires that $|c'| \leq b-a$ for the offset $c'$.
     - Here, $c' = (b-a) \cdot \text{frac}(\frac{c}{b-a})$, and we verify that $|c'| \leq b-a$ because $0 \leq \text{frac}(y) < 1$ for any $y$.
  
  2. Next, we show that $f(x + (b-a) \cdot \text{frac}(\frac{c}{b-a})) = f(x + c)$ for all $x$ in the relevant domain.
     - We use the fact that $\text{frac}(y) = y - \text{floor}(y)$ to rewrite:
       $x + (b-a) \cdot \text{frac}(\frac{c}{b-a}) = (x + c) + (-\text{floor}(\frac{c}{b-a})) \cdot (b-a)$
     - Since $f$ is periodic with period $b-a$, and $\text{floor}(\frac{c}{b-a})$ is an integer, we can use `REAL_PERIODIC_INTEGER_MULTIPLE` to show that adding $-\text{floor}(\frac{c}{b-a}) \cdot (b-a)$ doesn't change the value of $f$.
     - Therefore, $f(x + (b-a) \cdot \text{frac}(\frac{c}{b-a})) = f(x + c)$.
  
  3. By the extensional equality of functions and `HAS_REAL_INTEGRAL_EQ`, the integral of $f(x + c)$ over $[a,b]$ equals $i$.

### Mathematical insight
This theorem extends the property of integrals of periodic functions. If a function is periodic with period $p$, then shifting the function by any amount $c$ (not just by the period) does not change the integral over an interval of length exactly $p$. This is because the "excess" part that's shifted out of the interval on one side reappears on the other side due to periodicity.

The key insight is how the proof handles arbitrary offsets by decomposing them into an integer multiple of the period plus a remainder. The periodicity handles the integer multiple part automatically, and the remainder is handled by `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`.

This result is useful in Fourier analysis and when working with periodic functions generally, as it allows for flexible manipulation of integrals involving shifts of periodic functions.

### Dependencies
- Theorems:
  - `REAL_PERIODIC_INTEGER_MULTIPLE`: Establishes that a function is periodic with period $a$ if and only if it returns the same value when the input is shifted by any integer multiple of $a$.
  - `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`: A restricted version of this theorem that requires the offset to be bounded by the period.
  - `HAS_REAL_INTEGRAL_NULL_EQ` (not in the dependency list): Handles the case of integration over null intervals.
  - `HAS_REAL_INTEGRAL_EQ` (not in the dependency list): States that functions that are equal on the domain of integration have the same integral.

### Porting notes
- The theorem relies on the `frac` function (fractional part) and `floor` function, which would need to be properly defined in the target system.
- The concept of "has_real_integral" will need to be defined appropriately in the target system, potentially requiring adaptation from HOL Light's specific formulation.
- The proof uses quite a bit of automation via tactics like `ASM_SIMP_TAC` and `REAL_ARITH`, which may need to be replaced with more explicit reasoning in systems with different automation capabilities.

---

## REAL_INTEGRABLE_PERIODIC_OFFSET

### Name of formal statement
REAL_INTEGRABLE_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_PERIODIC_OFFSET]);;
```

### Informal statement
For all real-valued functions $f$, real numbers $a$, $b$, and $c$, if:
1. $f$ is periodic with period $(b-a)$, i.e., $\forall x. f(x + (b-a)) = f(x)$, and
2. $f$ is integrable on the interval $[a,b]$,

then the function $g(x) = f(x+c)$ is also integrable on the interval $[a,b]$.

### Informal proof
The proof follows directly from the definition of real integrability and a previous result about periodic functions with offset.

First, we rewrite the goal using the definition of `real_integrable_on`, which reduces the problem to showing that there exists some value $i$ such that $f$ has a real integral equal to $i$ on the interval $[a,b]$.

Then, we apply the theorem `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`, which states that if $f$ has period $(b-a)$ and has a real integral $i$ on $[a,b]$, then the function $\lambda x. f(x+c)$ also has the same real integral $i$ on $[a,b]$.

The result follows immediately from these facts.

### Mathematical insight
This theorem establishes that horizontal shifts preserve integrability for periodic functions. This is an important property because it shows that if we integrate a periodic function over a full period, we can start the integration at any point and still maintain integrability.

The key insight is that for periodic functions, a horizontal shift doesn't change the "content" of what's being integrated over a full period interval - it just rearranges where the features of the function appear within that interval. Since integration is invariant to such rearrangements (as long as we integrate over a complete period), the shifted function remains integrable.

This result is particularly useful in Fourier analysis and when working with trigonometric functions, where periodic functions and their integrals are fundamental.

### Dependencies
#### Theorems
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET` - Shows that if a periodic function has a real integral on an interval, then a horizontally shifted version of the function has the same integral.

#### Definitions
- `real_integrable_on` - Defines what it means for a function to be integrable on an interval.

### Porting notes
When porting this theorem:
1. Ensure that the target system has a corresponding definition of integrability.
2. The porting of `HAS_REAL_INTEGRAL_PERIODIC_OFFSET` is a prerequisite.
3. The proof is straightforward and relies mostly on applying the definition of integrability and using the dependent theorem.

---

## ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `f:real->real` (SPEC_ALL REAL_INTEGRABLE_PERIODIC_OFFSET)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
For any function $f : \mathbb{R} \to \mathbb{R}$, real numbers $a$, $b$, and $c$, if:
- $f$ is periodic with period $b-a$, i.e., $\forall x. f(x + (b - a)) = f(x)$
- $f$ is absolutely integrable on the interval $[a,b]$

then the shifted function $x \mapsto f(x + c)$ is also absolutely integrable on the interval $[a,b]$.

### Informal proof
This theorem follows directly from the corresponding result for regular (non-absolute) integrability.

1. First, we unfold the definition of `absolutely_real_integrable_on`.
2. We then apply the theorem `REAL_INTEGRABLE_PERIODIC_OFFSET` which states that if $f$ is periodic with period $b-a$ and is integrable on $[a,b]$, then any shifted version $x \mapsto f(x + c)$ is also integrable on $[a,b]$.
3. Since absolute integrability means that both $f$ and $|f|$ are integrable, and shifting preserves integrability for periodic functions, the result follows.

### Mathematical insight
This theorem extends the property of preserving integrability under shifts to the case of absolute integrability. It is a natural extension of `REAL_INTEGRABLE_PERIODIC_OFFSET` and is useful in Fourier analysis and when working with periodic functions. 

The key insight is that shifting a periodic function doesn't change its integrability properties on an interval of length equal to the period. This makes sense intuitively because shifting a periodic function essentially rearranges the same values over the interval.

This result is particularly important when considering absolutely integrable functions, which are relevant for many convergence theorems in analysis and for defining certain function spaces like $L^1$.

### Dependencies
#### Theorems
- `REAL_INTEGRABLE_PERIODIC_OFFSET`: If $f$ is periodic with period $b-a$ and integrable on $[a,b]$, then $x \mapsto f(x + c)$ is also integrable on $[a,b]$.

#### Definitions
- `absolutely_real_integrable_on`: A function is absolutely integrable on an interval if both the function itself and its absolute value are integrable on that interval.

### Porting notes
When porting this theorem, ensure that:
1. The definition of absolute integrability matches the HOL Light definition
2. The dependency `REAL_INTEGRABLE_PERIODIC_OFFSET` is ported first
3. Be aware that different proof assistants may have different ways of representing periodic functions and intervals

---

## REAL_INTEGRAL_PERIODIC_OFFSET

### REAL_INTEGRAL_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> real_integral (real_interval[a,b]) (\x. f(x + c)) =
            real_integral (real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;
```

### Informal statement
For any function $f$, real numbers $a$, $b$, and $c$, if:
- $f$ is periodic with period $(b-a)$, i.e., $\forall x. f(x + (b-a)) = f(x)$, and
- $f$ is integrable on the interval $[a,b]$,

then the integral of the shifted function equals the original integral:
$$\int_{[a,b]} f(x+c) \, dx = \int_{[a,b]} f(x) \, dx$$

### Informal proof
The proof shows that shifting a periodic function by any amount preserves its integral over a full period interval:

1. First, we apply `REAL_INTEGRAL_UNIQUE`, which states that if two functions have the same integral on a given interval, then their integral values are equal.

2. Next, we apply `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`, which states that if $f$ has period $(b-a)$ and has real integral $i$ on $[a,b]$, then the function $\lambda x. f(x+c)$ also has real integral $i$ on $[a,b]$.

3. Finally, we use `GSYM HAS_REAL_INTEGRAL_INTEGRAL` to connect the `has_real_integral` relation with the `real_integral` function, ensuring that our result applies to the proper integral values.

This proof shows that for periodic functions, shifting by any amount preserves the integral value over a complete period interval.

### Mathematical insight
This theorem establishes an important invariance property of integrals of periodic functions: the integral value over a full period is preserved under arbitrary shifts of the function. This is particularly useful in Fourier analysis and when dealing with periodic phenomena.

The result is intuitive when thinking geometrically: shifting a periodic function doesn't change its "area" over a complete period. This is because what "leaves" the integration interval on one end "enters" at the other end in exactly the same amount, due to the periodicity.

This theorem helps simplify calculations with periodic functions by allowing arbitrary shifts without affecting integral values, which is especially useful in applications like signal processing and differential equations with periodic solutions.

### Dependencies
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`: States that for a periodic function with period $(b-a)$, if $f$ has real integral $i$ on $[a,b]$, then $\lambda x. f(x+c)$ has the same integral on the same interval.
- `REAL_INTEGRAL_UNIQUE`: Ensures uniqueness of the integral value.
- `HAS_REAL_INTEGRAL_INTEGRAL`: Connects the `has_real_integral` relation to the `real_integral` function.

### Porting notes
When porting this theorem:
- Make sure your target system has a well-developed theory of real analysis, particularly concerning integration.
- Be aware of how the target system handles function shifts and periodicity.
- The notion of "integrable" might have different formulations in different systems, but the core mathematical idea remains the same.

---

## FOURIER_OFFSET_TERM

### FOURIER_OFFSET_TERM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_OFFSET_TERM = prove
 (`!f n t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           (!x. f(x + &2 * pi) = f x)
           ==> fourier_coefficient (\x. f(x + t)) (2 * n + 2) *
               trigonometric_set (2 * n + 2) (&0) =
               fourier_coefficient f (2 * n + 1) *
               trigonometric_set (2 * n + 1) t +
               fourier_coefficient f (2 * n + 2) *
               trigonometric_set (2 * n + 2) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[trigonometric_set; fourier_coefficient;
              orthonormal_coefficient] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; COS_0; REAL_MUL_RID] THEN
  REWRITE_TAC[l2product] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; GSYM REAL_INTEGRAL_RMUL;
                FOURIER_PRODUCTS_INTEGRABLE_STRONG; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_COS_COS] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_ADD o
     rand o rand o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
       EXISTS_TAC `(:real)` THEN
       REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
       MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
       REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
       SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
       REWRITE_TAC[trigonometric_set; real_div] THEN
       REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
       ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
       REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
       MATCH_MP_TAC(REAL_ARITH
        `abs x <= &1 /\ abs y <= &1 ==> abs((x + y) / &2) <= &1`) THEN
       REWRITE_TAC[SIN_BOUND; COS_BOUND; REAL_ABS_NEG]]);
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   `(cm - cp) / &2 * f + (cm + cp) / &2 * f = cm * f`] THEN
  MP_TAC(ISPECL
   [`\x. cos(&(n + 1) * (x - t)) * f x`;
    `real_integral (real_interval[--pi,pi])
                   (\x. cos(&(n + 1) * (x - t)) * f x)`;
    `--pi`; `pi`; `t:real`] HAS_REAL_INTEGRAL_PERIODIC_OFFSET) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. cos (&(n + 1) * (x - t)) * f x) real_integrable_on
    real_interval[--pi,pi]`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
      SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
      REWRITE_TAC[trigonometric_set; real_div] THEN
      REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
      ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[COS_BOUND]];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `n * ((x + &2 * pi) - t) = (&2 * n) * pi + n * (x - t)`] THEN
    REWRITE_TAC[COS_ADD; SIN_NPI; COS_NPI; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_MUL_LZERO; EVEN_MULT; ARITH] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_SUB_RZERO; REAL_MUL_LID];
    REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = a * c * b`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For any function $f$ that is absolutely integrable on $[-\pi, \pi]$ and $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$), and for any natural number $n$ and real number $t$, the following relationship holds between Fourier coefficients of $f$ and its translation $f(\cdot + t)$:

$$\begin{align}
& \text{fourier\_coefficient}(x \mapsto f(x + t))(2n + 2) \cdot \text{trigonometric\_set}(2n + 2)(0) \\
&= \text{fourier\_coefficient}(f)(2n + 1) \cdot \text{trigonometric\_set}(2n + 1)(t) \\
&+ \text{fourier\_coefficient}(f)(2n + 2) \cdot \text{trigonometric\_set}(2n + 2)(t)
\end{align}$$

where:
- $\text{fourier\_coefficient}$ represents the coefficients in a Fourier series expansion
- $\text{trigonometric\_set}$ represents the orthonormal basis functions in the Fourier series

### Informal proof
The proof establishes how the Fourier coefficients of a shifted function relate to the original function's coefficients.

- We start by expanding the definitions of the trigonometric set and Fourier coefficients:
  - $\text{trigonometric\_set}(0)(x) = \frac{\cos(0 \cdot x)}{\sqrt{2\pi}}$
  - $\text{trigonometric\_set}(2n+1)(x) = \frac{\sin((n+1) \cdot x)}{\sqrt{\pi}}$
  - $\text{trigonometric\_set}(2n+2)(x) = \frac{\cos((n+1) \cdot x)}{\sqrt{\pi}}$
  - $\text{fourier\_coefficient} = \text{orthonormal\_coefficient}([-\pi,\pi])(\text{trigonometric\_set})$
  - $\text{orthonormal\_coefficient}(s)(w)(f)(n) = \text{l2product}(s)(w(n))(f)$
  - $\text{l2product}(s)(f)(g) = \int_s f(x)g(x)dx$

- We substitute these definitions and simplify. Since $\cos(0) = 1$, $\text{trigonometric\_set}(2n+2)(0) = \frac{1}{\sqrt{\pi}}$.

- Using trigonometric identities for products of sine and cosine functions:
  $$\cos(a)\cos(b) = \frac{\cos(a-b) + \cos(a+b)}{2}$$
  $$\cos(a)\sin(b) = \frac{\sin(a+b) - \sin(a-b)}{2}$$

- We express the integrand in terms of these products and apply the distributive property of integration.

- A key step uses the fact that for a periodic function with a translation, the integral over a full period remains invariant:
  $$\int_{-\pi}^{\pi} \cos((n+1)(x-t))f(x)dx = \int_{-\pi}^{\pi} \cos((n+1)x)f(x+t)dx$$

- This follows from the $2\pi$-periodicity of $f$ and the properties of cosine functions.

- By combining these results and applying the necessary algebraic manipulations, we arrive at the desired equality.

### Mathematical insight
This theorem establishes a fundamental relationship between the Fourier coefficients of a function and its shifted version. It shows how a translation in the time/space domain affects the coefficients in the frequency domain.

The result is particularly important for understanding how shifting a function manifests in its Fourier series representation. It demonstrates that time/space shifts correspond to specific phase shifts in the frequency domain, which is a core principle in Fourier analysis.

This relationship is crucial for applications in signal processing, differential equations, and other fields where the behavior of functions under translations needs to be analyzed in the frequency domain.

### Dependencies
- Definitions:
  - `l2product`: Inner product in L2 space
  - `orthonormal_coefficient`: Coefficient with respect to an orthonormal basis
  - `fourier_coefficient`: Coefficient in a Fourier series expansion

- Theorems:
  - `trigonometric_set`: Definition of the trigonometric basis functions
  - `ODD_EVEN_INDUCT_LEMMA`: Induction principle for even and odd numbers
  - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Integrability of products of a function with trigonometric functions
  - `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`: Integration of shifted periodic functions

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined notion of Fourier coefficients and trigonometric basis functions.
2. The proof relies heavily on properties of periodic functions and trigonometric identities, which should be available in most theorem provers.
3. The handling of integrability conditions and the measurability of functions may differ across systems.
4. Pay attention to how orthonormal bases are represented in the target system, as the definition approach may vary.

---

## FOURIER_SUM_OFFSET

### FOURIER_SUM_OFFSET
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..2*n) (\k. fourier_coefficient (\x. f (x + t)) k *
                             trigonometric_set k (&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[fourier_coefficient; trigonometric_set; l2product;
                orthonormal_coefficient; REAL_MUL_LZERO; COS_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`\x:real. &1 / sqrt(&2 * pi) * f x`;
                  `--pi`; `pi`; `t:real`] REAL_INTEGRAL_PERIODIC_OFFSET) THEN
    ASM_SIMP_TAC[REAL_ARITH `pi - --pi = &2 * pi`; REAL_INTEGRABLE_LMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
  SUBGOAL_THEN `1..2*n = 2*0+1..(2*(n-1)+1)+1` SUBST1_TAC THENL
   [BINOP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; SUM_PAIR] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN
  ASM_SIMP_TAC[GSYM FOURIER_OFFSET_TERM] THEN
  REWRITE_TAC[trigonometric_set; REAL_MUL_RZERO; COS_0; SIN_0] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For a function $f$ that is absolutely integrable on $[-\pi, \pi]$ and periodic with period $2\pi$ (i.e., $f(x + 2\pi) = f(x)$ for all $x$), and for any real number $t$ and natural number $n$:

$$\sum_{k=0}^{2n} c_k(f) \cdot \psi_k(t) = \sum_{k=0}^{2n} c_k(f_t) \cdot \psi_k(0)$$

where:
- $c_k(f)$ is the $k$-th Fourier coefficient of $f$, defined as the inner product of $f$ with the $k$-th trigonometric basis function on $[-\pi, \pi]$
- $\psi_k$ is the $k$-th trigonometric basis function
- $f_t$ is the function defined by $f_t(x) = f(x + t)$

This theorem states that shifting a function by $t$ in its argument corresponds to evaluating the trigonometric basis at $t$ in the Fourier expansion.

### Informal proof
The proof proceeds by induction and algebraic manipulation of the Fourier series terms:

1. First, we split the sum using `SUM_CLAUSES_LEFT` to separate the $k=0$ term from the rest.

2. For the $k=0$ term:
   - We use the definition of Fourier coefficients, trigonometric basis functions, and inner products
   - The coefficient $c_0(f)$ involves the integral $\int_{-\pi}^{\pi} \frac{1}{\sqrt{2\pi}} f(x) dx$
   - We apply the `REAL_INTEGRAL_PERIODIC_OFFSET` theorem to show that shifting $f$ by $t$ doesn't change this integral since $f$ is $2\pi$-periodic

3. For the remaining terms ($k \geq 1$):
   - We handle the case where $n = 0$ separately, which is trivial
   - For $n > 0$, we reorganize the sum using `SUM_PAIR` to group terms by parity
   - We apply the `FOURIER_OFFSET_TERM` theorem which relates the Fourier coefficients of the shifted function to the original coefficients
   - The theorem specifically tells us that:
     $$c_{2n+2}(f_t) \cdot \psi_{2n+2}(0) = c_{2n+1}(f) \cdot \psi_{2n+1}(t) + c_{2n+2}(f) \cdot \psi_{2n+2}(t)$$
   
4. Using the properties of trigonometric functions (notably that $\sin(0) = 0$ and $\cos(0) = 1$), we simplify the expressions and complete the proof with arithmetic reasoning.

### Mathematical insight
This theorem is a formal statement of a fundamental property of Fourier series: the relationship between time-shifting a function and phase-shifting its Fourier coefficients. When we shift a function by $t$, the effect on its Fourier expansion is to multiply each basis function by a corresponding phase factor.

This relationship is a discrete analog of the time-shifting property in Fourier transforms: if $F(ω)$ is the Fourier transform of $f(t)$, then the transform of $f(t-t_0)$ is $e^{-iωt_0}F(ω)$.

The theorem is important for understanding how translations in the time domain affect the frequency domain representation, which has applications in signal processing, differential equations, and harmonic analysis.

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Defines the trigonometric basis functions
  - `REAL_INTEGRAL_PERIODIC_OFFSET`: Shows that the integral of a periodic function is invariant under shifts
  - `FOURIER_OFFSET_TERM`: Relates Fourier coefficients of shifted functions to original coefficients

- **Definitions**:
  - `l2product`: Defines the L² inner product between functions
  - `orthonormal_coefficient`: Defines the projection coefficient onto an orthonormal basis
  - `fourier_coefficient`: Specifically defines Fourier coefficients using the trigonometric basis

### Porting notes
When porting this theorem:
1. Ensure your system has a proper representation of Fourier series and trigonometric basis functions
2. The coefficient indexing scheme is important - HOL Light uses a specific indexing where even indices correspond to cosine terms and odd indices to sine terms
3. The handling of absolute integrability might differ between systems
4. Take care with the notion of function equality, especially for shifted functions

---

## FOURIER_SUM_OFFSET_UNPAIRED

### FOURIER_SUM_OFFSET_UNPAIRED
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem (let ... = prove)

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_UNPAIRED = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                           trigonometric_set (2 * k) (&0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                   trigonometric_set (2 * k) (&0) +
                   fourier_coefficient (\x. f (x + t)) (2 * k + 1) *
                   trigonometric_set (2 * k + 1) (&0))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_PAIR] THEN
    REWRITE_TAC[GSYM ADD1; MULT_CLAUSES; SUM_CLAUSES_NUMSEG; LE_0];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL_0]] THEN
  REWRITE_TAC[ADD1; trigonometric_set; real_div; REAL_MUL_RZERO] THEN
  REWRITE_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;
```

### Informal statement
For any function $f$ and natural numbers $n$ and real number $t$, if:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$

Then the sum of Fourier coefficients multiplied by the trigonometric basis functions:
$$\sum_{k=0}^{2n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, t)$$

equals the sum:
$$\sum_{k=0}^{n} \text{fourier\_coefficient}(f(\cdot + t), 2k) \cdot \text{trigonometric\_set}(2k, 0)$$

This theorem shows how to express a Fourier sum evaluated at point $t$ in terms of the Fourier coefficients of the shifted function $f(x+t)$ evaluated at $0$, considering only the even-indexed terms.

### Informal proof
We prove this by applying the theorem `FOURIER_SUM_OFFSET` and then simplifying the resulting expression.

1. Apply `FOURIER_SUM_OFFSET` to transform the left-hand side sum:
   $$\sum_{k=0}^{2n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, t) = \sum_{k=0}^{2n} \text{fourier\_coefficient}(f(\cdot + t), k) \cdot \text{trigonometric\_set}(k, 0)$$

2. We then show this equals:
   $$\sum_{k=0}^{n} [\text{fourier\_coefficient}(f(\cdot + t), 2k) \cdot \text{trigonometric\_set}(2k, 0) + \text{fourier\_coefficient}(f(\cdot + t), 2k+1) \cdot \text{trigonometric\_set}(2k+1, 0)]$$

   This is done by grouping the terms in pairs using `SUM_PAIR`.

3. For the final step, we observe that:
   - By the definition of `trigonometric_set`, $\text{trigonometric\_set}(2k+1, 0) = \frac{\sin(0 \cdot (k+1))}{\sqrt{\pi}} = 0$
   - Therefore, the second term in each pair vanishes
   - This leaves us with only the even-indexed terms:
     $$\sum_{k=0}^{n} \text{fourier\_coefficient}(f(\cdot + t), 2k) \cdot \text{trigonometric\_set}(2k, 0)$$

### Mathematical insight
This theorem reveals a key property of Fourier series: evaluating a function's Fourier series at any point $t$ is equivalent to computing specific Fourier coefficients of the shifted function $f(\cdot + t)$. More specifically, it shows that we only need the even-indexed coefficients of the shifted function when evaluating at $0$.

This result demonstrates how translation in the function domain relates to the behavior of Fourier coefficients, which is fundamental in harmonic analysis and signal processing. The theorem enables more efficient computation of a Fourier series at arbitrary points by leveraging periodicity properties.

### Dependencies
- **Theorems**:
  - `FOURIER_SUM_OFFSET`: Relates the Fourier sum evaluated at $t$ to the Fourier coefficients of the shifted function.
  - `trigonometric_set`: Defines the orthonormal basis functions for the Fourier series.
  
- **Definitions**:
  - `fourier_coefficient`: Defined as the orthonormal coefficient with respect to the trigonometric basis.

### Porting notes
When implementing this in other systems:
- Ensure the trigonometric basis functions are defined with the same normalization factors (involving $\sqrt{\pi}$ and $\sqrt{2\pi}$).
- The result depends critically on the values of trigonometric functions at $0$ ($\sin(0) = 0$ and $\cos(0) = 1$).
- This theorem builds on the periodicity of the trigonometric functions and the definition of the Fourier coefficients, which might be implemented differently in other systems.

---

## dirichlet_kernel

### dirichlet_kernel
- dirichlet_kernel

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let dirichlet_kernel = new_definition
 `dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))`;;
```

### Informal statement
The Dirichlet kernel $D_n(x)$ is defined for a non-negative integer $n$ and real number $x$ as:

$$D_n(x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{if } x \neq 0
\end{cases}$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The Dirichlet kernel is a fundamental tool in Fourier analysis, particularly in studying the convergence properties of Fourier series. When a function $f(x)$ has a Fourier series, the $n$-th partial sum of this series can be expressed as the convolution of $f$ with the Dirichlet kernel.

The function has an important property that
$$D_n(x) = \sum_{j=-n}^{n} e^{ijx} = \sum_{j=-n}^{n} \cos(jx)$$

This makes it useful for analyzing the partial sums of Fourier series. The behavior of the Dirichlet kernel—especially its oscillation and the fact that its $L^1$ norm grows logarithmically with $n$—explains why Fourier series can behave poorly at points of discontinuity (Gibbs phenomenon) and why they may not converge pointwise for some $L^1$ functions.

### Dependencies
- None specific to this definition

### Porting notes
This definition is straightforward to port to other proof assistants. Care should be taken with:
1. The handling of division by zero (since $\sin(0/2) = 0$), which is explicitly handled by the conditional statement
2. The representation of rational numbers like $1/2$ in the target system
3. Ensuring the parameter $n$ is appropriately typed as a natural number or non-negative integer

---

## DIRICHLET_KERNEL_0

### Name of formal statement
DIRICHLET_KERNEL_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_0 = prove
 (`!x. abs(x) < &2 * pi ==> dirichlet_kernel 0 x = &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_kernel] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_SYM; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv(&2 * x) * x = inv(&2)`) THEN
  DISCH_TAC THEN SUBGOAL_THEN `~(x * inv(&2) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[] THEN MATCH_MP_TAC SIN_EQ_0_PI] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers $x$ such that $|x| < 2\pi$, the Dirichlet kernel of order 0 evaluated at $x$ equals $\frac{1}{2}$. Formally:

$$\forall x.\ |x| < 2\pi \Rightarrow \text{dirichlet\_kernel}(0, x) = \frac{1}{2}$$

### Informal proof
We need to prove that for any $x$ with $|x| < 2\pi$, we have $\text{dirichlet\_kernel}(0, x) = \frac{1}{2}$. 

First, let's use the definition of the Dirichlet kernel:
$$\text{dirichlet\_kernel}(n, x) = \begin{cases} 
n + \frac{1}{2} & \text{if}\ x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

The proof proceeds by cases:

* **Case 1**: If $x = 0$, then $\text{dirichlet\_kernel}(0, x) = 0 + \frac{1}{2} = \frac{1}{2}$.

* **Case 2**: If $x \neq 0$, then:
  $$\text{dirichlet\_kernel}(0, x) = \frac{\sin((0 + \frac{1}{2})x)}{2\sin(\frac{x}{2})} = \frac{\sin(\frac{x}{2})}{2\sin(\frac{x}{2})}$$
  
  Since we know $|x| < 2\pi$, we have $|\frac{x}{2}| < \pi$. This means $\sin(\frac{x}{2}) \neq 0$ because $\sin$ is only zero at integer multiples of $\pi$. 
  
  Therefore, we can simplify:
  $$\frac{\sin(\frac{x}{2})}{2\sin(\frac{x}{2})} = \frac{1}{2}$$

Thus, in both cases, $\text{dirichlet\_kernel}(0, x) = \frac{1}{2}$, which completes the proof.

### Mathematical insight
This theorem establishes the base case (order 0) for the Dirichlet kernel, which is a fundamental concept in Fourier analysis. The Dirichlet kernel appears when studying the partial sums of Fourier series. 

For $n = 0$, we discover that the kernel simplifies to the constant function $\frac{1}{2}$, regardless of the input value $x$ (within the range $|x| < 2\pi$). This provides a clean starting point for induction or recursion on the order of the Dirichlet kernel.

Understanding this base case is essential for analyzing the convergence behavior of Fourier series and the properties of convolution with Dirichlet kernels, which is a key topic in harmonic analysis.

### Dependencies
- **Definitions**:
  - `dirichlet_kernel`: The Dirichlet kernel defined as 
    ```
    dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))
    ```

### Porting notes
When porting this theorem:
1. Ensure proper treatment of real number literals (HOL Light uses `&` prefix for real literals)
2. The proof relies on the fact that sine function is zero only at integer multiples of π, so this fact should be available in the target system
3. Be careful with the condition $|x| < 2\pi$ - this ensures that $\sin(\frac{x}{2})$ is not zero in the denominator of the Dirichlet kernel

---

## DIRICHLET_KERNEL_NEG

### DIRICHLET_KERNEL_NEG
- `DIRICHLET_KERNEL_NEG`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_NEG = prove
 (`!n x. dirichlet_kernel n (--x) = dirichlet_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dirichlet_kernel; REAL_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; real_div; SIN_NEG;
                  REAL_INV_NEG; REAL_NEG_NEG]);;
```

### Informal statement
For all integers $n$ and real numbers $x$, the Dirichlet kernel is an even function:

$$D_n(-x) = D_n(x)$$

where $D_n(x)$ is the Dirichlet kernel defined as:

$$D_n(x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{if } x \neq 0
\end{cases}$$

### Informal proof
The proof shows that the Dirichlet kernel is an even function by directly applying the definition and properties of trigonometric functions.

We need to prove that $D_n(-x) = D_n(x)$ for all $n$ and $x$.

- First, we consider the case when $x = 0$:
  - When $x = 0$, we have $-x = 0$ as well
  - By definition, $D_n(0) = n + \frac{1}{2}$ and $D_n(-0) = n + \frac{1}{2}$
  - Therefore, $D_n(-x) = D_n(x)$ in this case

- Next, we consider the case when $x \neq 0$:
  - When $x \neq 0$, we have $-x \neq 0$ as well
  - By definition:
    $$D_n(-x) = \frac{\sin((n + \frac{1}{2})(-x))}{2\sin(\frac{-x}{2})}$$
  - Using the property that $\sin(-\theta) = -\sin(\theta)$, we get:
    $$D_n(-x) = \frac{-\sin((n + \frac{1}{2})x)}{2(-\sin(\frac{x}{2}))} = \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} = D_n(x)$$

Therefore, $D_n(-x) = D_n(x)$ for all $n$ and $x$, proving that the Dirichlet kernel is an even function.

### Mathematical insight
The Dirichlet kernel plays a crucial role in Fourier analysis, particularly in the study of Fourier series convergence. Its evenness property (being an even function) is important because:

1. It simplifies calculations in Fourier analysis, particularly when integrating against the kernel
2. It reflects the symmetry of the convergence behavior of Fourier series
3. It relates to the fact that the Dirichlet kernel is used to represent the partial sums of Fourier series

This evenness property is consistent with the broader pattern that many important kernels in Fourier analysis are even functions. Conceptually, this means the kernel treats positive and negative frequencies symmetrically, which is fundamental to how Fourier approximations work.

### Dependencies
- Definitions:
  - `dirichlet_kernel`: Defines the Dirichlet kernel function as described in the informal statement

### Porting notes
When porting this theorem:
- Pay attention to the handling of division by zero cases, which are explicitly excluded in the piecewise definition
- The proof relies on basic properties of trigonometric functions, especially $\sin(-x) = -\sin(x)$, which should be available in most proof assistants
- The definition of the Dirichlet kernel itself may need special attention to ensure the piecewise definition is properly handled

---

## DIRICHLET_KERNEL_CONTINUOUS_STRONG

### DIRICHLET_KERNEL_CONTINUOUS_STRONG
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (dirichlet_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  let lemma = prove
   (`f real_differentiable (atreal a) /\ f(a) = b
     ==> (f ---> b) (atreal a)`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      MATCH_MP REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN ASM_MESON_TAC[]) in
  SIMP_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
           REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[dirichlet_kernel] THEN ASM_CASES_TAC `x = &0` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `(\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2)))
      real_continuous atreal x`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_DIV THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REWRITE_TAC[NETLIMIT_ATREAL] THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
      REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `abs x` THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[EVENTUALLY_ATREAL; REAL_ARITH
     `&0 < abs(x - &0) <=> ~(x = &0)`] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LHOSPITAL THEN MAP_EVERY EXISTS_TAC
   [`\x. (&k + &1 / &2) * cos((&k + &1 / &2) * x)`;
    `\x. cos(x / &2)`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO] THEN REPEAT STRIP_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC COS_POS_PI) THEN
    MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_RZERO; SIN_0] THEN REAL_DIFFERENTIABLE_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; SIN_0] THEN
    REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_DIV_1] THEN
    MATCH_MP_TAC REALLIM_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
                real_div; COS_0; REAL_MUL_RID] THEN
    REAL_DIFFERENTIABLE_TAC]);;
```

### Informal statement
For all natural numbers $n$, the Dirichlet kernel function $\text{dirichlet\_kernel}(n)$ is real-continuous on the real interval $[-2\pi, 2\pi]$.

The Dirichlet kernel is defined as:
$$\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

### Informal proof
The proof shows that the Dirichlet kernel function is continuous at every point in the interval $[-2\pi, 2\pi]$.

First, we establish a lemma: if a function $f$ is real-differentiable at point $a$ and $f(a) = b$, then $f$ approaches $b$ at point $a$ (i.e., $f$ is continuous at $a$).

For the main proof:
1. We need to show that the Dirichlet kernel is continuous at every point $x \in [-2\pi, 2\pi]$.
2. We consider two cases:
   
   - **Case 1:** When $x = 0$
     At $x = 0$, we need to show that $\lim_{x \to 0} \frac{\sin((k + \frac{1}{2})x)}{2\sin(\frac{x}{2})} = k + \frac{1}{2}$
     We apply L'Hôpital's rule since both numerator and denominator approach 0 as $x$ approaches 0:
     * The derivative of the numerator is $(k + \frac{1}{2}) \cdot \cos((k + \frac{1}{2})x)$
     * The derivative of the denominator is $\cos(\frac{x}{2})$
     * Evaluating at $x = 0$: $\frac{(k + \frac{1}{2}) \cdot 1}{1} = k + \frac{1}{2}$
   
   - **Case 2:** When $x \neq 0$
     In this case, we need to show that $\frac{\sin((k + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$ is continuous at $x$.
     We use the fact that:
     * $\sin((k + \frac{1}{2})x)$ is continuous (as composition of continuous functions)
     * $\sin(\frac{x}{2})$ is continuous
     * $\sin(\frac{x}{2}) \neq 0$ for $x \in [-2\pi, 2\pi] \setminus \{0\}$ (because $\sin(y) = 0$ only when $y = n\pi$)
     * The quotient of continuous functions is continuous where the denominator is non-zero

Therefore, the Dirichlet kernel is continuous at every point in $[-2\pi, 2\pi]$.

### Mathematical insight
The Dirichlet kernel is fundamental in Fourier analysis, where it appears in the partial sums of Fourier series. Its continuity is a key property that is needed when studying the convergence behavior of Fourier series.

The interesting aspect of the proof is handling the singularity at $x = 0$, where both numerator and denominator approach 0. L'Hôpital's rule is applied to resolve this indeterminate form, showing that the function value at $x = 0$ agrees with the limit of the function as $x$ approaches 0, ensuring continuity.

The proof also demonstrates a standard technique for showing continuity of piecewise functions: verify continuity at each piece and ensure that the function values agree at the boundaries between pieces.

### Dependencies
- Definitions:
  - `dirichlet_kernel`: Defines the Dirichlet kernel function
  
- Used theorems (implicitly):
  - `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`: Real differentiability implies continuity
  - `SIN_EQ_0_PI`: Characterizes where the sine function equals zero
  - `COS_POS_PI`: Gives conditions for positivity of cosine
  - `LHOSPITAL`: L'Hôpital's rule for resolving limits with indeterminate forms

### Porting notes
When implementing this in other proof assistants, consider:
1. The piecewise definition of the Dirichlet kernel requires careful handling
2. L'Hôpital's rule implementation might vary across systems
3. The proof heavily relies on automatic differentiation tactics (`REAL_DIFFERENTIABLE_TAC`) which might need manual expansion in systems with less automation
4. The treatment of the singularity at $x=0$ requires careful analysis of the limit behavior

---

## DIRICHLET_KERNEL_CONTINUOUS

### Name of formal statement
DIRICHLET_KERNEL_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_CONTINUOUS = prove
 (`!n. (dirichlet_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the Dirichlet kernel function $\text{dirichlet\_kernel}(n)$ is real-continuous on the closed interval $[-\pi, \pi]$.

### Informal proof
This theorem is proven by showing that the Dirichlet kernel is continuous on a larger open interval and then using the fact that continuity is preserved under restriction to a subset.

The proof proceeds as follows:
* Apply the theorem `REAL_CONTINUOUS_ON_SUBSET` to show that if a function is continuous on a superset, it is continuous on a subset.
* Use the existing theorem `DIRICHLET_KERNEL_CONTINUOUS_STRONG` which states that the Dirichlet kernel is continuous on the open interval $(-2\pi, 2\pi)$.
* Show that $[-\pi, \pi]$ is a subset of $(-2\pi, 2\pi)$, which follows from the fact that $\pi > 0$.

### Mathematical insight
The Dirichlet kernel is a fundamental function in Fourier analysis, defined as:
$$\text{dirichlet\_kernel}(n)(x) = \begin{cases}
n + \frac{1}{2}, & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}, & \text{if } x \neq 0
\end{cases}$$

This theorem establishes the continuity of the Dirichlet kernel on the interval $[-\pi, \pi]$, which is essential for various applications in Fourier analysis, particularly in proving convergence properties of Fourier series. The continuity is a basic property needed in many theorems involving the Dirichlet kernel.

This result is simpler than `DIRICHLET_KERNEL_CONTINUOUS_STRONG` but is often the version needed in applications since $[-\pi, \pi]$ is the standard interval for Fourier analysis.

### Dependencies
- **Theorems**:
  - `DIRICHLET_KERNEL_CONTINUOUS_STRONG`: States that the Dirichlet kernel is continuous on the open interval $(-2\pi, 2\pi)$
  - `REAL_CONTINUOUS_ON_SUBSET`: If a function is continuous on a set A and B is a subset of A, then the function is continuous on B
  - `PI_POS`: States that $\pi > 0$

- **Definitions**:
  - `dirichlet_kernel`: Defines the Dirichlet kernel function

### Porting notes
When porting this theorem, ensure that:
1. The Dirichlet kernel is defined with the same case distinction for $x = 0$ and $x \neq 0$
2. The larger interval theorem `DIRICHLET_KERNEL_CONTINUOUS_STRONG` is ported first, as this theorem depends on it
3. The handling of real intervals (open vs. closed) might have different notation in other proof assistants

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. dirichlet_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;
```

### Informal statement
For all functions $f$ and natural numbers $n$, if $f$ is absolutely integrable on the real interval $[-\pi, \pi]$, then the product of the Dirichlet kernel $D_n(x)$ and $f(x)$ is also absolutely integrable on the real interval $[-\pi, \pi]$.

Here, the Dirichlet kernel $D_n(x)$ is defined as:
$$D_n(x) = \begin{cases} 
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

### Informal proof
The proof establishes that the product of the Dirichlet kernel and an absolutely integrable function is also absolutely integrable. This is done in two steps:

1. First, we apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`, which states that the product of an absolutely integrable function and a bounded measurable function is absolutely integrable.

2. To satisfy the conditions of this theorem, we need to show:
   - The Dirichlet kernel is measurable on $[-\pi, \pi]$. This follows from the fact that it is continuous on $[-\pi, \pi]$ (using `DIRICHLET_KERNEL_CONTINUOUS`), and continuous functions on closed sets are measurable (using `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`).
   
   - The Dirichlet kernel is bounded on $[-\pi, \pi]$. This follows from the fact that any continuous function on a compact set is bounded (using `REAL_COMPACT_IMP_BOUNDED` and `REAL_COMPACT_CONTINUOUS_IMAGE`). The interval $[-\pi, \pi]$ is compact (using `REAL_COMPACT_INTERVAL`).

Since both conditions are satisfied, the product $D_n(x) \cdot f(x)$ is absolutely integrable on $[-\pi, \pi]$.

### Mathematical insight
This theorem is an important step in the development of Fourier series theory. The Dirichlet kernel plays a crucial role in the study of Fourier series, as it appears in the convolution formula for partial sums of Fourier series.

Specifically, if $S_n(f)$ represents the $n$-th partial sum of the Fourier series for $f$, then:
$$S_n(f)(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(t) \cdot D_n(x-t) \, dt$$

Establishing that the product $D_n(x) \cdot f(x)$ is absolutely integrable ensures that this convolution is well-defined when $f$ is absolutely integrable, which is a standard assumption in Fourier analysis.

### Dependencies
- Theorems:
  - `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`: Establishes that the product of an absolutely integrable function and a bounded measurable function is absolutely integrable.
  - `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`: States that continuous functions on closed subsets are measurable.
  - `REAL_COMPACT_IMP_BOUNDED`: States that a function defined on a compact set is bounded.
  - `REAL_COMPACT_CONTINUOUS_IMAGE`: States that the continuous image of a compact set is compact.
  - `DIRICHLET_KERNEL_CONTINUOUS`: Proves that the Dirichlet kernel is continuous on $[-\pi, \pi]$.
  - `REAL_CLOSED_REAL_INTERVAL`: States that real intervals are closed.
  - `REAL_COMPACT_INTERVAL`: States that closed bounded real intervals are compact.

- Definitions:
  - `dirichlet_kernel`: Defines the Dirichlet kernel as described in the informal statement.

### Porting notes
When porting this theorem:
1. Ensure that the definition of absolute integrability in the target system matches HOL Light's definition.
2. The proof relies on properties of compact sets and continuous functions, which should be readily available in most proof assistants.
3. The definition of the Dirichlet kernel includes a case distinction for $x = 0$, which might need special handling in some systems.
4. The proof uses several general theorems about measurable functions and integration that should be available in any proof assistant with a well-developed real analysis library.

---

## COSINE_SUM_LEMMA

### Name of formal statement
COSINE_SUM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COSINE_SUM_LEMMA = prove
 (`!n x. (&1 / &2 + sum(1..n) (\k. cos(&k * x))) * sin(x / &2) =
         sin((&n + &1 / &2) * x) / &2`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
   [ASM_REWRITE_TAC[REAL_ADD_LID; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_RID; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
    REWRITE_TAC[REAL_MUL_COS_SIN; real_div; REAL_SUB_RDISTRIB] THEN
    SUBGOAL_THEN
     `!k x. &k * x + x * inv(&2) = (&(k + 1) * x - x * inv(&2))`
     (fun th -> REWRITE_TAC[th; SUM_DIFFS_ALT])
    THENL [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM real_div] THEN
    REWRITE_TAC[REAL_ARITH `&1 * x - x / &2 = x / &2`] THEN
    REWRITE_TAC[REAL_ARITH `(&n + &1) * x - x / &2 = (&n + &1 / &2) * x`] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any natural number $n$ and real number $x$, the following identity holds:
$$\left(\frac{1}{2} + \sum_{k=1}^{n} \cos(kx)\right) \cdot \sin\left(\frac{x}{2}\right) = \frac{\sin\left(\left(n + \frac{1}{2}\right) \cdot x\right)}{2}$$

This is a trigonometric identity relating a sum of cosines multiplied by a sine term to a single sine term.

### Informal proof
The proof proceeds by case analysis on the value of $n$:

**Case 1: $n = 0$**
* When $n = 0$, the sum $\sum_{k=1}^{n} \cos(kx)$ is empty, so it evaluates to $0$
* The left-hand side becomes $\frac{1}{2} \cdot \sin\left(\frac{x}{2}\right)$
* The right-hand side becomes $\frac{\sin\left(\frac{1}{2} \cdot x\right)}{2} = \frac{\sin\left(\frac{x}{2}\right)}{2}$
* These are equal, confirming the identity for $n = 0$

**Case 2: $n \geq 1$**
* Distribute the term $\sin\left(\frac{x}{2}\right)$ over the sum on the left-hand side
* Apply the trigonometric identity $\cos(a)\sin(b) = \frac{1}{2}[\sin(a+b) - \sin(a-b)]$ to each term
* This transforms the problem into manipulating sums of sine terms
* For each $k$, we have $kx + \frac{x}{2} = (k+1)x - \frac{x}{2}$
* Use the method of telescoping sums, where many terms cancel out
* After simplification and combining like terms, we get $\frac{\sin\left(\left(n+\frac{1}{2}\right)x\right)}{2}$ on the right-hand side
* The resulting expressions are equal, proving the identity

### Mathematical insight
This lemma provides a closed-form expression for a weighted sum of cosines in terms of a single sine function. It's a specific case of Dirichlet's kernel in Fourier analysis, which appears when studying the partial sums of Fourier series. The result allows for the simplification of certain trigonometric sums that would otherwise be unwieldy to compute directly.

Such trigonometric identities are valuable in various areas of mathematics including Fourier analysis, signal processing, and number theory. This particular form exhibits how a seemingly complex sum can collapse into a much simpler expression, which is often exploited in convergence proofs for Fourier series.

### Dependencies
No explicit dependencies identified in the provided information.

### Porting notes
When implementing this in other proof assistants:
- The proof relies heavily on trigonometric identities and algebraic manipulations
- Special attention should be paid to how real numbers and trigonometric functions are represented in the target system
- The case analysis structure (for $n=0$ and $n≥1$) should be preserved
- The telescoping sum technique is crucial for the proof and should be carefully implemented

---

## DIRICHLET_KERNEL_COSINE_SUM

### DIRICHLET_KERNEL_COSINE_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_COSINE_SUM = prove
 (`!n x. ~(x = &0) /\ abs(x) < &2 * pi
         ==> dirichlet_kernel n x = &1 / &2 + sum(1..n) (\k. cos(&k * x))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
  MATCH_MP_TAC(REAL_FIELD
    `~(y = &0) /\ z * y = x / &2 ==> x / (&2 * y) = z`) THEN
  REWRITE_TAC[COSINE_SUM_LEMMA] THEN
  MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any non-negative integer $n$ and real number $x$ such that $x \neq 0$ and $|x| < 2\pi$, the Dirichlet kernel satisfies:

$$\operatorname{dirichlet\_kernel}(n, x) = \frac{1}{2} + \sum_{k=1}^{n} \cos(k \cdot x)$$

### Informal proof
We need to show that for $x \neq 0$ and $|x| < 2\pi$, the Dirichlet kernel equals $\frac{1}{2}$ plus a sum of cosines.

Starting with the definition of the Dirichlet kernel, we have:
$$\operatorname{dirichlet\_kernel}(n, x) = \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$$
for $x \neq 0$.

We use the following steps:
1. Apply a field transformation: if $y \neq 0$ and $z \cdot y = \frac{x}{2}$, then $\frac{x}{2y} = z$.
2. Use the `COSINE_SUM_LEMMA` which states that:
   $$\left(\frac{1}{2} + \sum_{k=1}^{n} \cos(k \cdot x)\right) \cdot \sin\left(\frac{x}{2}\right) = \frac{\sin\left((n + \frac{1}{2})x\right)}{2}$$
3. Note that $\sin(\frac{x}{2}) \neq 0$ since $|x| < 2\pi$ and $x \neq 0$, which implies that $\frac{x}{2}$ is not a multiple of $\pi$.

Putting these together, we get:
$$\operatorname{dirichlet\_kernel}(n, x) = \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} = \frac{1}{2} + \sum_{k=1}^{n} \cos(k \cdot x)$$

### Mathematical insight
The Dirichlet kernel is a fundamental concept in Fourier analysis, particularly in the study of Fourier series. This theorem establishes the equivalence between two different representations of the Dirichlet kernel:
1. The fractional expression $\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$
2. The sum $\frac{1}{2} + \sum_{k=1}^{n} \cos(k \cdot x)$

This equivalence is important because it connects the geometric properties of the Dirichlet kernel (as a sum of cosines) with its analytic properties (as a ratio of sines). The Dirichlet kernel is used to approximate functions in Fourier analysis and appears in the convergence theory of Fourier series.

The restriction that $|x| < 2\pi$ ensures that $\sin(\frac{x}{2})$ is non-zero, which is necessary for the fractional representation to be well-defined.

### Dependencies
- Theorems:
  - `COSINE_SUM_LEMMA`: Shows that $(\frac{1}{2} + \sum_{k=1}^{n} \cos(k \cdot x)) \cdot \sin(\frac{x}{2}) = \frac{\sin((n + \frac{1}{2})x)}{2}$
  - `SIN_EQ_0_PI`: Characterizes when sine equals zero (at multiples of π)
  - `REAL_FIELD`: Field properties of real numbers
- Definitions:
  - `dirichlet_kernel`: Defined as $n + \frac{1}{2}$ when $x = 0$, and $\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$ otherwise

### Porting notes
When porting this theorem to other systems:
1. Ensure that the Dirichlet kernel is properly defined with the special case handling for $x = 0$
2. The proof relies on the `COSINE_SUM_LEMMA`, which should be ported first
3. The condition $|x| < 2\pi$ is crucial for ensuring that $\sin(\frac{x}{2}) \neq 0$, which might need to be explicitly proven in systems with stricter typing
4. In some systems, you might need to handle division more carefully, ensuring that denominators are non-zero

---

## HAS_REAL_INTEGRAL_DIRICHLET_KERNEL

### Name of formal statement
HAS_REAL_INTEGRAL_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL = prove
 (`!n. (dirichlet_kernel n has_real_integral pi) (real_interval[--pi,pi])`,
  GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `\x. &1 / &2 + sum(1..n) (\k. cos(&k * x))` THEN
  EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  SIMP_TAC[REAL_ARITH `&0 < pi /\ --pi <= x /\ x <= pi ==> abs(x) < &2 * pi`;
           DIRICHLET_KERNEL_COSINE_SUM; PI_POS] THEN
  SUBGOAL_THEN `pi = pi + sum(1..n) (\k. &0)` MP_TAC THENL
   [REWRITE_TAC[SUM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH  `pi = (&1 / &2) * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN MP_TAC PI_POS THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `k:num` HAS_REAL_INTEGRAL_COS_NX) THEN ASM_SIMP_TAC[LE_1]]);;
```

### Informal statement
For any natural number $n$, the Dirichlet kernel $D_n(x)$ has a real integral over the interval $[-\pi, \pi]$ equal to $\pi$:

$$\int_{-\pi}^{\pi} D_n(x) \, dx = \pi$$

where the Dirichlet kernel is defined as:

$$D_n(x) = \begin{cases}
n + \frac{1}{2}, & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}, & \text{if } x \neq 0
\end{cases}$$

### Informal proof
The proof proceeds by showing that the Dirichlet kernel can be expressed as a sum of cosines on most of the integration domain:

* First, we apply `HAS_REAL_INTEGRAL_SPIKE` which allows us to replace a function with an equivalent one except at a set of negligible measure (in this case, just at $x = 0$).

* We use `DIRICHLET_KERNEL_COSINE_SUM` which states that for any $x \neq 0$ with $|x| < 2\pi$:
  $$D_n(x) = \frac{1}{2} + \sum_{k=1}^{n} \cos(kx)$$

* Since the points in $[-\pi, \pi]$ satisfy $|x| < 2\pi$, this alternative representation of the Dirichlet kernel is valid except at $x = 0$.

* We rewrite the integral as:
  $$\int_{-\pi}^{\pi} D_n(x) \, dx = \int_{-\pi}^{\pi} \left(\frac{1}{2} + \sum_{k=1}^{n} \cos(kx)\right) \, dx$$

* We rewrite $\pi$ as $\pi + \sum_{k=1}^{n} 0$ to match the structure of the right side.

* Using linearity of integrals, we split the integral into:
  $$\int_{-\pi}^{\pi} \frac{1}{2} \, dx + \sum_{k=1}^{n} \int_{-\pi}^{\pi} \cos(kx) \, dx$$

* For the first term, $\int_{-\pi}^{\pi} \frac{1}{2} \, dx = \frac{1}{2} \cdot 2\pi = \pi$

* For each term in the sum, we use `HAS_REAL_INTEGRAL_COS_NX` which tells us that for each $k \geq 1$:
  $$\int_{-\pi}^{\pi} \cos(kx) \, dx = 0$$

* Therefore, the total integral equals $\pi + \sum_{k=1}^{n} 0 = \pi$

### Mathematical insight
The Dirichlet kernel is a fundamental function in Fourier analysis, used to approximate functions with their Fourier series. This theorem establishes a key property: its average value over a full period is $\pi/2\pi = 1/2$. 

The Dirichlet kernel behaves like a nascent delta function - as $n$ increases, it concentrates more mass near $x = 0$ while maintaining the same integral. This property makes it useful in proving convergence results for Fourier series.

The representation of the Dirichlet kernel as a sum of cosine functions plus a constant term is crucial for analyzing its behavior and is utilized extensively in this proof.

### Dependencies
- **Theorems:**
  - `HAS_REAL_INTEGRAL_COS_NX`: The integral of $\cos(nx)$ over $[-\pi, \pi]$ equals $2\pi$ if $n = 0$, and $0$ if $n \neq 0$
  - `DIRICHLET_KERNEL_COSINE_SUM`: Representation of Dirichlet kernel as a cosine sum: $D_n(x) = \frac{1}{2} + \sum_{k=1}^{n} \cos(kx)$ for $x \neq 0$ and $|x| < 2\pi$

- **Definitions:**
  - `dirichlet_kernel`: Definition of the Dirichlet kernel function

### Porting notes
When porting this theorem, be aware that:
1. The exact definition of the Dirichlet kernel is crucial and should match exactly
2. The proof relies on the properties of trigonometric integrals, specifically the orthogonality of cosines
3. The techniques used here (handling a point discontinuity with a "spike" lemma) may need different approaches in other systems
4. Some proof assistants might have different ways of handling the summation of integrals or differently formalized notions of negligible sets

---

## HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF

### HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF = prove
 (`!n. (dirichlet_kernel n has_real_integral (pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`dirichlet_kernel n`; `--pi`; `pi`; `&0`; `pi`]
        REAL_INTEGRABLE_SUBINTERVAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MESON_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL; real_integrable_on];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM HAS_REAL_INTEGRAL_REFLECT]) THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; ETA_AX; REAL_NEG_0] THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`dirichlet_kernel n`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `--pi`; `pi`; `&0`] HAS_REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_2] THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MATCH_MP_TAC(REAL_ARITH `x = pi ==> x = &2 * y ==> y = pi / &2`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]);;
```

### Informal statement
For all natural numbers $n$, the Dirichlet kernel $\text{dirichlet\_kernel}$ $n$ has a real integral equal to $\pi/2$ over the interval $[0, \pi]$.

Formally:
$$\forall n. \left(\int_{[0,\pi]} \text{dirichlet\_kernel}(n, x) \, dx = \frac{\pi}{2}\right)$$

Where the Dirichlet kernel is defined as:
$$\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

### Informal proof
The proof utilizes the fact that the integral of the Dirichlet kernel over $[-\pi, \pi]$ is $\pi$ (from `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`) and that the Dirichlet kernel is an even function (from `DIRICHLET_KERNEL_NEG`).

The proof proceeds as follows:

1. Start with the fact that the Dirichlet kernel is integrable over $[-\pi, \pi]$ with integral value $\pi$.
2. Show that the interval $[0, \pi]$ is a subinterval of $[-\pi, \pi]$, making the Dirichlet kernel integrable over $[0, \pi]$ as well.
3. Reflect the integral: since $\text{dirichlet\_kernel}(n, -x) = \text{dirichlet\_kernel}(n, x)$ (the Dirichlet kernel is an even function), the integral over $[-\pi, 0]$ equals the integral over $[0, \pi]$.
4. Combine the integrals over $[-\pi, 0]$ and $[0, \pi]$ to get the integral over $[-\pi, \pi]$:
   $$\int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \, dx = 2 \cdot \int_{[0, \pi]} \text{dirichlet\_kernel}(n, x) \, dx$$
5. Since we know the left side equals $\pi$, we have $\int_{[0, \pi]} \text{dirichlet\_kernel}(n, x) \, dx = \pi/2$.

### Mathematical insight
This theorem establishes the integral of the Dirichlet kernel over half the symmetric interval. Since the Dirichlet kernel is an even function, its integral over $[0, \pi]$ is exactly half of its integral over the full interval $[-\pi, \pi]$.

The Dirichlet kernel plays an important role in Fourier analysis and the theory of Fourier series. It represents the partial sum of a Fourier series for a function and approaches the Dirac delta function as $n$ approaches infinity. Understanding its integrable properties is fundamental for establishing convergence results in Fourier analysis.

### Dependencies
#### Theorems
- `DIRICHLET_KERNEL_NEG`: The Dirichlet kernel is an even function: $\text{dirichlet\_kernel}(n, -x) = \text{dirichlet\_kernel}(n, x)$
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`: The integral of the Dirichlet kernel over $[-\pi, \pi]$ equals $\pi$

#### Definitions
- `dirichlet_kernel`: Definition of the Dirichlet kernel function

### Porting notes
When porting this theorem:
1. Ensure your system has a solid foundation for real analysis, including definitions for integrals and the concept of "integrable functions"
2. Make sure the Dirichlet kernel is defined with exactly the same behavior at the singular point $x = 0$
3. The proof relies on symmetry properties and combining integrals over subintervals, which should be expressible in most proof assistants

---

## FOURIER_SUM_OFFSET_DIRICHLET_KERNEL

### FOURIER_SUM_OFFSET_DIRICHLET_KERNEL
- FOURIER_SUM_OFFSET_DIRICHLET_KERNEL

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) =
            real_integral (real_interval[--pi,pi])
                          (\x. dirichlet_kernel n x * f(x + t)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_UNPAIRED] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH] THEN
  REWRITE_TAC[trigonometric_set; COS_0; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `fourier_coefficient (\x. f(x + t)) 0 * &1 / sqrt(&2 * pi) +
    sum (1..n) (\k. fourier_coefficient (\x. f(x + t)) (2 * k) / sqrt pi)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1; REAL_MUL_RZERO; COS_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID;
              fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [GSYM REAL_MUL_ASSOC; GSYM REAL_INTEGRAL_RMUL; GSYM REAL_INTEGRAL_ADD;
    ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
    ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
    ABSOLUTELY_REAL_INTEGRABLE_LMUL;
    TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
    GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
    ABSOLUTELY_REAL_INTEGRABLE_RMUL;
    ABSOLUTELY_REAL_INTEGRABLE_SUM;
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{}:real->bool` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0; REAL_ARITH
   `a * b * c * b:real = (a * c) * b pow 2`] THEN
  SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE;
           REAL_LE_INV_EQ] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_ARITH
   `d * f * i = (&1 * f) * inv(&2) * i + y <=> i * f * (d - &1 / &2) = y`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. inv pi * f(x + t) * cos(&k * x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `x - &1 / &2 = y <=> x = &1 / &2 + y`] THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[dirichlet_kernel] THENL
     [REWRITE_TAC[REAL_MUL_RZERO; COS_0; SUM_CONST_NUMSEG; ADD_SUB] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ ~d /\ (~c ==> e)
                         ==> (a /\ b /\ c ==> d) ==> e`) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[REAL_FIELD
      `~(y = &0) ==> (x / (&2 * y) = z <=> z * y = x / &2)`] THEN
      REWRITE_TAC[COSINE_SUM_LEMMA]];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_RING
     `s * s:real = p ==> p * f * c = (c * s) * f * s`) THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; PI_POS_LE]]);;
```

### Informal statement
For a function $f$ that is absolutely integrable on the interval $[-\pi, \pi]$ and $2\pi$-periodic (i.e., $f(x+2\pi) = f(x)$ for all $x$), the following equality holds for any $n \geq 0$ and any real number $t$:

$$\sum_{k=0}^{2n} \hat{f}(k) \cdot \psi_k(t) = \frac{1}{\pi}\int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx$$

where:
- $\hat{f}(k)$ is the $k$-th Fourier coefficient of $f$
- $\psi_k(t)$ is the $k$-th trigonometric basis function evaluated at $t$
- $D_n(x)$ is the Dirichlet kernel of order $n$

### Informal proof
The proof establishes that the sum of trigonometric functions weighted by Fourier coefficients can be expressed as a convolution with the Dirichlet kernel. The proof proceeds as follows:

- First, we apply the `FOURIER_SUM_OFFSET_UNPAIRED` theorem to transform the sum into an equivalent form:
  $$\sum_{k=0}^{2n} \hat{f}(k) \cdot \psi_k(t) = \sum_{k=0}^{n} \hat{f_{t}}(2k) \cdot \psi_{2k}(0)$$
  where $\hat{f_t}(k)$ denotes the Fourier coefficient of the function $f(x+t)$.

- We split the sum by separating the $k=0$ term:
  $$\hat{f_t}(0) \cdot \psi_0(0) + \sum_{k=1}^{n} \hat{f_t}(2k) \cdot \psi_{2k}(0)$$

- We use the explicit form of the trigonometric basis functions:
  $$\psi_0(0) = \frac{1}{\sqrt{2\pi}}, \quad \psi_{2k}(0) = \frac{\cos(0)}{\sqrt{\pi}} = \frac{1}{\sqrt{\pi}}$$

- The Fourier coefficients are expressed as inner products using the trigonometric basis:
  $$\hat{f_t}(k) = \int_{-\pi}^{\pi} f(x+t) \cdot \psi_k(x) \, dx$$

- We establish that $f(x+t)$ is absolutely integrable on $[-\pi,\pi]$ using the periodicity of $f$.

- The key mathematical insight is to recognize that the sum can be written in terms of the Dirichlet kernel:
  $$D_n(x) = \frac{\sin((n+\frac{1}{2})x)}{2\sin(\frac{x}{2})}$$
  which can be expressed as $D_n(x) = \frac{1}{2} + \sum_{k=1}^{n} \cos(kx)$ for $x \neq 0$.

- Using various trigonometric identities and integral properties, we show that:
  $$\int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx = \pi \cdot \left(\hat{f_t}(0) \cdot \psi_0(0) + \sum_{k=1}^{n} \hat{f_t}(2k) \cdot \psi_{2k}(0)\right)$$

- Dividing both sides by $\pi$ completes the proof.

### Mathematical insight
The theorem provides a connection between the Fourier series and the convolution with the Dirichlet kernel. This insight is crucial in Fourier analysis as it relates the partial sums of a Fourier series to a convolution integral. 

The Dirichlet kernel $D_n(x)$ plays a central role in the convergence properties of Fourier series. When convolving a function with the Dirichlet kernel, the result approximates the original function, with the approximation improving as $n$ increases. This theorem provides a precise formula for that approximation in terms of the partial sums of the Fourier series.

In signal processing terms, the theorem shows how the sum of weighted frequency components (left side) can be expressed as a filtering operation in the time domain (right side).

### Dependencies
- **Theorems**:
  - `FOURIER_SUM_OFFSET_UNPAIRED`: Relates the Fourier sum to coefficients of the offset function
  - `TRIGONOMETRIC_SET_EVEN`: Provides the explicit form of even-indexed trigonometric basis functions
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that offset of a periodic integrable function remains integrable
  - `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`: Integrability of product with trigonometric functions
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: Integrability of product with Dirichlet kernel
  - `COSINE_SUM_LEMMA`: Relates sum of cosines to the Dirichlet kernel formula

- **Definitions**:
  - `fourier_coefficient`: The Fourier coefficient of a function
  - `trigonometric_set`: The trigonometric basis functions
  - `dirichlet_kernel`: The Dirichlet kernel definition
  - `l2product`: Inner product in L2 space
  - `orthonormal_coefficient`: Coefficient with respect to an orthonormal basis

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined notion of absolute integrability.
2. The proper definition of the Dirichlet kernel is crucial, including its behavior at $x=0$.
3. Trigonometric basis functions may be defined differently in other systems - pay attention to normalization factors.
4. Be prepared to establish various trigonometric identities that might be handled implicitly in HOL Light.
5. The handling of the "spike" at $x=0$ in the Dirichlet kernel may require special attention in other systems.

---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL

### FOURIER_SUM_LIMIT_DIRICHLET_KERNEL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x + t)))
             ---> pi * l) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  SUBGOAL_THEN `l = (l * pi) / pi`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[real_div; REALLIM_RMUL_EQ; PI_NZ; REAL_INV_EQ_0] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
The theorem states that for a function $f$ that:
1. Is absolutely real integrable on the interval $[-\pi, \pi]$
2. Is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$)

The following two limits are equivalent:

$$\lim_{n \to \infty} \sum_{k=0}^{n} \hat{f}(k) \cdot \phi_k(t) = l$$

if and only if

$$\lim_{n \to \infty} \int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx = \pi \cdot l$$

where:
- $\hat{f}(k)$ is the Fourier coefficient of $f$ for index $k$
- $\phi_k(t)$ is the $k$-th trigonometric basis function evaluated at $t$
- $D_n(x)$ is the Dirichlet kernel of order $n$

### Informal proof
The proof follows these steps:

1. First, we use `FOURIER_SUM_LIMIT_PAIR` to show the equivalence between the limit of the sum up to $n$ terms and the limit of the sum up to $2n$ terms. This step transforms our original sum formulation.

2. We then apply `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`, which allows us to express the finite Fourier sum in terms of an integral with the Dirichlet kernel:

   $$\sum_{k=0}^{2n} \hat{f}(k) \cdot \phi_k(t) = \frac{1}{\pi} \int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx$$

3. We perform an algebraic manipulation to rewrite $l$ as $\frac{l \cdot \pi}{\pi}$ using the fact that $\pi > 0$.

4. Finally, we apply the theorem about limits with constant factors, specifically that:

   $$\lim_{n \to \infty} a_n = L \iff \lim_{n \to \infty} c \cdot a_n = c \cdot L$$
   
   for any non-zero constant $c$, where we use $c = \frac{1}{\pi}$ and simplify the result using algebraic properties of multiplication.

### Mathematical insight
This theorem establishes a fundamental equivalence between two ways of expressing the convergence of Fourier series:

1. The first expression is the standard definition using the trigonometric basis functions and Fourier coefficients.
2. The second expression uses the Dirichlet kernel, which is the periodic sinc function that appears in the study of Fourier analysis.

The theorem is important because:
1. It connects the discrete sum representation of Fourier series with an integral representation via the Dirichlet kernel.
2. It provides a tool for analyzing convergence properties of Fourier series.
3. The Dirichlet kernel representation is often easier to manipulate for certain theoretical analyses.

This result is part of the foundational theory for classical Fourier analysis, particularly for studying pointwise convergence of Fourier series.

### Dependencies
- **Theorems**:
  - `FOURIER_SUM_LIMIT_PAIR`: Establishes equivalence between the limit of Fourier sums up to n terms and up to 2n terms
  - `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`: Connects the finite Fourier sum to an integral with the Dirichlet kernel
  - `trigonometric_set`: Defines the trigonometric basis functions for Fourier analysis

- **Definitions**:
  - `fourier_coefficient`: Defines Fourier coefficients in terms of orthonormal coefficients
  - `dirichlet_kernel`: Defines the Dirichlet kernel function

### Porting notes
When porting this theorem:
1. Ensure that the trigonometric basis functions and Fourier coefficients are defined consistently with HOL Light's definitions.
2. The Dirichlet kernel has a specific definition with a discontinuity at 0, which needs to be preserved.
3. The periodicity condition for functions might be handled differently in other systems, so take care to represent it correctly.
4. Pay attention to the theory of limits in the target system, as the equivalence between limits might be formalized differently.

---

## SIMPLE_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
SIMPLE_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIMPLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (\x. (f(x + t) - f(t)) / sin(x / &2))
        absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f(t)) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
               ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  MATCH_MP_TAC(TAUT `(a ==> c) /\ b ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FOURIER_COEFFICIENT_SUB; FOURIER_COEFFICIENT_CONST;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s:real = u /\ ft * t = x ==> (f0 - ft) * t + s = (f0 * t + u) - x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LE_1; ARITH; REAL_SUB_RZERO];
      REWRITE_TAC[trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
      MATCH_MP_TAC(REAL_FIELD `&0 < s ==> (f * s) * &1 / s = f`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
    MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
          ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    SUBGOAL_THEN
     `!n. real_integral (real_interval [--pi,pi])
                        (\x. dirichlet_kernel n x * (f(x + t) - f(t))) =
          real_integral (real_interval [--pi,pi])
                        (\x. sin((&n + &1 / &2) * x) *
                             inv(&2) * (f(x + t) - f(t)) / sin(x / &2))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For any function $f$ and real number $t$, if:
1. $f$ is absolutely integrable on the interval $[-\pi, \pi]$, i.e., $f$ is absolutely real integrable on $[-\pi, \pi]$,
2. The function $\frac{f(x+t) - f(t)}{\sin(x/2)}$ is absolutely integrable on the interval $[-\pi, \pi]$, and
3. $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$,

then the sequence of partial sums of the Fourier series of $f$ evaluated at the point $t$ converges to $f(t)$. That is:

$$\left(\sum_{k=0}^{n} c_k \cdot \phi_k(t)\right) \to f(t) \text{ as } n \to \infty$$

where $c_k$ is the $k$-th Fourier coefficient of $f$ and $\phi_k$ is the $k$-th trigonometric basis function.

### Informal proof
The proof transforms the problem into showing that the difference between the Fourier series approximation and the function value approaches zero.

* First, we rewrite the limit to prove that $\sum_{k=0}^{n} c_k \cdot \phi_k(t) - f(t) \to 0$ as $n \to \infty$.

* We then apply `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` to the function $f(x) - f(t)$. This theorem relates the Fourier sum limit to an integral involving the Dirichlet kernel. 

* We confirm that the offset function $f(x+t)$ is absolutely integrable on $[-\pi,\pi]$ using `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` and the periodicity of $f$.

* The proof proceeds by dealing with two aspects:
  1. Simplifying the Fourier coefficients of $f(x) - f(t)$, which are equal to the Fourier coefficients of $f$ minus the Fourier coefficients of the constant function $f(t)$.
  
  2. The Fourier coefficient of a constant function is $c \cdot \sqrt{2\pi}$ for $k=0$ and $0$ for $k > 0$ (by `FOURIER_COEFFICIENT_CONST`).

* For the first few terms, we handle the $k=0$ term separately, establishing that the sum from $k=1$ to $n$ equals the sum for the function $f(x) - f(t)$.

* We then prove that the integral of the Dirichlet kernel multiplied by $f(x+t) - f(t)$ can be rewritten as:
  $$\int_{-\pi}^{\pi} \frac{\sin((n+1/2)x)}{2\sin(x/2)} \cdot (f(x+t) - f(t)) \, dx$$

* Finally, we apply the Riemann-Lebesgue lemma for the sine function with half-integer multiple (`RIEMANN_LEBESGUE_SIN_HALF`), which shows that this integral approaches zero as $n \to \infty$, since the function $\frac{f(x+t) - f(t)}{\sin(x/2)}$ is absolutely integrable by assumption.

### Mathematical insight
This theorem provides a sufficient condition for pointwise convergence of the Fourier series to the function value at a specific point. The key insight is the introduction of the Dini-type condition that $\frac{f(x+t) - f(t)}{\sin(x/2)}$ must be absolutely integrable.

This is a variant of the Dini criterion for Fourier series convergence. The condition essentially controls the behavior of the function near the point where we want to establish convergence. The denominator $\sin(x/2)$ is related to the Dirichlet kernel's behavior, and requiring that the ratio is integrable ensures the oscillatory integral involving the Dirichlet kernel converges to zero.

This theorem is important because it provides practical verifiable conditions for the pointwise convergence of Fourier series without requiring stronger conditions like uniform continuity or differentiability of the function.

### Dependencies
- **Definitions:**
  - `fourier_coefficient` - The coefficient in a Fourier series expansion
  - `dirichlet_kernel` - The kernel function used in Fourier analysis

- **Theorems:**
  - `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` - Relates Fourier sum convergence to integrals with the Dirichlet kernel
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` - Shows that a periodic offset of an absolutely integrable function remains integrable
  - `FOURIER_COEFFICIENT_SUB` - Linearity of Fourier coefficients with respect to function subtraction
  - `FOURIER_COEFFICIENT_CONST` - Formula for the Fourier coefficients of a constant function
  - `RIEMANN_LEBESGUE_SIN_HALF` - The Riemann-Lebesgue lemma for sine with half-integer multiple
  - `trigonometric_set` - Definition of the trigonometric basis functions

### Porting notes
When porting this theorem:
1. Ensure the definition of Fourier coefficients and the trigonometric basis functions match HOL Light's conventions
2. The Dirichlet kernel might be defined differently in other systems, verify the definition carefully
3. The proof relies heavily on the Riemann-Lebesgue lemma for sine with half-integer multiple, which might need to be established separately
4. The absolute integrability conditions are crucial and their exact formulation may differ between systems

---

## REAL_SIN_X2_ZEROS

### Name of formal statement
REAL_SIN_X2_ZEROS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_SIN_X2_ZEROS = prove
 (`{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
   `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
  REWRITE_TAC[PI_NZ; REAL_RING
   `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
  MESON_TAC[IN]);;
```

### Informal statement
The theorem states that the set of all real numbers $x$ such that $\sin(x/2) = 0$ is equal to the image of the set of integers under the function $f(n) = 2\pi n$.

In mathematical notation:
$$\{x \in \mathbb{R} \mid \sin(x/2) = 0\} = \{2\pi n \mid n \in \mathbb{Z}\}$$

### Informal proof
The proof shows that the solutions to $\sin(x/2) = 0$ are precisely the numbers of the form $2\pi n$ where $n$ is an integer.

* First, the proof applies symmetry conversion (`SYM_CONV`) to switch the sides of the equality.
* Then it uses `SURJECTIVE_IMAGE_EQ` to prove that the image of integers under the function $f(n) = 2\pi n$ equals the set of solutions to $\sin(x/2) = 0$.
* It rewrites the statement using the fact that $\sin(y) = 0$ if and only if $y = n\pi$ for some integer $n$.
* This means $\sin(x/2) = 0$ if and only if $x/2 = n\pi$ for some integer $n$.
* Algebraically, this is equivalent to $x = 2\pi n$.
* The proof also handles the injectivity condition for the mapping by showing that $2\pi m = 2\pi n$ if and only if $\pi = 0$ or $m = n$. Since $\pi \neq 0$, this means $m = n$.
* This completes the proof that the set of zeros of $\sin(x/2)$ is precisely $\{2\pi n \mid n \in \mathbb{Z}\}$.

### Mathematical insight
This theorem characterizes all zeros of the $\sin(x/2)$ function, showing they occur at even multiples of $\pi$. This is a direct consequence of the fact that the sine function has zeros at integer multiples of $\pi$.

The result is useful in various applications of trigonometry, particularly when working with functions that have periodicity related to $\sin(x/2)$. The characterization of zeros is fundamental for understanding the behavior of this function.

### Dependencies
- `SYM_CONV`: Symmetry conversion
- `SURJECTIVE_IMAGE_EQ`: Theorem about equating image of a surjective function
- `SIN_EQ_0`: Characterization of zeros of the sine function
- `PI_NZ`: Statement that $\pi \neq 0$
- `IN`: Predicate for set membership
- `REAL_ARITH`, `REAL_RING`: Automation for real arithmetic

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the target system has a well-defined representation of the real sine function and $\pi$.
- Check how the target system handles set builder notation and image sets.
- The `SURJECTIVE_IMAGE_EQ` theorem is key for this proof and may need to be ported first if not available.
- Real arithmetic automation equivalent to `REAL_ARITH` and `REAL_RING` would be helpful for simplifying the algebraic manipulations.

---

## HOELDER_FOURIER_CONVERGENCE_PERIODIC

### HOELDER_FOURIER_CONVERGENCE_PERIODIC
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HOELDER_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M a t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ &0 < a /\
        (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t) rpow a)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `?e. &0 < e /\
         !x. abs(x) < e
             ==> abs((f (x + t) - f t) / sin (x / &2))
                 <= &4 * abs M * abs(x) rpow (a - &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REAL_DIFF_CONV
     `((\x. sin(x / &2)) has_real_derivative w) (atreal (&0))`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COS_0; REAL_MUL_RID] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &4`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SIN_0; REAL_SUB_RZERO] THEN DISCH_THEN
     (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `sin(x / &2) = &0` THENL
     [ONCE_REWRITE_TAC[real_div] THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_ADD_LID;
                      REAL_MUL_LZERO] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
     `abs(x - &1 / &2) < &1 / &4 ==> &1 / &4 <= abs(x)`)) THEN
    SUBGOAL_THEN
     `abs((f(x + t) - f t) / sin (x / &2)) =
      abs(inv(sin(x / &2) / x)) * abs(f(x + t) - f t) / abs(x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_INV] THEN
      UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS; REAL_LE_DIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV] THEN
      SUBST1_TAC(REAL_ARITH `&4 = inv(&1 / &4)`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_ABS_NZ; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM REAL_POW_1] THEN
      ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD; GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC[REAL_ARITH `a - &1 + &1 = a`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `M * abs((x + t) - t) rpow a` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN
        REWRITE_TAC[GSYM REAL_ABS_RPOW] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--e,e)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. max (B * abs(f(x + t) - f t))
                           ((&4 * abs M) * abs(x) rpow (a - &1))` THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
      MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_LMUL;
       ABSOLUTELY_REAL_INTEGRABLE_ABS;
       ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    MP_TAC(ISPECL
     [`\x. inv(a) * x rpow a`; `\x. x rpow (a - &1)`; `&0`; `pi`]
     REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC[PI_POS_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN
        MAP_EVERY UNDISCH_TAC [`&0 < a`; `&0 < x`] THEN CONV_TAC REAL_FIELD];
      DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE)] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
    SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_NEG_LE0; PI_POS_LE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_NEG_NEG; REAL_NEG_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_INTEGRABLE_EQ)) THEN
    SIMP_TAC[IN_REAL_INTERVAL; real_abs];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_CASES_TAC `abs(x) < e` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM real_div] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;
```

### Informal statement
This theorem states a sufficient condition for the convergence of a Fourier series under Hölder continuity conditions:

Let $f$ be a function such that:
1. $f$ is absolutely integrable on the interval $[-\pi, \pi]$
2. $f$ is $2\pi$-periodic: $f(x + 2\pi) = f(x)$ for all $x$
3. There exist constants $d > 0$, $a > 0$, and $M > 0$ such that $f$ satisfies a Hölder condition at point $t$:
   $|f(x) - f(t)| \leq M|x-t|^a$ for all $x$ with $|x-t| < d$

Then the Fourier series of $f$ converges to $f(t)$ at the point $t$:

$$\lim_{n \to \infty} \sum_{k=0}^{n} c_k \cdot \phi_k(t) = f(t)$$

where $c_k$ are the Fourier coefficients of $f$ and $\phi_k$ are the trigonometric basis functions.

### Informal proof
The proof establishes that under the given Hölder continuity condition, the Fourier series of $f$ converges to $f(t)$ at the point $t$.

The main steps are:

1. First, we apply `SIMPLE_FOURIER_CONVERGENCE_PERIODIC`, which reduces the problem to showing that the function $\frac{f(x+t)-f(t)}{\sin(x/2)}$ is absolutely integrable on $[-\pi,\pi]$.

2. We show that near $x = 0$, this function behaves like $|x|^{a-1}$. Specifically, we prove that for some small $\epsilon > 0$:
   $$\left|\frac{f(x+t)-f(t)}{\sin(x/2)}\right| \leq 4|M| \cdot |x|^{a-1}$$
   when $|x| < \epsilon$.

   This is done by:
   - Using the derivative of $\sin(x/2)$ at $x = 0$ to show that $\sin(x/2) \approx x/2$ for small $x$
   - Applying the Hölder condition for $f$
   - Performing algebraic manipulations to get the desired bound

3. For $x$ away from zero, we handle the potential division-by-zero issues:
   - We show that $\sin(x/2)$ has isolated zeros (at multiples of $2\pi$)
   - We prove that the set of points where $\sin(x/2)$ is bounded away from zero forms a compact set
   - We obtain a bound $B$ on $\frac{1}{\sin(x/2)}$ on this compact set

4. We then split the domain into regions and show that $\frac{f(x+t)-f(t)}{\sin(x/2)}$ is bounded by an integrable function:
   - Near $x = 0$, it's bounded by $4|M| \cdot |x|^{a-1}$, which is integrable when $a > 0$
   - Away from $x = 0$, it's bounded by $B \cdot |f(x+t)-f(t)|$, which is integrable

5. We apply the fundamental theorem of calculus to show that $|x|^{a-1}$ is integrable on $[-\pi,\pi]$, which completes the proof that $\frac{f(x+t)-f(t)}{\sin(x/2)}$ is absolutely integrable.

The key insight is connecting the Hölder condition to the integrability of the function $\frac{f(x+t)-f(t)}{\sin(x/2)}$, which is necessary for the convergence of the Fourier series.

### Mathematical insight
This theorem provides a sufficient condition for pointwise convergence of Fourier series based on local regularity of the function. The key insight is that Hölder continuity with exponent $a > 0$ is sufficient to ensure convergence.

This result is part of a broader theme in Fourier analysis where the regularity of a function determines the convergence properties of its Fourier series. While uniform convergence requires stronger conditions (like continuous differentiability), pointwise convergence can be established under weaker regularity conditions like Hölder continuity.

The theorem is significant because:
1. It generalizes simpler conditions for Fourier convergence
2. It shows that a local property (Hölder continuity at a point) ensures convergence at that point
3. The parameter $a$ measures the "smoothness" of the function - larger values of $a$ indicate higher regularity

The proof technique, using the Dirichlet kernel and analyzing the behavior of $\frac{f(x+t)-f(t)}{\sin(x/2)}$, is a standard approach in Fourier analysis for establishing pointwise convergence.

### Dependencies
- Core theorems:
  - `SIMPLE_FOURIER_CONVERGENCE_PERIODIC`: Provides a simpler convergence criterion for Fourier series
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that a shifted periodic function remains integrable
  - `REAL_SIN_X2_ZEROS`: Characterizes the zeros of $\sin(x/2)$

- Definitions:
  - `fourier_coefficient`: Defines the Fourier coefficients using orthonormal basis
  - `trigonometric_set`: Defines the trigonometric basis functions

### Porting notes
When porting this theorem to other systems:
1. Ensure the target system has a well-developed theory of Fourier series and real integration
2. The proof relies on properties of the Dirichlet kernel and detailed analysis of singularities at points where $\sin(x/2) = 0$
3. Pay attention to the treatment of the function $x \mapsto |x|^a$ (real powers) which might be handled differently in other systems
4. The theorem uses traditional analysis techniques (compactness, bounds, etc.) which should be available in most proof assistants but might have different syntax

---

## LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC

### LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t))
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOELDER_FOURIER_CONVERGENCE_PERIODIC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `&1`] THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LT_01]);;
```

### Informal statement
For any function $f$, positive real numbers $d$ and $M$, and real number $t$:
- If $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$
- $f$ satisfies a Lipschitz condition at point $t$, i.e., $0 < d$ and for all $x$ with $|x - t| < d$, we have $|f(x) - f(t)| \leq M|x - t|$

Then the Fourier series of $f$ converges to $f(t)$ at point $t$:
$$\lim_{n \to \infty} \sum_{k=0}^{n} \text{fourier\_coefficient}(f,k) \cdot \text{trigonometric\_set}(k,t) = f(t)$$

### Informal proof
The proof applies the more general theorem `HOELDER_FOURIER_CONVERGENCE_PERIODIC` with Hölder exponent $a = 1$.

We need to show that:
- $f$ is absolutely integrable on $[-\pi, \pi]$ ✓ (given)
- $f$ is $2\pi$-periodic ✓ (given)
- $0 < d$ ✓ (given)
- $0 < a$ ✓ (we can set $a = 1$)
- $f$ satisfies the Hölder condition $|f(x) - f(t)| \leq M|x - t|^a$ when $|x - t| < d$

For the last condition, the Lipschitz condition we're given is precisely the Hölder condition with $a = 1$, since $\text{rpow}(|x - t|, 1) = |x - t|$.

The theorem follows directly from `HOELDER_FOURIER_CONVERGENCE_PERIODIC` with these parameters.

### Mathematical insight
This theorem establishes convergence of Fourier series for Lipschitz functions at points where they satisfy a Lipschitz condition. It's a special case of the more general Hölder condition convergence theorem, with Hölder exponent $a = 1$.

Lipschitz continuity is a particularly important and common smoothness condition in analysis. This result shows that Lipschitz functions have well-behaved Fourier series, which is important for applications in signal processing, PDEs, and other areas where Fourier analysis is used.

The theorem extends classical results about pointwise convergence of Fourier series under differentiability conditions to the weaker condition of Lipschitz continuity, highlighting how the smoothness properties of a function directly affect the convergence behavior of its Fourier series.

### Dependencies
- **Theorems**:
  - `HOELDER_FOURIER_CONVERGENCE_PERIODIC`: The more general theorem about Fourier series convergence under a Hölder condition
  - `trigonometric_set`: Definition of the orthonormal basis for Fourier series

- **Definitions**:
  - `fourier_coefficient`: The Fourier coefficients defined as orthonormal coefficients on $[-\pi,\pi]$

### Porting notes
When porting this theorem:
- Ensure that the Hölder condition with exponent 1 (the Lipschitz condition) is properly defined in your target system
- The convergence notation `---> f t` represents pointwise convergence of the sequence of partial Fourier sums to the function value at $t$
- The trigonometric basis functions and Fourier coefficients should be defined consistently with their HOL Light definitions

---

## BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t within {x | t < x}) /\
         f real_differentiable (atreal t within {x | x < t})
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[real_differentiable; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B1:real` (LABEL_TAC "1"))
   (X_CHOOSE_THEN `B2:real` (LABEL_TAC "2"))) THEN
  MATCH_MP_TAC LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC THEN
  REMOVE_THEN "1" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  REMOVE_THEN "2" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  MAP_EVERY EXISTS_TAC [`min d1 d2:real`; `abs B1 + abs B2 + &1`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `x = t \/ t < x \/ x < t`)
  THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_LE_REFL];
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `t < x ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "1" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `x < t ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "2" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For any function $f$ and a point $t$, if:
1. $f$ is absolutely integrable on the interval $[-\pi, \pi]$,
2. $f$ is periodic with period $2\pi$, i.e., $f(x + 2\pi) = f(x)$ for all $x$,
3. $f$ is differentiable from the right at $t$ (i.e., $f$ is differentiable at $t$ within the set $\{x \mid t < x\}$), and
4. $f$ is differentiable from the left at $t$ (i.e., $f$ is differentiable at $t$ within the set $\{x \mid x < t\}$),

then the Fourier series of $f$ converges to $f(t)$ at the point $t$. That is:

$$\lim_{n \to \infty} \sum_{k=0}^{n} c_k \cdot \phi_k(t) = f(t)$$

where $c_k$ is the $k$-th Fourier coefficient of $f$ and $\phi_k$ is the $k$-th function in the trigonometric basis.

### Informal proof
We need to show that if $f$ has both left and right derivatives at $t$, then its Fourier series converges to $f(t)$ at point $t$.

First, we break down the differentiability conditions into their detailed form using the definition of real differentiability:
- Let $B_1$ be the right derivative of $f$ at $t$
- Let $B_2$ be the left derivative of $f$ at $t$

We'll apply the theorem `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC`, which states that a Lipschitz condition near $t$ is sufficient for Fourier convergence at $t$.

For the right differentiability:
- By definition of differentiability, $\frac{f(x) - f(t)}{x - t} \to B_1$ as $x \to t^+$
- This implies that for any $ε = 1$, there exists $d_1 > 0$ such that 
  $|x - t| < d_1$ and $t < x$ implies $|\frac{f(x) - f(t)}{x - t} - B_1| < 1$

Similarly, for the left differentiability:
- There exists $d_2 > 0$ such that $|x - t| < d_2$ and $x < t$ implies $|\frac{f(x) - f(t)}{x - t} - B_2| < 1$

We can now establish our Lipschitz condition by setting:
- $d = \min(d_1, d_2)$
- $M = |B_1| + |B_2| + 1$

We then show that $|f(x) - f(t)| \leq M \cdot |x - t|$ whenever $|x - t| < d$ by considering three cases:
1. $x = t$: Then $|f(x) - f(t)| = 0 \leq M \cdot 0$, which is trivially satisfied
2. $t < x$: Then $|\frac{f(x) - f(t)}{x - t}| < |B_1| + 1$, which implies $|f(x) - f(t)| < (|B_1| + 1)|x - t| \leq M|x - t|$
3. $x < t$: Then $|\frac{f(x) - f(t)}{x - t}| < |B_2| + 1$, which implies $|f(x) - f(t)| < (|B_2| + 1)|x - t| \leq M|x - t|$

This establishes the Lipschitz condition, and by `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC`, we conclude that the Fourier series of $f$ converges to $f(t)$ at point $t$.

### Mathematical insight
This theorem provides a sufficient condition for pointwise convergence of a Fourier series. The intuition behind the result is that if a function has both left and right derivatives at a point, then it behaves "well enough" near that point to ensure convergence.

This is a specific case of a more general principle in Fourier analysis: local regularity of a function determines convergence properties of its Fourier series. The existence of one-sided derivatives is a form of regularity that's weaker than full differentiability but still strong enough to guarantee convergence.

The result is important because:
1. It extends convergence results to functions that might have "kinks" (different left and right derivatives) but are still reasonably well-behaved
2. It's a practical tool for analyzing functions that arise in physics and engineering, which often have piecewise smooth behavior
3. It bridges the gap between results for continuous functions and results for differentiable functions

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Defines the orthonormal basis functions for the Fourier series
  - `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC`: Shows that the Fourier series converges to $f(t)$ when $f$ satisfies a Lipschitz condition near $t$

- **Definitions**:
  - `fourier_coefficient`: Defines the Fourier coefficients as orthonormal coefficients with respect to the trigonometric basis on $[-\pi, \pi]$

### Porting notes
When porting this theorem:
1. Ensure your system has appropriate definitions for Fourier series and their components (coefficients, basis functions)
2. Handle the one-sided derivatives carefully - some systems may have different syntax for expressing a derivative within a restricted domain
3. The proof relies on converting the existence of one-sided derivatives to a local Lipschitz condition, which is a common approach that should translate well to other proof assistants

---

## DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC
- `DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  UNDISCH_TAC `f real_differentiable (atreal t)` THEN
  REWRITE_TAC[real_differentiable] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;
```

### Informal statement
For all real functions $f$ and real numbers $t$, if:
1. $f$ is absolutely integrable on the interval $[-\pi, \pi]$,
2. $f$ is periodic with period $2\pi$ (i.e., $f(x + 2\pi) = f(x)$ for all $x$),
3. $f$ is differentiable at the point $t$,

then the sequence of partial sums of the Fourier series of $f$ converges to $f(t)$. That is:

$$\lim_{n \to \infty} \sum_{k=0}^{n} c_k \cdot \phi_k(t) = f(t)$$

where $c_k$ is the Fourier coefficient of $f$ for index $k$, and $\phi_k$ is the $k$-th trigonometric basis function.

### Informal proof
This theorem states that if a $2\pi$-periodic function is differentiable at a point $t$, then its Fourier series converges to the function value at that point.

The proof proceeds as follows:

- We apply the more general theorem `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`, which requires the function to be differentiable from both the left and right sides of $t$.
- Since $f$ is differentiable at $t$ (without any restriction to a specific side), it is differentiable both from the left and from the right.
- Specifically, we use the fact that:
  - If $f$ is differentiable at $t$, then $f$ is differentiable within $\{x | t < x\}$ (from the right)
  - If $f$ is differentiable at $t$, then $f$ is differentiable within $\{x | x < t\}$ (from the left)
- This is formalized in HOL Light through the relationship between `HAS_REAL_DERIVATIVE_ATREAL` and `HAS_REAL_DERIVATIVE_ATREAL_WITHIN`.
- Thus, the conditions for `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC` are satisfied, and the Fourier series of $f$ converges to $f(t)$.

### Mathematical insight
This theorem is a significant result in Fourier analysis, establishing the pointwise convergence of Fourier series at points where a function is differentiable. It demonstrates that smoothness conditions (in this case, differentiability) ensure the convergence of the Fourier expansion to the original function value.

The theorem is a special case of the more general result `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`, which requires only one-sided differentiability from both directions. This reflects the general principle in Fourier analysis that smoother functions have better convergence properties for their Fourier series.

In practical applications, this theorem justifies the use of Fourier series to represent differentiable periodic functions in fields such as signal processing, differential equations, and mathematical physics.

### Dependencies
- **Theorems**: 
  - `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`: States that Fourier series converge at points where a function is differentiable from both left and right
  - `trigonometric_set`: Defines the trigonometric basis functions used in Fourier series
- **Definitions**:
  - `fourier_coefficient`: Defines Fourier coefficients as orthonormal coefficients with respect to the trigonometric basis on $[-\pi,\pi]$
  - `real_differentiable`: Concept of differentiability for real functions
  - `HAS_REAL_DERIVATIVE_ATREAL`: Describes a function having a derivative at a specific point
  - `HAS_REAL_DERIVATIVE_ATREAL_WITHIN`: Describes a function having a derivative at a point within a specific set

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the target system has a well-developed theory of Fourier analysis
2. Make sure the relationship between general differentiability and one-sided differentiability is properly established
3. In systems with a different treatment of filters or neighborhoods (such as Lean), the translation from `atreal t` to the left and right neighborhoods might need special attention
4. The use of orthonormal coefficients may be formalized differently in other systems, so the definition of `fourier_coefficient` might need adjustment

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;
```

### Informal statement
For any function $f$, natural number $n$, and constant $c$, if:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$

Then the following functions are absolutely integrable on the interval $[-\pi, \pi]$:
1. $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot f(t + x)$
2. $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot f(t - x)$
3. $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot c$

where the Dirichlet kernel is defined as:
$$\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

### Informal proof
The proof is broken into three parts, one for each of the claimed absolutely integrable functions:

1. For the function $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot f(t + x)$:
   - Rewrite the expression by using the symmetry of addition (swapping the terms in $t + x$)
   - Apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` which states that if a $2\pi$-periodic function is absolutely integrable on $[-\pi, \pi]$, then so is the function with an offset
   - The periodicity condition is satisfied by our assumption that $f(x + 2\pi) = f(x)$
   - The interval length $\pi - (-\pi) = 2\pi$ matches the periodicity

2. For the function $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot f(t - x)$:
   - First convert to the standard form of integrability
   - Use the reflection theorem for real integrals to transform the integral
   - Simplify by noting that $-(-x) = x$ and rewriting using addition symmetry
   - Apply the same `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` theorem as in part 1
   - Again, the periodicity condition is satisfied by our assumption

3. For the function $x \mapsto \text{dirichlet\_kernel}(n, x) \cdot c$:
   - Directly apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_CONST` which states that a constant function multiplied by an absolutely integrable function remains absolutely integrable

### Mathematical insight
This theorem extends the absolute integrability of functions involving the Dirichlet kernel by showing that translations and reflections of the integrated function preserve integrability. The Dirichlet kernel is fundamental in Fourier analysis, particularly in the study of Fourier series convergence.

The theorem is especially useful for halving the region of integration when dealing with symmetric functions, as suggested by the comment in the original code: "Use reflection to halve the region of integration." This can significantly simplify certain calculations in Fourier analysis.

The result also establishes that the Dirichlet kernel, despite having singularities, behaves well with respect to absolute integrability when multiplied with appropriate functions.

### Dependencies
- **Theorems**:
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: If a function is $2\pi$-periodic and absolutely integrable on $[a,b]$, then shifting the function by any constant preserves absolute integrability.
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: If a function is absolutely integrable on $[-\pi,\pi]$, then multiplying it by the Dirichlet kernel preserves absolute integrability.
  - `ABSOLUTELY_REAL_INTEGRABLE_CONST`: Implicitly used for handling the constant case.
  - `REAL_INTEGRABLE_REFLECT`: Used to handle the reflection case.

- **Definitions**:
  - `dirichlet_kernel`: The Dirichlet kernel function as defined above.

### Porting notes
When implementing this in other proof assistants:
1. Ensure that the Dirichlet kernel is properly defined, especially handling its singularity at x = 0.
2. The proof relies on several specialized theorems about absolutely integrable functions - these would need to be established first.
3. The reflection property of integrals might be formalized differently in other systems, so careful attention should be paid to how `REAL_INTEGRABLE_REFLECT` is represented.
4. The theorem uses real arithmetic simplification which might need different approaches in other systems.

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;
```

### Informal statement
For all functions $f$, integers $n$, real numbers $d$ and $c$, and some parameter $t$, if:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$)
- $d \leq \pi$

Then the following functions are all absolutely integrable on the interval $[0, d]$:
1. $x \mapsto D_n(x) \cdot f(t + x)$
2. $x \mapsto D_n(x) \cdot f(t - x)$
3. $x \mapsto D_n(x) \cdot c$
4. $x \mapsto D_n(x) \cdot (f(t + x) + f(t - x))$
5. $x \mapsto D_n(x) \cdot ((f(t + x) + f(t - x)) - c)$

where $D_n(x)$ is the Dirichlet kernel defined as:
$D_n(x) = \begin{cases} 
n + \frac{1}{2} & \text{if}\ x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$

### Informal proof
This theorem is proved by applying several key properties of absolute integrability:

- First, we rewrite the conjunction to separate the hypotheses from the conclusion, and apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED` to the hypotheses.

- For the first three functions, we prove they are absolutely integrable on $[0,d]$ by showing:
  * They are absolutely integrable on $[-\pi,\pi]$ (from the applied theorem)
  * The interval $[0,d]$ is a subset of $[-\pi,\pi]$ (since $d \leq \pi$ and $\pi > 0$)
  * We can restrict integrability to a subinterval using `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`

- For the last two functions, we use the distributive property of multiplication over addition and subtraction:
  * $D_n(x) \cdot (f(t + x) + f(t - x)) = D_n(x) \cdot f(t + x) + D_n(x) \cdot f(t - x)$
  * $D_n(x) \cdot ((f(t + x) + f(t - x)) - c) = D_n(x) \cdot (f(t + x) + f(t - x)) - D_n(x) \cdot c$

- We then apply the theorems `ABSOLUTELY_REAL_INTEGRABLE_ADD` and `ABSOLUTELY_REAL_INTEGRABLE_SUB` to show that the addition and subtraction of absolutely integrable functions remains absolutely integrable.

### Mathematical insight
This theorem is important in Fourier analysis, particularly when working with the Dirichlet kernel, which is the fundamental tool for studying the convergence of Fourier series.

The theorem extends the result about absolute integrability over $[-\pi,\pi]$ to arbitrary intervals $[0,d]$ where $d \leq \pi$. This is useful because in many Fourier analysis applications, we need to work with integrals on subintervals of $[-\pi,\pi]$.

The functions involving $f(t+x)$ and $f(t-x)$ represent translations of the function $f$, which are important for convolution operations. The theorem ensures that these translated functions, when multiplied by the Dirichlet kernel, remain absolutely integrable - a key property needed for various convergence results in Fourier theory.

The inclusion of the constant term $c$ and the difference $(f(t+x) + f(t-x)) - c$ allows for analyzing how Fourier series approximate functions, particularly when studying pointwise convergence.

### Dependencies
- **Theorems:**
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED` - Establishes absolute integrability of functions multiplied by Dirichlet kernel on $[-\pi,\pi]$
  - `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL` - Allows restricting absolute integrability to subintervals
  - `ABSOLUTELY_REAL_INTEGRABLE_ADD` - Shows sum of absolutely integrable functions is absolutely integrable
  - `ABSOLUTELY_REAL_INTEGRABLE_SUB` - Shows difference of absolutely integrable functions is absolutely integrable
  - `PI_POS` - States that $\pi > 0$

- **Definitions:**
  - `dirichlet_kernel` - Defines the Dirichlet kernel function used in Fourier analysis

### Porting notes
When porting this theorem:
1. Ensure your target system has a suitable definition of absolute integrability and the Dirichlet kernel
2. Be careful with the handling of real interval notation and subset relations between intervals
3. The proof relies on algebraic properties of real multiplication (distributivity) applied to integrals, so verify your target system has equivalent theorems
4. The parameter $t$ appears free in the statement - in some proof assistants, this might need to be explicitly quantified

---

## FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) -
            l =
            real_integral (real_interval[&0,pi])
                          (\x. dirichlet_kernel n x *
                               ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC(MATCH_MP (REAL_FIELD
   `&0 < pi ==> x = y + pi * l ==> x / pi - l = y / pi`) PI_POS) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[MESON[REAL_ADD_SYM]
   `dirichlet_kernel n x * f(x + t) = dirichlet_kernel n x * f(t + x)`] THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM real_sub] THEN
  MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF) THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * l` o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
  REWRITE_TAC[REAL_ARITH `pi / &2 * &2 * l = pi * l`] THEN
  DISCH_THEN(SUBST1_TAC o GSYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_RADD] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(GSYM REAL_INTEGRAL_SUB) THEN
  MP_TAC(GEN `c:real` (ISPECL [`f:real->real`; `n:num`; `pi`; `c:real`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_ADD_LDISTRIB;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```

### Informal statement
For any function $f$ that is absolutely integrable on the interval $[-\pi, \pi]$ and periodic with period $2\pi$ (i.e., $f(x + 2\pi) = f(x)$ for all $x$), and for any natural number $n$ and real number $t$, we have:

$$\sum_{k=0}^{2n} \text{fourier\_coefficient}(f)(k) \cdot \text{trigonometric\_set}(k)(t) - l = \frac{1}{\pi} \int_0^{\pi} \text{dirichlet\_kernel}(n)(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

where $\text{fourier\_coefficient}$ represents the Fourier coefficients of $f$, $\text{trigonometric\_set}$ represents the trigonometric basis functions, and $\text{dirichlet\_kernel}$ is the Dirichlet kernel function.

### Informal proof
This theorem extends the result from `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL` to express the difference between the partial Fourier sum and a constant in terms of an integral involving the Dirichlet kernel.

The proof proceeds as follows:

* First, we apply the theorem `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`, which expresses the partial Fourier sum in terms of an integral over $[-\pi, \pi]$.

* The theorem `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL` states that:
  $$\sum_{k=0}^{2n} \text{fourier\_coefficient}(f)(k) \cdot \text{trigonometric\_set}(k)(t) = \frac{1}{\pi} \int_{-\pi}^{\pi} \text{dirichlet\_kernel}(n)(x) \cdot f(x+t) \, dx$$

* We want to transform this into the form $(\text{sum} - l) = \frac{1}{\pi} \int_0^{\pi} \ldots$, so we use a field property:
  $$\text{If } x = y + \pi \cdot l \text{ and } \pi > 0, \text{ then } \frac{x}{\pi} - l = \frac{y}{\pi}$$

* We need to show that the integral over $[-\pi, \pi]$ can be rewritten in terms of an integral over $[0, \pi]$.

* The function $f(x+t)$ is absolutely integrable on $[-\pi, \pi]$ due to the periodicity of $f$ (proven using `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`).

* Using `REAL_INTEGRAL_REFLECT_AND_ADD`, we transform the integral over $[-\pi, \pi]$ to an integral over $[0, \pi]$ with the integrand $f(t+x) + f(t-x)$.

* For the constant term, we use `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF` which states that $\int_0^{\pi} \text{dirichlet\_kernel}(n)(x) \, dx = \frac{\pi}{2}$.

* Multiplying both sides by $2l$, we get $\int_0^{\pi} \text{dirichlet\_kernel}(n)(x) \cdot 2l \, dx = \pi \cdot l$.

* Finally, we use the linearity of the integral to combine terms and arrive at the desired result.

The theorem effectively expresses the approximation error of the partial Fourier sum in terms of an integral involving the Dirichlet kernel and the deviation of the function's symmetric average from the constant $l$.

### Mathematical insight
This theorem provides a key insight into the relationship between a function's partial Fourier sum and the behavior of the function itself. By expressing the difference between the partial sum and a constant $l$ in terms of an integral involving the Dirichlet kernel, the theorem offers a powerful tool for analyzing the convergence properties of Fourier series.

The theorem is particularly useful for studying the pointwise convergence of Fourier series. The Dirichlet kernel plays a central role in Fourier analysis, serving as the convolution kernel for partial Fourier sums. The appearance of the symmetric average $(f(t+x) + f(t-x))$ in the integral highlights the importance of local symmetry properties in determining convergence behavior.

This result is a stepping stone toward proving important results like Fejér's theorem and the Dirichlet-Jordan test for the convergence of Fourier series at specific points. It transforms the global properties of the Fourier series (represented by the sum) into local properties of the function (represented by the integral).

### Dependencies
- **Theorems**:
  - `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`: Expresses the partial Fourier sum in terms of an integral involving the Dirichlet kernel
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that a periodic shift of an absolutely integrable function remains absolutely integrable
  - `REAL_INTEGRAL_REFLECT_AND_ADD`: Relates the integral over $[-a,a]$ to an integral over $[0,a]$ with a modified integrand
  - `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`: Gives the integral of the Dirichlet kernel over $[0,\pi]$
  - `DIRICHLET_KERNEL_NEG`: Shows that the Dirichlet kernel is an even function
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: Shows that multiplying an absolutely integrable function by the Dirichlet kernel preserves absolute integrability
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART`: Various integrability properties for functions involving the Dirichlet kernel

- **Definitions**:
  - `fourier_coefficient`: The Fourier coefficients of a function
  - `dirichlet_kernel`: The Dirichlet kernel function
  - `trigonometric_set`: The trigonometric basis functions

### Porting notes
When porting this theorem, consider the following:

1. Make sure your target system has appropriate definitions for Fourier coefficients, trigonometric basis functions, and the Dirichlet kernel. The Dirichlet kernel is defined as:
   - $\text{dirichlet\_kernel}(n)(x) = n + \frac{1}{2}$ if $x = 0$
   - $\text{dirichlet\_kernel}(n)(x) = \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$ otherwise

2. Ensure that your system has a well-developed theory of real integration, particularly for absolutely integrable functions and properties of integrals under variable transformations.

3. The proof relies heavily on the periodicity of trigonometric functions and properties of the Dirichlet kernel, so these foundations should be established in the target system.

4. The parameter $l$ in the theorem statement represents an arbitrary constant, which is useful for applications where you want to measure the deviation of the Fourier sum from a specific value.

---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_RMUL_EQ THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For any function $f$, point $t$, and real number $l$, if $f$ is absolutely integrable on the interval $[-\pi, \pi]$ and $f$ is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$), then the following are equivalent:

1. The sequence of partial Fourier sums 
   $\sum_{k=0}^n c_k \phi_k(t)$ converges to $l$ as $n \to \infty$,
   
   where $c_k$ is the $k$-th Fourier coefficient of $f$ and $\phi_k$ is the $k$-th trigonometric basis function.

2. The sequence of integrals
   $\int_0^{\pi} D_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$ converges to $0$ as $n \to \infty$,
   
   where $D_n(x)$ is the Dirichlet kernel.

### Informal proof
We prove the equivalence of the two limit statements.

First, we apply `FOURIER_SUM_LIMIT_PAIR` to transform the first condition. This theorem states that the convergence of the sum from $0$ to $n$ is equivalent to the convergence of the sum from $0$ to $2n$:
$(\sum_{k=0}^n c_k \phi_k(t) \to l) \iff (\sum_{k=0}^{2n} c_k \phi_k(t) \to l)$

Next, we rewrite the limit condition to express it as convergence to zero, which transforms the left-hand side of our equivalence.

We apply `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`, which states that:
$\sum_{k=0}^{2n} c_k \phi_k(t) - l = \frac{1}{\pi} \int_0^{\pi} D_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \,dx$

This formula relates the difference between the partial Fourier sum and the limit to an integral involving the Dirichlet kernel.

Finally, we distribute the division by $\pi$ and apply `REALLIM_NULL_RMUL_EQ`, which states that for a non-zero constant $c$, we have $(a_n \to 0) \iff (c \cdot a_n \to 0)$. Since $\pi > 0$, this completes the proof of the equivalence.

### Mathematical insight
This theorem establishes an important connection between the convergence of Fourier series and the behavior of integrals involving the Dirichlet kernel. The Dirichlet kernel plays a central role in the theory of Fourier series, particularly in studying pointwise convergence.

The result effectively characterizes the convergence of Fourier series at a point in terms of a convolution with the Dirichlet kernel. This is a key insight in Fourier analysis, as it transforms questions about series convergence into questions about integral behavior.

The second condition can be viewed as a statement about how well the Dirichlet kernels approximate a delta function - if they behave increasingly like a delta function centered at zero, then the Fourier series will converge to the value $l$.

This relationship is fundamental for proving convergence properties of Fourier series and understanding their behavior at points of discontinuity or other irregular points of the function.

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Defines the trigonometric basis functions in the Fourier series
  - `FOURIER_SUM_LIMIT_PAIR`: Equivalence between convergence of sums to $n$ and to $2n$
  - `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`: Relates the partial Fourier sum to an integral with the Dirichlet kernel

- **Definitions**:
  - `fourier_coefficient`: Defines the Fourier coefficients as orthonormal coefficients
  - `dirichlet_kernel`: Defines the Dirichlet kernel function

### Porting notes
When porting this theorem to other proof assistants:
- The Dirichlet kernel and its properties will need to be properly defined first
- The theory of orthonormal functions and Fourier coefficients must be developed
- Careful handling of the periodic extension of functions will be needed
- Some proof assistants might have different ways of expressing convergence of sequences, which may require adaptation
- The use of real analysis tactics (like `REAL_FIELD`) may need to be replaced with appropriate alternatives in target systems

---

## RIEMANN_LOCALIZATION_INTEGRAL

### RIEMANN_LOCALIZATION_INTEGRAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL = prove
 (`!d f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ (!x. abs(x) < d ==> f x = g x)
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * g(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * f(x)) -
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * g(x)) =
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs(x) < d then &0 else f(x) - g(x)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 GSYM REAL_INTEGRAL_SUB] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{}:real->bool` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ARITH `&0 = x - y <=> x = y`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs x < d then &0 else f(x) - g(x))) =
        real_integral (real_interval[--pi,pi])
                      (\x. sin((&n + &1 / &2) * x) *
                           inv(&2) *
                           (if abs x < d then &0 else f(x) - g(x)) /
                           sin(x / &2))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
    REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--d,d)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. B * abs(f(x) - g(x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_REAL_MEASURABLE; REAL_MEASURABLE_ON_0;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB] THEN
      SUBGOAL_THEN `{x | abs x < d} = real_interval(--d,d)`
       (fun th -> REWRITE_TAC[th; REAL_LEBESGUE_MEASURABLE_INTERVAL]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      SUBGOAL_THEN `{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
        REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
         `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
        REWRITE_TAC[PI_NZ; REAL_RING
          `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
        MESON_TAC[IN];
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ABS;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ONCE_REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;
```

### Informal statement

For any functions $f$ and $g$ that are absolutely integrable on the interval $[-\pi, \pi]$, and a positive number $d > 0$, if $f(x) = g(x)$ for all $|x| < d$, then:

$$\lim_{n \to \infty} \left( \int_{-\pi}^{\pi} D_n(x) \cdot f(x) \, dx - \int_{-\pi}^{\pi} D_n(x) \cdot g(x) \, dx \right) = 0$$

where $D_n(x)$ is the Dirichlet kernel defined as:

$$D_n(x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{if } x \neq 0
\end{cases}$$

This theorem states that the asymptotic behavior of the Dirichlet integrals depends only on the values of the function near the origin.

### Informal proof

The proof proceeds in several steps:

1. First, rewrite the difference of integrals as a single integral of the difference:
   $$\int_{-\pi}^{\pi} D_n(x) \cdot f(x) \, dx - \int_{-\pi}^{\pi} D_n(x) \cdot g(x) \, dx = \int_{-\pi}^{\pi} D_n(x) \cdot (f(x) - g(x)) \, dx$$

2. Since $f(x) = g(x)$ when $|x| < d$, we can rewrite this as:
   $$\int_{-\pi}^{\pi} D_n(x) \cdot \begin{cases} 0 & \text{if } |x| < d \\ f(x) - g(x) & \text{otherwise} \end{cases} \, dx$$

3. Using the definition of the Dirichlet kernel (except at $x = 0$), we convert the integral to:
   $$\int_{-\pi}^{\pi} \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} \cdot \begin{cases} 0 & \text{if } |x| < d \\ f(x) - g(x) & \text{otherwise} \end{cases} \, dx$$

   The point $x = 0$ can be excluded as it forms a negligible set.

4. By the Riemann-Lebesgue lemma (specifically `RIEMANN_LEBESGUE_SIN_HALF`), we need to show that the function:
   $$h(x) = \frac{1}{2} \cdot \frac{f(x) - g(x)}{\sin(\frac{x}{2})} \cdot \begin{cases} 0 & \text{if } |x| < d \\ 1 & \text{otherwise} \end{cases}$$
   is absolutely integrable.

5. To prove this, we show that the function $\frac{1}{\sin(\frac{x}{2})}$ is bounded on $[-\pi,\pi] \setminus (-d,d)$:
   - The function $\frac{1}{\sin(\frac{x}{2})}$ is continuous on this domain since $\sin(\frac{x}{2})$ never equals zero there.
   - The domain is compact (closed and bounded), so the continuous function attains a maximum value $B$.

6. Therefore, $h(x)$ is bounded by $B \cdot |f(x) - g(x)|$, which is integrable since $f$ and $g$ are absolutely integrable.

7. Finally, applying the Riemann-Lebesgue lemma, we conclude that the sequence of integrals converges to zero.

### Mathematical insight

This theorem represents a localization principle in Fourier analysis: the asymptotic behavior of Dirichlet integrals (which are related to Fourier series) depends only on the local behavior of the function near the origin. 

This is a manifestation of a broader principle in analysis that certain limiting behaviors are determined by local properties. In the context of Fourier analysis, this theorem is particularly important because:

1. It shows that the convergence behavior of Fourier series at a point depends only on the function's behavior near that point.
2. It allows us to analyze convergence by focusing on a local neighborhood.
3. It underpins many results about pointwise convergence of Fourier series.

The theorem is named after Bernhard Riemann, who made significant contributions to the theory of Fourier series and integration. It's a fundamental result in the study of Fourier analysis and has applications in partial differential equations, signal processing, and harmonic analysis.

### Dependencies
- **Theorems**:
  - `RIEMANN_LEBESGUE_SIN_HALF`: States that if $f$ is absolutely integrable on $[-\pi,\pi]$, then the sequence of integrals $\int_{-\pi}^{\pi} \sin((n+\frac{1}{2})x) \cdot f(x) \, dx$ converges to 0.
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: States that if $f$ is absolutely integrable on $[-\pi,\pi]$, then the product of $f$ with the Dirichlet kernel is also absolutely integrable on $[-\pi,\pi]$.

- **Definitions**:
  - `dirichlet_kernel`: Defines the Dirichlet kernel as $D_n(x) = (n + \frac{1}{2})$ if $x = 0$, otherwise $\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})}$.

### Porting notes
When porting this theorem to other systems, special attention should be paid to:

1. The definition of absolute integrability, which may vary across systems.
2. The handling of the Dirichlet kernel, especially its singularity at $x = 0$.
3. The application of the Riemann-Lebesgue lemma, which might require different formulations in other systems.
4. The treatment of measurability and negligible sets, which can have different foundations in different proof assistants.

---

## RIEMANN_LOCALIZATION_INTEGRAL_RANGE

### RIEMANN_LOCALIZATION_INTEGRAL_RANGE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL_RANGE = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--d,d])
                                (\x. dirichlet_kernel n x * f(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL[`d:real`; `f:real->real`;
           `\x. if x IN real_interval[--d,d] then f x else &0`]
     RIEMANN_LOCALIZATION_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
      REWRITE_TAC[MESON[] `(if p then if q then x else y else y) =
                           (if p /\ q then x else y)`] THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV; GSYM IN_INTER] THEN
      REWRITE_TAC[INTER; IN_REAL_INTERVAL] THEN
      ASM_SIMP_TAC[REAL_ARITH
       `&0 < d /\ d <= pi
        ==> ((--pi <= x /\ x <= pi) /\ --d <= x /\ x <= d <=>
             --d <= x /\ x <= d)`] THEN
      REWRITE_TAC[GSYM real_interval] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[MESON[REAL_MUL_RZERO]
     `a * (if p then b else &0) = if p then a * b else &0`] THEN
    SUBGOAL_THEN `real_interval[--d,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_RESTRICT th])]]);;
```

### Informal statement
For all real numbers $d$ and functions $f$, if:
- $f$ is absolutely real integrable on the interval $[-\pi, \pi]$
- $0 < d \leq \pi$

Then the sequence
$$\left( \int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx - \int_{[-d, d]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx \right)$$
converges to $0$ as $n$ approaches infinity (in the sequential sense).

Where the Dirichlet kernel is defined as:
$$\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

### Informal proof
We will apply the Riemann localization integral theorem (`RIEMANN_LOCALIZATION_INTEGRAL`). Let's define a function $g(x)$ such that:

$$g(x) = \begin{cases}
f(x) & \text{if } x \in [-d, d] \\
0 & \text{otherwise}
\end{cases}$$

First, we need to establish that $g$ is absolutely real integrable on $[-\pi, \pi]$:
- We rewrite this in terms of the restriction of $f$ to $[-d, d]$
- Since $[-d, d] \subset [-\pi, \pi]$ (as $d \leq \pi$), the restriction of $f$ to $[-d, d]$ is absolutely integrable
- Therefore $g$ is absolutely real integrable on $[-\pi, \pi]$

Next, we need to verify that $f$ and $g$ agree on the interval $(-d, d)$, which is true by our construction of $g$.

By applying the `RIEMANN_LOCALIZATION_INTEGRAL` theorem, we know that:
$$\left( \int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx - \int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \cdot g(x) \, dx \right) \to 0$$

Now, observe that:
$$\int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \cdot g(x) \, dx = \int_{[-d, d]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx$$

This is because:
- $g(x) = f(x)$ when $x \in [-d, d]$
- $g(x) = 0$ when $x \not\in [-d, d]$, so $\text{dirichlet\_kernel}(n, x) \cdot g(x) = 0$ in this region

Therefore:
$$\left( \int_{[-\pi, \pi]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx - \int_{[-d, d]} \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx \right) \to 0$$

Which proves the statement.

### Mathematical insight
This theorem is a variation of the Riemann localization principle applied to Fourier analysis. It shows that the contribution to the Fourier integral from outside a small interval around the point of interest becomes negligible as the number of terms increases.

The Dirichlet kernel plays a fundamental role in Fourier series convergence. This result shows that when computing the Fourier coefficients (through convolution with the Dirichlet kernel), we can focus on the behavior of the function in an arbitrarily small neighborhood around each point.

This localization property is crucial in Fourier analysis because it means that the convergence of Fourier series depends only on the local behavior of the function, not on its global properties. This is why Fourier series can converge even to functions with discontinuities.

### Dependencies
- `RIEMANN_LOCALIZATION_INTEGRAL`: States that if two functions agree in a neighborhood of a point, then their Fourier integrals converge to the same value
- `dirichlet_kernel`: Definition of the Dirichlet kernel function used in Fourier analysis

### Porting notes
When porting this theorem, pay attention to:
1. The definition of absolute integrability in your target system
2. How the Dirichlet kernel is defined, particularly at the singularity point x = 0
3. The notion of sequential convergence in your target system

The proof relies heavily on the Riemann localization principle, so that theorem should be ported first.

---

## RIEMANN_LOCALIZATION

### RIEMANN_LOCALIZATION
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION = prove
 (`!t d c f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ (!x. g(x + &2 * pi) = g(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> f x = g x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> c) sequentially <=>
             ((\n. sum (0..n)
                       (\k. fourier_coefficient g k * trigonometric_set k t))
              ---> c) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;
```

### Informal statement
The Riemann localization principle for Fourier series states that:

Let $f$ and $g$ be absolutely integrable functions on the interval $[-\pi, \pi]$ that are both $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ and $g(x + 2\pi) = g(x)$ for all $x$). If there exists $d > 0$ such that $f(x) = g(x)$ for all $x$ satisfying $|x - t| < d$ (i.e., $f$ and $g$ agree in a neighborhood of the point $t$), then the Fourier series of $f$ and $g$ have the same convergence behavior at the point $t$.

Specifically, for any constant $c$, the sequence of partial sums
$$\left(\sum_{k=0}^{n} \hat{f}(k) \cdot \phi_k(t)\right)$$
converges to $c$ if and only if the sequence
$$\left(\sum_{k=0}^{n} \hat{g}(k) \cdot \phi_k(t)\right)$$
converges to $c$, where $\hat{f}(k)$ and $\hat{g}(k)$ are the Fourier coefficients of $f$ and $g$ respectively, and $\phi_k$ is the $k$-th trigonometric basis function.

### Informal proof
The proof proceeds in several steps:

1. First, we apply the `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` theorem to both sides of the equivalence. This transforms the convergence of Fourier partial sums into equivalent statements about integrals involving the Dirichlet kernel:
   
   For a function $h$, the Fourier partial sum 
   $$\sum_{k=0}^{n} \hat{h}(k) \cdot \phi_k(t)$$
   converges to $c$ if and only if 
   $$\int_{-\pi}^{\pi} D_n(x) \cdot h(x+t) \, dx \to \pi c$$
   where $D_n$ is the Dirichlet kernel.

2. We then apply this to both $f$ and $g$, converting the original equivalence to:
   
   $$\left(\int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx \to \pi c\right) \iff \left(\int_{-\pi}^{\pi} D_n(x) \cdot g(x+t) \, dx \to \pi c\right)$$

3. To prove this equivalence, we use `REALLIM_TRANSFORM_EQ` to show that the difference between these integrals converges to 0:
   
   $$\left(\int_{-\pi}^{\pi} D_n(x) \cdot f(x+t) \, dx - \int_{-\pi}^{\pi} D_n(x) \cdot g(x+t) \, dx\right) \to 0$$

4. We invoke `RIEMANN_LOCALIZATION_INTEGRAL` with parameter $d$ to prove this limit.

5. Finally, we verify the conditions required by `RIEMANN_LOCALIZATION_INTEGRAL`:
   - We show that both $(x \mapsto f(x+t))$ and $(x \mapsto g(x+t))$ are absolutely integrable on $[-\pi,\pi]$ by applying `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` to $f$ and $g$.
   - We confirm that these functions agree when $|x| < d$, which follows from our assumption that $f$ and $g$ agree when $|x-t| < d$.

The final step uses algebraic manipulation to show that the conditions align perfectly with the requirements of the localization principle.

### Mathematical insight
The Riemann localization principle is a fundamental result in the theory of Fourier series that essentially states: the convergence behavior of a Fourier series at a specific point depends only on the behavior of the function in a neighborhood of that point.

This is a powerful principle because:

1. It allows us to analyze Fourier convergence locally, focusing only on the behavior of functions near the point of interest.
2. It separates the global integrability conditions (needed for defining Fourier coefficients) from the local convergence properties.
3. It confirms our intuition that adding a "bump" to a function far from a point $t$ shouldn't affect the convergence of its Fourier series at $t$.

The theorem is named after Bernhard Riemann, who first observed this localization property. It's a key result in understanding pointwise convergence of Fourier series and plays a role in more advanced results like the Dirichlet-Jordan theorem on Fourier convergence at points of discontinuity.

### Dependencies
- Theorems:
  - `trigonometric_set`: Defines the trigonometric basis functions
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that translations of periodic integrable functions remain integrable
  - `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL`: Relates Fourier sum convergence to integrals with Dirichlet kernels
  - `RIEMANN_LOCALIZATION_INTEGRAL`: The key technical result about integrals with Dirichlet kernels
  
- Definitions:
  - `fourier_coefficient`: Defines the Fourier coefficients using orthonormal projection

### Porting notes
When porting this theorem:
1. The proof relies heavily on the properties of the Dirichlet kernel and its relationship to Fourier series, so these supporting theorems need to be ported first.
2. The theorem assumes $2\pi$-periodicity, which is standard in analysis but may be defined differently in other systems.
3. Absolute integrability is required for the functions, which ensures that the Fourier coefficients are well-defined.
4. The localization principle works with any appropriate measure theory, but the implementation details may vary between systems.

---

## RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF

### Name of formal statement
RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))) -
                  real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`d:real`; `f:real->real`] RIEMANN_LOCALIZATION_INTEGRAL_RANGE) THEN
  MP_TAC(GEN `n:num` (ISPECL [`f:real->real`; `n:num`]
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. dirichlet_kernel n x * f x) absolutely_real_integrable_on
        real_interval[--d,d]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL) o SPEC `n:num`) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM REAL_ADD_LDISTRIB]]);;
```

### Informal statement
For any function $f$ that is absolutely integrable on the interval $[-\pi, \pi]$ and for any real number $d$ where $0 < d \leq \pi$, the sequence 
$$\left(\int_0^\pi \text{dirichlet\_kernel}(n, x) \cdot (f(x) + f(-x)) \, dx - \int_0^d \text{dirichlet\_kernel}(n, x) \cdot (f(x) + f(-x)) \, dx\right)_{n=1}^{\infty}$$ 
converges to $0$ as $n$ approaches infinity.

Here, $\text{dirichlet\_kernel}(n, x)$ is defined as:
- $n + \frac{1}{2}$ if $x = 0$
- $\frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})}$ otherwise

### Informal proof
We prove this using the following steps:

- First, we apply the theorem `RIEMANN_LOCALIZATION_INTEGRAL_RANGE`, which states that for an absolutely integrable function on $[-\pi, \pi]$ and $0 < d \leq \pi$, the sequence of differences between integrals over $[-\pi, \pi]$ and $[-d, d]$ of $\text{dirichlet\_kernel}(n, x) \cdot f(x)$ converges to zero.

- We leverage `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL` to establish that if $f$ is absolutely integrable on $[-\pi, \pi]$, then $\text{dirichlet\_kernel}(n, x) \cdot f(x)$ is also absolutely integrable on that interval.

- Next, we show that for any $n$, the function $\text{dirichlet\_kernel}(n, x) \cdot f(x)$ is absolutely integrable on the subinterval $[-d, d]$ by applying the subinterval property of absolute integrability.

- Finally, we use the fact that the Dirichlet kernel is even (i.e., $\text{dirichlet\_kernel}(n, -x) = \text{dirichlet\_kernel}(n, x)$) from `DIRICHLET_KERNEL_NEG`. 

- By applying `REAL_INTEGRAL_REFLECT_AND_ADD`, we convert the integral over $[-\pi, \pi]$ (or $[-d, d]$) to twice the integral over $[0, \pi]$ (or $[0, d]$) with the integrand $\text{dirichlet\_kernel}(n, x) \cdot (f(x) + f(-x))$.

- Since the difference of the integrals over $[-\pi, \pi]$ and $[-d, d]$ converges to zero, and the reflection transformation preserves this convergence property, the difference between the integrals over $[0, \pi]$ and $[0, d]$ with the symmetric integrand also converges to zero.

### Mathematical insight
This theorem is a variant of the Riemann localization principle for Fourier series, focusing on the positive half of the interval and using the symmetrized version of the function. It shows that when studying the convergence behavior of Fourier series using Dirichlet kernels, we can localize our attention to arbitrarily small intervals.

This localization property is fundamental in Fourier analysis since it allows us to reduce questions about global convergence to local properties of functions. Specifically, when analyzing the convergence of Fourier series at a point, we can focus on the behavior of the function near that point rather than considering the entire interval.

The theorem is part of the theoretical foundation for understanding the pointwise convergence of Fourier series, particularly in connection with Dirichlet's test and related results.

### Dependencies
- Theorems:
  - `RIEMANN_LOCALIZATION_INTEGRAL_RANGE`: Shows the main localization property for integrals of functions multiplied by Dirichlet kernels.
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: Establishes that multiplying an absolutely integrable function by a Dirichlet kernel preserves absolute integrability.
  - `DIRICHLET_KERNEL_NEG`: States that the Dirichlet kernel is an even function.
  - `REAL_INTEGRAL_REFLECT_AND_ADD`: Relates integrals over symmetric intervals to integrals of symmetrized functions.

- Definitions:
  - `dirichlet_kernel`: Defines the Dirichlet kernel used in Fourier analysis.

### Porting notes
When porting this theorem:
1. Ensure that the Dirichlet kernel is properly defined with the same mathematical properties, particularly its behavior at x = 0.
2. The proof relies heavily on properties of absolute integrability and transformations of integrals, so these supporting theorems need to be available.
3. Systems with more integrated support for real analysis might have simpler proofs for this result, possibly using more general theorems about convergence of parametrized integrals.

---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART

### Name of formal statement
FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[REAL_ARITH `(x + y) - &2 * l = (x - l) + (y - l)`] THEN
  MP_TAC(MESON[real_sub] `!x. (f:real->real)(t - x) = f(t + --x)`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]);;
```

### Informal statement
Let $f$ be a function that is absolutely real integrable on the interval $[-\pi, \pi]$ and $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$). Let $d$ be a real number such that $0 < d \leq \pi$, and let $t$ and $l$ be real numbers.

Then the sequence of partial sums of the Fourier series of $f$ at point $t$ converges to $l$:
$$\lim_{n \to \infty} \sum_{k=0}^{n} \text{fourier\_coefficient}(f, k) \cdot \text{trigonometric\_set}(k, t) = l$$

if and only if:
$$\lim_{n \to \infty} \int_{0}^{d} \text{dirichlet\_kernel}(n, x) \cdot ((f(t + x) + f(t - x)) - 2l) \, dx = 0$$

where $\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{if } x \neq 0
\end{cases}$

### Informal proof
This theorem relates the convergence of Fourier series to a specific integral involving the Dirichlet kernel. The proof proceeds as follows:

1. First, we apply `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF`, which states that the Fourier series of $f$ at point $t$ converges to $l$ if and only if:
   $$\lim_{n \to \infty} \int_{0}^{\pi} \text{dirichlet\_kernel}(n, x) \cdot ((f(t + x) + f(t - x)) - 2l) \, dx = 0$$

2. We need to show that this is equivalent to the integral over $[0, d]$ instead of $[0, \pi]$. We use `REALLIM_TRANSFORM_EQ` to transform the limit.

3. We rewrite the integrand using the identity $(f(t + x) + f(t - x)) - 2l = (f(t + x) - l) + (f(t - x) - l)$.

4. We use the fact that $f(t - x) = f(t + (-x))$.

5. We apply `RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF` to show that the difference between the integrals over $[0, \pi]$ and $[0, d]$ tends to zero as $n$ approaches infinity.

6. To apply this theorem, we need to show that $f$ is absolutely integrable. We use `ABSOLUTELY_REAL_INTEGRABLE_SUB` and `ABSOLUTELY_REAL_INTEGRABLE_CONST` to show that the function $(f(t + x) + f(t + (-x))) - 2l$ is absolutely integrable.

7. Finally, we use `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` to handle the offset in the function, leveraging the periodicity of $f$. This completes the proof that the two limit conditions are equivalent.

### Mathematical insight
This theorem is a localization result for Fourier series convergence, known as a variant of the Riemann localization principle. It shows that the convergence of a Fourier series at a point depends only on the behavior of the function in any neighborhood of that point.

The key insight is that the convergence of the Fourier series can be characterized through integrals involving the Dirichlet kernel, and that these integrals can be restricted to arbitrarily small intervals around the point of interest. This is powerful because it means we can determine convergence by examining the function locally.

The Dirichlet kernel plays a crucial role here as the summation kernel for Fourier series. Its properties, particularly how it behaves as $n$ increases, are fundamental to understanding pointwise convergence of Fourier series.

This result is important in Fourier analysis as it provides a more flexible criterion for checking convergence, especially when dealing with functions that might have different behaviors in different regions.

### Dependencies
- **Theorems**:
  - `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF`: Relates Fourier series convergence to an integral over $[0,\pi]$
  - `RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF`: Shows that the integral difference over ranges $[0,\pi]$ and $[0,d]$ tends to zero
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Preserves absolute integrability under periodic offsets
  - `trigonometric_set`: Defines the trigonometric basis functions

- **Definitions**:
  - `fourier_coefficient`: Orthonormal coefficients for the trigonometric basis functions
  - `dirichlet_kernel`: The summation kernel for Fourier series

### Porting notes
When porting this theorem:
1. Ensure that the definition of the Dirichlet kernel is consistent with HOL Light's definition, particularly its behavior at $x = 0$.
2. The theorem relies on several properties of Fourier series and absolute integrability that need to be established first.
3. The proof uses various transformations and localization principles that might require different approaches in other proof assistants, especially those with less automation for real analysis.
4. The periodicity condition is crucial and should be handled carefully, especially in systems where function extension principles are treated differently.

---

## REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND

### REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND
- Theorem that expands the definition of Dirichlet kernel in real integrals

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. real_integral s (\x. dirichlet_kernel n x * f x) =
           real_integral s (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) *
                                f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;
```

### Informal statement
For any function $f$, any natural number $n$, and any set $s$ over which we are integrating, the real integral of the Dirichlet kernel multiplied by $f$ is equal to the real integral of the expanded form of the Dirichlet kernel multiplied by $f$:

$$\int_s \text{dirichlet\_kernel}(n, x) \cdot f(x) \, dx = \int_s \frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} \cdot f(x) \, dx$$

This theorem effectively allows us to replace the Dirichlet kernel with its explicit formula, except at the point $x = 0$ where the kernel has a different value.

### Informal proof
The proof uses the fact that the Dirichlet kernel is defined as:

$$\text{dirichlet\_kernel}(n, x) = \begin{cases}
n + \frac{1}{2} & \text{if } x = 0 \\
\frac{\sin((n + \frac{1}{2})x)}{2\sin(\frac{x}{2})} & \text{otherwise}
\end{cases}$$

The main argument proceeds as follows:

* We apply the `REAL_INTEGRAL_SPIKE` theorem, which states that changing a function's value on a negligible set does not change its integral.
* We specify the set $\{0\}$ as the negligible set where the functions differ.
* We prove that $\{0\}$ is a negligible set using `REAL_NEGLIGIBLE_SING`.
* Finally, we simplify the goal using the definition of Dirichlet kernel, showing that the two functions agree except at $x = 0$.

This demonstrates that the integral remains unchanged when we replace the full definition of the Dirichlet kernel with just its non-zero case formula.

### Mathematical insight
This theorem allows us to simplify calculations involving integrals of the Dirichlet kernel by using its explicit formula without having to handle the special case at $x = 0$ separately. This is useful because:

1. The Dirichlet kernel plays an important role in Fourier analysis, particularly in the convergence of Fourier series.
2. The special case at $x = 0$ is mathematically necessary for the definition but can complicate computations.
3. For integration purposes, a single point (like $x = 0$) is negligible, so we can use the simpler formula throughout.

This result is a technical convenience that streamlines further work with Fourier series and related topics.

### Dependencies
- Definitions:
  - `dirichlet_kernel`: The Dirichlet kernel function defined as described in the informal proof
- Theorems:
  - `REAL_INTEGRAL_SPIKE`: States that changing a function on a negligible set doesn't change its integral
  - `REAL_NEGLIGIBLE_SING`: States that a singleton set (like {0}) is negligible for real integration

### Porting notes
When porting this theorem:
- Ensure your target system has a notion of "negligible set" for integration (often called "null set" or "measure zero set")
- The key insight is that the proof relies on the fact that changing a function on a set of measure zero doesn't affect its integral
- You'll need a version of the `REAL_INTEGRAL_SPIKE` theorem, which is a fundamental result in measure theory and integration

---

## REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND

### REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. (\x. dirichlet_kernel n x * f x) real_integrable_on s <=>
           (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) * f x)
           real_integrable_on s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;
```

### Informal statement
For any function $f$, natural number $n$, and set $s$, the product of the Dirichlet kernel $\text{dirichlet\_kernel } n$ and $f$ is integrable on $s$ if and only if the function $\frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})} \cdot f(x)$ is integrable on $s$. That is:

$$\left(\lambda x.\, \text{dirichlet\_kernel } n \, x \cdot f(x)\right) \text{ integrable on } s \iff \left(\lambda x.\, \frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})} \cdot f(x)\right) \text{ integrable on } s$$

### Informal proof
The proof shows that these two functions differ only at $x = 0$, and a function that differs from another at only a negligible set of points has the same integrability properties.

1. Apply `REAL_INTEGRABLE_SPIKE` in both directions, which states that if two functions differ only on a negligible set, then one is integrable if and only if the other is integrable.

2. Choose the set where the functions differ to be the singleton $\{0\}$, which is negligible as shown by `REAL_NEGLIGIBLE_SING`.

3. Simplify the goal using the definition of set difference and singleton set.

4. Finally, apply the definition of the Dirichlet kernel, which shows that at $x = 0$, the kernel equals $n + \frac{1}{2}$, and at all other points it equals $\frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})}$.

### Mathematical insight
This theorem establishes that the Dirichlet kernel, despite its singularity at $x = 0$, can be treated as the function $\frac{\sin((n + \frac{1}{2}) \cdot x)}{2 \cdot \sin(\frac{x}{2})}$ for integrability purposes. This is important in Fourier analysis, where the Dirichlet kernel is used to study the convergence of Fourier series. The theorem confirms that when considering integrability, we can ignore the special case at $x = 0$ because a single point has measure zero and doesn't affect the integral.

### Dependencies
#### Theorems
- `REAL_INTEGRABLE_SPIKE`: If two functions differ only on a negligible set, then one is integrable if and only if the other is integrable.
- `REAL_NEGLIGIBLE_SING`: A singleton set is negligible with respect to the Lebesgue measure.

#### Definitions
- `dirichlet_kernel`: 
  ```
  dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))
  ```

### Porting notes
When porting this theorem, be aware of how your target system handles:
1. Singularities in functions (the Dirichlet kernel has a removable singularity at x = 0)
2. Measure theory concepts like "negligible sets" (null sets or sets of measure zero)
3. The concept of functions differing only on a set of measure zero being equivalent for integration purposes

---

## FOURIER_SUM_LIMIT_SINE_PART

### FOURIER_SUM_LIMIT_SINE_PART
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_SINE_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. sin((&n + &1 / &2) * x) *
                                     ((f(t + x) + f(t - x)) - &2 * l) / x))
             ---> &0) sequentially)`,
  let lemma0 = prove
   (`!x. abs(sin(x) - x) <= abs(x) pow 3`,
    GEN_TAC THEN MP_TAC(ISPECL [`0`; `Cx x`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; IM_CX] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; COMPLEX_NORM_CX; REAL_ABS_0] THEN
    REWRITE_TAC[REAL_EXP_0; REAL_MUL_LID] THEN REAL_ARITH_TAC) in
  let lemma1 = prove
   (`!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= x pow 2`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs x` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; GSYM(CONJUNCT2 real_pow)] THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; ARITH] THEN
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL; REAL_MUL_RID] THEN
    REWRITE_TAC[lemma0]) in
  let lemma2 = prove
   (`!x. abs(x) <= &1 / &2  ==> abs(x) / &2 <= abs(sin x)`,
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` lemma0) THEN
    MATCH_MP_TAC(REAL_ARITH
      `&4 * x3 <= abs x ==> abs(s - x) <= x3 ==> abs(x) / &2 <= abs s`) THEN
    REWRITE_TAC[REAL_ARITH
     `&4 * x pow 3 <= x <=> x * x pow 2 <= x * (&1 / &2) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. ~(x = &0) /\ abs x <= &1 / &2
         ==> abs(inv(sin x) - inv x) <= &2 * abs x`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(sin x)` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_CASES_TAC `sin x = &0` THENL
     [MP_TAC(SPEC `x:real` SIN_EQ_0_PI) THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_SUB_LDISTRIB; REAL_MUL_RINV] THEN
      REWRITE_TAC[REAL_ARITH `abs(&1 - s * inv x) = abs(s / x - &1)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x:real) pow 2` THEN
      ASM_SIMP_TAC[lemma1] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MP_TAC(ISPEC `x:real` lemma2) THEN ASM_REAL_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `d:real`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN EXISTS_TAC
   `\n. real_integral (real_interval[&0,d])
                      (\x. sin((&n + &1 / &2) * x) *
                           (inv(&2 * sin(x / &2)) - inv x) *
                           ((f(t + x) + f(t - x)) - &2 * l))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND] THEN
    REWRITE_TAC[REAL_ARITH
     `a * (inv y - inv x) * b:real = a / y * b - a / x * b`] THEN
    REWRITE_TAC[REAL_ARITH `sin(y) * (a - b) / x = sin(y) / x * (a - b)`] THEN
    MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
      [ALL_TAC; REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. dirichlet_kernel n x * (&2 * sin(x / &2)) / x *
                      ((f(t + x) + f(t - x)) - &2 * l)` THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN
        REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL; REAL_MUL_ASSOC] THEN
        STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_REWRITE_TAC[dirichlet_kernel] THEN
        MATCH_MP_TAC(REAL_FIELD
         `~(x = &0) /\ ~(y = &0) ==> a / x = a / (&2 * y) * (&2 * y) / x`) THEN
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
        ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                     ABSOLUTELY_REAL_INTEGRABLE_SUB;
                     ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
          REWRITE_TAC[REAL_NEGLIGIBLE_SING; SING_GSPEC] THEN
          CONJ_TAC THEN MATCH_MP_TAC
            REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
          REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
          REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
          REAL_DIFFERENTIABLE_TAC;
          ALL_TAC]]] THEN
    SUBGOAL_THEN `real_bounded (IMAGE (\x. &1 + (x / &2) pow 2)
                                      (real_interval[--pi,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `x = &0` THENL
       [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RID] THEN
        ASM_REAL_ARITH_TAC;
        REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(z - &1) <= y ==> abs(&1 + y) <= B ==> abs(z) <= B`) THEN
        ASM_SIMP_TAC[REAL_FIELD
          `~(x = &0) ==> (&2 * y) / x = y / (x / &2)`] THEN
        MATCH_MP_TAC lemma1 THEN ASM_REAL_ARITH_TAC]];

    SUBGOAL_THEN `real_interval[&0,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC
       [GSYM(MATCH_MP REAL_INTEGRAL_RESTRICT th)])] THEN
    REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
     `(if p x then a x * b x * c x else &0) =
      a x * (if p x then b x else &0) * c x`] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0; SET_RULE `{x | x IN s} = s`;
                  REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_SUB THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV) [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        REWRITE_TAC[REAL_ARITH `&2 * x = &0 <=> x = &0`] THEN
        REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_bounded(IMAGE (\x. inv (&2 * sin (x / &2)) - inv x)
                         (real_interval[--pi,-- &1] UNION
                          real_interval[&1,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      SIMP_TAC[REAL_COMPACT_INTERVAL; REAL_COMPACT_UNION] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `max B (&2)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `abs(x) <= &1` THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_INV_0; SIN_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(is - &2 * ix) <= &1 ==> abs(inv(&2) * is - ix) <= max B (&2)`) THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs(x / &2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma3; ASM_REAL_ARITH_TAC] THEN
    ASM_REAL_ARITH_TAC]);;
```

### Informal statement
This theorem states that for a function $f$ that is absolutely integrable on the interval $[-\pi, \pi]$ and $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$), and for any $d$ such that $0 < d \leq \pi$, the following are equivalent:

1. The partial sums of the Fourier series of $f$ at point $t$ converge to $l$:
   $$\lim_{n\to\infty} \sum_{k=0}^{n} c_k(f) \cdot \text{trigonometric\_set}(k,t) = l$$

2. The following integral approaches zero as $n$ tends to infinity:
   $$\lim_{n\to\infty} \int_0^d \frac{\sin((n+\frac{1}{2})x) \cdot ((f(t+x) + f(t-x)) - 2l)}{x} dx = 0$$

where $c_k(f)$ represents the Fourier coefficients of $f$.

### Informal proof
The proof establishes the equivalence between the convergence of Fourier series and an integral condition. It proceeds in several steps:

1. First, several lemmas about sine function approximations are established:
   - $|\sin(x) - x| \leq |x|^3$
   - For $x \neq 0$, $|\sin(x)/x - 1| \leq x^2$
   - For $|x| \leq 1/2$, $|x|/2 \leq |\sin(x)|$
   - For $x \neq 0$ and $|x| \leq 1/2$, $|\frac{1}{\sin(x)} - \frac{1}{x}| \leq 2|x|$

2. The proof then applies the `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART` theorem to relate the Fourier series convergence to an integral involving the Dirichlet kernel:
   $$\lim_{n\to\infty} \int_0^d \text{dirichlet\_kernel}(n,x) \cdot ((f(t+x) + f(t-x)) - 2l) dx = 0$$

3. The integral with the Dirichlet kernel is transformed into the desired form by using:
   - The Dirichlet kernel is expressed as $\frac{\sin((n+\frac{1}{2})x)}{2\sin(x/2)}$ for $x \neq 0$
   - The difference $\frac{\sin((n+\frac{1}{2})x)}{2\sin(x/2)} - \frac{\sin((n+\frac{1}{2})x)}{x}$ is bounded and the difference in integrals approaches zero

4. Using the Riemann-Lebesgue lemma for sine functions (specifically `RIEMANN_LEBESGUE_SIN_HALF`), the proof shows that the integral of the error term approaches zero as $n$ increases.

5. Various results about absolute integrability are applied to ensure that all the required functions are properly integrable.

### Mathematical insight
This theorem provides a characterization of pointwise convergence of Fourier series in terms of an integral condition. It's a variation of the Dirichlet-Jordan test and connects to the Riemann localization principle. The result is part of the theory analyzing when and how Fourier series converge to the original function.

The alternative characterization using the integral condition is often easier to work with in proofs. This theorem helps bridge between the abstract theory of Fourier series and concrete applications involving specific functions.

The form with $\sin((n+\frac{1}{2})x)/x$ reveals the connection to the sinc function which plays a central role in harmonic analysis and signal processing.

### Dependencies
- Theorems:
  - `trigonometric_set`: Defines the trigonometric basis functions used in Fourier series
  - `RIEMANN_LEBESGUE_SIN_HALF`: A variant of the Riemann-Lebesgue lemma for sine functions
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that a shifted periodic integrable function remains integrable
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`: Ensures that multiplying by the Dirichlet kernel preserves absolute integrability
  - `REAL_SIN_X2_ZEROS`: Characterizes the zeros of $\sin(x/2)$
  - `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART`: Relates Fourier series convergence to an integral with the Dirichlet kernel
  - `REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND`: Expands the integral of the product with the Dirichlet kernel
  - `REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND`: Similar to above for integrability

- Definitions:
  - `fourier_coefficient`: Defined as the orthonormal coefficient with respect to the trigonometric basis
  - `dirichlet_kernel`: Defined as $n+\frac{1}{2}$ for $x=0$ and $\frac{\sin((n+\frac{1}{2})x)}{2\sin(x/2)}$ for $x \neq 0$

### Porting notes
When porting this theorem:
1. First ensure the correct definition of the trigonometric basis and Fourier coefficients
2. The Dirichlet kernel and its properties need to be carefully established
3. Special attention should be paid to how periodicity and absolute integrability are formalized
4. The Riemann-Lebesgue lemma variants are crucial and should be ported first
5. The complex analysis behind the sine function approximations may require different tactics in other systems

---

## FOURIER_DINI_TEST

### FOURIER_DINI_TEST
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_DINI_TEST = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\
        &0 < d /\
        (\x. abs((f(t + x) + f(t - x)) - &2 * l) / x)
        real_integrable_on real_interval[&0,d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `pi`]
                FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[PI_POS; REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `dd = min d (min (k / &2) pi)` THEN
  DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d /\ dd <= pi /\ dd < k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[&0,dd]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`--pi`; `pi`] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_SUB;
                   REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0:real`; `d:real`] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
         [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
                REAL_INTEGRABLE_SPIKE)) THEN
        EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY] THEN
        SIMP_TAC[REAL_ABS_DIV; IN_REAL_INTERVAL; IN_DIFF] THEN
        SIMP_TAC[real_abs];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[dd,pi]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_INV] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (\x. sin((&n + &1 / &2) * x) *
           ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[&0,dd]) /\
    (!n. (\x. sin((&n + &1 / &2) * x) *
          ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[dd,pi])`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
       REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REPEAT STRIP_TAC THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
       REAL_DIFFERENTIABLE_TAC;
       REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
       EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]]);
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. if abs x < dd then &0
                    else ((f:real->real)(t + x) - l) / x`
     RIEMANN_LEBESGUE_SIN_HALF) THEN
  SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[MESON[] `(if P x then if Q x then &0 else a x else &0) =
                         (if P x /\ ~Q x then a x else &0)`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_LZERO]
    `(if P x /\ Q x then a x * b x else &0) =
     (if Q x then a x else &0) * (if P x then b x else &0)`] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0] THEN CONJ_TAC THENL
       [REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
        REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_COMPL] THEN
        REWRITE_TAC[REAL_ARITH `abs x < d <=> --d < x /\ x < d`] THEN
        REWRITE_TAC[GSYM real_interval; REAL_LEBESGUE_MEASURABLE_INTERVAL];
        GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
        MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
        SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
                 REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
                 REAL_CLOSED_UNIV]];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[REAL_NOT_LT] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ABS_NUM;
                   REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_MUL_RNEG; SIN_NEG; REAL_MUL_LNEG] THEN
  REWRITE_TAC[GSYM real_sub; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then &0 else a) - (if p then &0 else --b) =
    (if p then &0 else a + b)`] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `s * (if p then &0 else y) = (if ~p then s * y else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[]
   `(if p then if q then x else &0 else &0) =
    (if p /\ q then x else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < dd /\ dd <= pi
    ==> ((&0 <= x /\ x <= pi) /\ ~(abs x < dd) <=>
         dd <= x /\ x <= pi)`] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[REAL_ARITH `(x - l) + (y - l) = (x + y) - &2 * l`] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `real_integral(real_interval[&0,dd]) f +
    real_integral(real_interval[dd,pi]) f =
    real_integral(real_interval[&0,pi]) f /\
    abs(real_integral(real_interval[&0,dd]) f) < e / &2
    ==> abs(real_integral(real_interval[dd,pi]) f - &0) < e / &2
        ==> abs(real_integral(real_interval[&0,pi]) f) < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `dd:real` THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs x < e / &2 ==> abs y <= x ==> abs y < e / &2`)) THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `d:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SIMP_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ARITH
        `&0 <= x ==> abs x = x`] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x * y <= y <=> x * y <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS; SIN_BOUND]]]);;
```

### Informal statement
This theorem states a condition for the convergence of a Fourier series, known as Dini's test:

For a function $f$ and a real number $t$, if:
1. $f$ is absolutely integrable on the interval $[-\pi,\pi]$
2. $f$ is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$)
3. There exists a real number $d > 0$ such that the function $\frac{|(f(t+x) + f(t-x)) - 2l|}{x}$ is Riemann integrable on the interval $[0,d]$

Then the Fourier series of $f$ at point $t$ converges to the value $l$:

$$\lim_{n \to \infty} \sum_{k=0}^{n} \widehat{f}(k) \cdot \phi_k(t) = l$$

where $\widehat{f}(k)$ is the $k$-th Fourier coefficient of $f$ and $\phi_k$ is the $k$-th trigonometric basis function.

### Informal proof
The proof proceeds by employing the sine part criterion for Fourier series convergence:

1. First, we apply `FOURIER_SUM_LIMIT_SINE_PART` which gives us the equivalent condition for convergence:
   $$\lim_{n \to \infty} \int_0^{\pi} \frac{\sin((n+\frac{1}{2})x)((f(t+x) + f(t-x)) - 2l)}{x} dx = 0$$

2. We establish that the indefinite integral of our function is continuous at the right endpoint. This follows from the integrability assumption.

3. For any given $\varepsilon > 0$, we choose a sufficiently small $\delta = \min(d, \frac{k}{2}, \pi)$ where $k$ is chosen so that the integral over $[0,\delta]$ is less than $\frac{\varepsilon}{2}$.

4. We split the integral into two parts: over $[0,\delta]$ and over $[\delta,\pi]$.

5. For the first part $[0,\delta]$, we show it is absolutely integrable by verifying:
   - The function is measurable (being a quotient of measurable functions)
   - The function is integrable on this subinterval

6. For the second part $[\delta,\pi]$, we again show absolute integrability by:
   - Demonstrating that $\frac{1}{x}$ is bounded on $[\delta,\pi]$ by $\frac{1}{\delta}$
   - Proving the remaining factor is absolutely integrable

7. Using the Riemann-Lebesgue lemma, we show that:
   $$\lim_{n \to \infty} \int_{\delta}^{\pi} \frac{\sin((n+\frac{1}{2})x)((f(t+x) + f(t-x)) - 2l)}{x} dx = 0$$

8. Finally, we combine the results to show that for sufficiently large $n$:
   - The integral over $[0,\delta]$ is less than $\frac{\varepsilon}{2}$
   - The integral over $[\delta,\pi]$ is less than $\frac{\varepsilon}{2}$
   - Therefore, the entire integral over $[0,\pi]$ is less than $\varepsilon$

This completes the proof that the Fourier series of $f$ at point $t$ converges to $l$.

### Mathematical insight
Dini's test is a significant result in the theory of Fourier series that provides a sufficient condition for pointwise convergence. It generalizes the concept of Dirichlet's test to handle functions with certain types of discontinuities.

The key insight is examining the symmetrized behavior of the function around the point of interest. The condition on the integrability of $\frac{|(f(t+x) + f(t-x)) - 2l|}{x}$ is essentially checking that the function doesn't oscillate too wildly near the point $t$, even if it has a jump discontinuity there.

This theorem is especially useful because:
1. It applies to a wide range of functions, including those with certain discontinuities
2. It gives a precise characterization of the limit value at each point
3. It connects the convergence behavior to local properties of the function around the point of interest

Dini's test is considered more general than Dirichlet's conditions and is a powerful tool in analyzing the convergence of Fourier series at specific points.

### Dependencies
- `FOURIER_SUM_LIMIT_SINE_PART`: Relates Fourier series convergence to the convergence of a specific sine integral
- `REAL_INTEGRAL_REFLECT_AND_ADD`: Relates the integral over [-a,a] to integrals over [0,a]
- `trigonometric_set`: Defines the trigonometric basis functions used in Fourier series
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`: Establishes the integrability of products of trigonometric functions with integrable functions
- `RIEMANN_LEBESGUE_SIN_HALF`: A version of the Riemann-Lebesgue lemma for half-integer frequencies
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that a shifted periodic integrable function remains integrable
- `fourier_coefficient`: Definition of Fourier coefficients using orthonormal basis functions

### Porting notes
When porting this theorem:
1. Ensure that the definition of Fourier coefficients and trigonometric basis functions uses the same normalization constants
2. The theorem heavily relies on real analysis concepts like absolute integrability and the Riemann-Lebesgue lemma, which might need to be established first
3. The notion of $2\pi$-periodicity should be precisely defined, as it's essential to the argument
4. The proof makes extensive use of measure theory (particularly to handle the discontinuity at zero in functions like $\frac{f(x)}{x}$)

---

## REAL_INTEGRAL_SIN_OVER_X_BOUND

### Name of formal statement
REAL_INTEGRAL_SIN_OVER_X_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_OVER_X_BOUND = prove
 (`!a b c.
       &0 <= a /\ &0 < c
       ==> (\x. sin(c * x) / x) real_integrable_on real_interval[a,b] /\
           abs(real_integral (real_interval[a,b]) (\x. sin(c * x) / x)) <= &4`,
  let lemma0 = prove
   (`!a b. (\x. sin x) real_integrable_on (real_interval[a,b]) /\
           abs(real_integral (real_interval[a,b]) (\x. sin x)) <= &2`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. --(cos x)`; `\x. sin x`; `a:real`; `b:real`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
         `abs x <= &1 /\ abs y <= &1 ==> abs(--y - --x) <= &2`) THEN
        REWRITE_TAC[COS_BOUND]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma1 = prove
   (`!a b. &0 < a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &4 / a`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. sin x`; `\x:real. --(inv x)`; `a:real`; `b:real`]
              REAL_SECOND_MEAN_VALUE_THEOREM_FULL) THEN
      ASM_REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; lemma0] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `c:real`
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_NEG) THEN
        REWRITE_TAC[REAL_ARITH `--(--(inv y) * x):real = x / y`] THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
        MATCH_MP_TAC(REAL_ARITH
         `inv b <= inv a /\ abs x <= inv a * &2 /\ abs y <= inv b * &2
          ==> abs(x + y) <= &4 / a`) THEN
        ASM_SIMP_TAC[REAL_LE_INV2; REAL_ABS_MUL] THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; lemma0] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL; REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!x. &0 <= x ==> sin(x) <= x`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= &1` THENL
     [ALL_TAC; ASM_MESON_TAC[SIN_BOUNDS; REAL_LE_TOTAL; REAL_LE_TRANS]] THEN
    MP_TAC(ISPECL [`1`; `Cx x`] TAYLOR_CSIN) THEN
    CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; GSYM CX_NEG;
                GSYM CX_ADD; GSYM CX_SUB] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; IM_CX; REAL_ABS_0; REAL_EXP_0] THEN
    SIMP_TAC[REAL_POW_1; REAL_DIV_1; real_pow;
             REAL_MUL_LNEG; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e <= t ==> abs(sin x - (x + --t)) <= e ==> sin x <= x`) THEN
    ASM_REWRITE_TAC[real_abs; REAL_ARITH
     `x pow 5 / &24 <= x pow 3 / &6 <=>
      x pow 3 * x pow 2 <= x pow 3 * &2 pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. &0 <= x /\ x <= &2 ==> abs(sin x / x) <= &1`,
    GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ASM_SIMP_TAC[real_div; REAL_MUL_RZERO; REAL_INV_0;
                   REAL_ABS_NUM; REAL_POS];
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                   REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < abs x`] THEN
      MATCH_MP_TAC(REAL_ARITH `s <= x /\ &0 <= s ==> abs s <= abs x`) THEN
      ASM_SIMP_TAC[lemma2] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC]) in
  let lemma4 = prove
   (`!a b. &0 <= a /\ b <= &2
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &2`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC `(\x. &1):real->real` THEN
        REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[lemma0];
            MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
            REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
            REWRITE_TAC[SING_GSPEC; REAL_NEGLIGIBLE_SING]];
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC];
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `real_integral (real_interval [a,b]) (\x. &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
          ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN ASM_REAL_ARITH_TAC]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma5 = prove
   (`!a b. &0 <= a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b]) (\x. sin x / x)) <= &4`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `b <= &2` THENL
     [ASM_MESON_TAC[lemma4; REAL_ARITH `x <= &2 ==> x <= &4`]; ALL_TAC] THEN
    ASM_CASES_TAC `&2 <= a` THENL
     [MP_TAC(SPECL [`a:real`; `b:real`] lemma1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= a ==> &0 < a`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRABLE_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
        ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= &2 /\ abs(y) <= &2 ==> abs(x + y) <= &4`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &4 / &2`] THEN
      ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
   [MP_TAC(ISPECL [`c * a:real`; `c * b:real`] lemma5) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_REAL_INTEGRAL_INTEGRAL] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     HAS_REAL_INTEGRAL_STRETCH)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    ASM_SIMP_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
      REAL_FIELD `&0 < c ==> inv c * c * a = a`; REAL_INV_MUL; real_div;
      REAL_FIELD `&0 < c ==> c * s * inv c * inv x = s * inv x`;
      REAL_FIELD `&0 < c ==> c * inv c * i = i /\ abs c = c`] THEN
    REWRITE_TAC[GSYM real_div; REAL_INTERVAL_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_LMUL_EQ] THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                 REAL_ABS_NUM; REAL_POS]]);;
```

### Informal statement
For all real numbers $a$, $b$, and $c$, if $0 \leq a$ and $0 < c$, then:
- The function $f(x) = \frac{\sin(cx)}{x}$ is Riemann integrable on the interval $[a,b]$, and
- The absolute value of the integral $\left|\int_{a}^{b} \frac{\sin(cx)}{x} dx\right| \leq 4$.

### Informal proof
This proof involves establishing several intermediate lemmas to reach the final result:

**Lemma 0**: For any interval $[a,b]$, $\sin(x)$ is integrable on $[a,b]$ and $\left|\int_{a}^{b} \sin(x) dx\right| \leq 2$.
- This follows from the Fundamental Theorem of Calculus, as $\sin(x)$ is the derivative of $-\cos(x)$.
- Since $|\cos(x)| \leq 1$ for all $x$, we have $\left|\int_{a}^{b} \sin(x) dx\right| = |-\cos(b) - (-\cos(a))| \leq 2$.

**Lemma 1**: If $0 < a$, then $\frac{\sin(x)}{x}$ is integrable on $[a,b]$ and $\left|\int_{a}^{b} \frac{\sin(x)}{x} dx\right| \leq \frac{4}{a}$.
- This uses the Second Mean Value Theorem to handle the division by $x$.

**Lemma 2**: If $0 \leq x$, then $\sin(x) \leq x$.
- This is proven using Taylor's theorem for sine, showing that the error term is bounded appropriately.

**Lemma 3**: If $0 \leq x \leq 2$, then $\left|\frac{\sin(x)}{x}\right| \leq 1$.
- This combines Lemma 2 with the fact that $\sin(x)$ is positive in this range.

**Lemma 4**: If $0 \leq a$ and $b \leq 2$, then $\frac{\sin(x)}{x}$ is integrable on $[a,b]$ and $\left|\int_{a}^{b} \frac{\sin(x)}{x} dx\right| \leq 2$.
- This follows from Lemma 3 by bounding the integrand.

**Lemma 5**: If $0 \leq a$, then $\frac{\sin(x)}{x}$ is integrable on $[a,b]$ and $\left|\int_{a}^{b} \frac{\sin(x)}{x} dx\right| \leq 4$.
- This considers cases based on whether $b \leq 2$ or $b > 2$, and whether $a \geq 2$ or $a < 2$.
- For $b \leq 2$, we apply Lemma 4.
- For $b > 2$, we split the integral at $x = 2$ and apply previous lemmas to bound each part.

**Main Theorem Proof**:
- For the case where $a \leq b$, we apply the variable substitution $u = cx$ to convert to the form addressed by Lemma 5.
- We use the fact that $\frac{\sin(cx)}{x} = c \cdot \frac{\sin(u)}{u}$ under this substitution.
- For the case where $a > b$, the result is trivial as the integral is zero.

### Mathematical insight
This theorem establishes a uniform bound on the integral of $\frac{\sin(cx)}{x}$ over any interval $[a,b]$ with $a \geq 0$. This function is particularly important in Fourier analysis and signal processing.

The key insight is that despite the apparent singularity at $x=0$ (when $a=0$), the integral remains bounded. This is because $\sin(cx)$ approaches zero as $x$ approaches zero, and it does so fast enough to make the quotient $\frac{\sin(cx)}{x}$ well-behaved near the origin.

The uniform bound of 4 is tight and independent of the parameter $c$, which makes this result particularly useful in applications where such integrals appear.

### Dependencies
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`: For computing the integral of sine
- `REAL_SECOND_MEAN_VALUE_THEOREM_FULL`: Used in Lemma 1
- `TAYLOR_CSIN`: Used in Lemma 2 to bound sine
- `SIN_BOUNDS`: For bounding sine values
- `SIN_POS_PI_LE`: For determining where sine is positive
- `REAL_INTEGRABLE_COMBINE` and `REAL_INTEGRAL_COMBINE`: For splitting integrals
- `HAS_REAL_INTEGRAL_STRETCH` and `HAS_REAL_INTEGRAL_LMUL`: For variable substitution

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-developed theory of integration, particularly for handling improper integrals.
2. The proof relies heavily on mean value theorems and properties of trigonometric functions, so these should be available.
3. The variable substitution technique used in the main proof requires careful handling of bounds and coefficients.
4. The bound of 4 is exact, and any automation in the target system should be careful not to overapproximate.

---

## FOURIER_JORDAN_BOUNDED_VARIATION

### FOURIER_JORDAN_BOUNDED_VARIATION

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_JORDAN_BOUNDED_VARIATION = prove
 (`!f x d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        &0 < d /\
        f has_bounded_real_variation_on real_interval[x - d,x + d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k x))
             ---> ((reallim (atreal x within {l | l <= x}) f +
                    reallim (atreal x within {r | r >= x}) f) / &2))
            sequentially`,
  let lemma = prove
   (`!f l d. &0 < d
             ==> ((f ---> l) (atreal (&0) within real_interval[&0,d]) <=>
                  (f ---> l) (atreal (&0) within {x | &0 <= x}))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_TRANSFORM_WITHINREAL_SET THEN
    REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC) in
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `d0:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `s = (reallim (atreal t within {l | l <= t}) f +
                   reallim (atreal t within {r | r >= t}) f) / &2` THEN
  MP_TAC(SPECL [`f:real->real`; `t:real`; `s:real`; `min d0 pi`]
        FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; PI_POS; REAL_ARITH `min d0 pi <= pi`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - &2 * s` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN ABBREV_TAC `d = min d0 pi` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `h has_bounded_real_variation_on real_interval[&0,d]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[HAS_BOUNDED_REAL_VARIATION_DARBOUX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`f1:real->real`; `f2:real->real`] THEN STRIP_TAC THEN
    EXISTS_TAC `\x. ((f1:real->real)(t + x) - f2(t - x)) - s` THEN
    EXISTS_TAC `\x. ((f2:real->real)(t + x) - f1(t - x)) + s` THEN
    ASM_REWRITE_TAC[REAL_ARITH `x - s <= y - s <=> x <= y`; REAL_LE_RADD] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `a <= a' /\ b' <= b ==> a - b <= a' - b'`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_ARITH
     `(f' + f) - &2 * (l + l') / &2 = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {l | l <= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC];
      SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {r | r >= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < d /\
        !n. (\x. sin ((&n + &1 / &2) * x) * h x / x)
            real_integrable_on real_interval[&0,k] /\
            abs(real_integral (real_interval[&0,k])
                              (\x. sin ((&n + &1 / &2) * x) * h x / x))
              <= e / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?h1 h2.
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h1 x <= h1 y) /\
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h2 x <= h2 y) /\
         (h1 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (h2 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (!x. h x = h1 x - h2 x)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`h:real->real`; `&0`; `d:real`]
          HAS_BOUNDED_REAL_VARIATION_DARBOUX) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`h1:real->real`; `h2:real->real`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`h1:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
      MP_TAC(ISPECL [`h2:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l':real`) THEN
      SUBGOAL_THEN `l':real = l` SUBST_ALL_TAC THENL
       [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
        MATCH_MP_TAC(ISPEC `atreal (&0) within {x | &0 <= x}`
          REALLIM_UNIQUE) THEN
        EXISTS_TAC `h:real->real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [W(MP_TAC o PART_MATCH (lhs o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
            rand o snd) THEN
          REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN
          ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC[EXTENSION; NOT_FORALL_THM; IN_ELIM_THM; IN_SING] THEN
          EXISTS_TAC `&1` THEN REAL_ARITH_TAC;
          GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_SUB THEN
          MAP_EVERY UNDISCH_TAC
           [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
            `(h2 ---> l') (atreal(&0) within real_interval[&0,d])`] THEN
          ASM_SIMP_TAC[lemma]];
        EXISTS_TAC `\x. (h1:real->real)(x) - l` THEN
        EXISTS_TAC `\x. (h2:real->real)(x) - l` THEN
        ASM_REWRITE_TAC[REAL_ARITH `x - l <= y - l <=> x <= y`] THEN
        ASM_REWRITE_TAC[GSYM REALLIM_NULL] THEN
        MAP_EVERY UNDISCH_TAC
         [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
          `(h2 ---> l) (atreal(&0) within real_interval[&0,d])`] THEN
        ASM_SIMP_TAC[lemma] THEN REPEAT DISCH_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?k. &0 < k /\ k < d /\ abs(h1 k) < e / &16 /\ abs(h2 k) < e / &16`
    MP_TAC THENL
     [UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k1:real` STRIP_ASSUME_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k2:real` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `min d (min k1 k2) / &2` THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h1:real->real`;
                     `&0`; `k:real`; `&0`; `(h1:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h1:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h2:real->real`;
                     `&0`; `k:real`; `&0`; `(h2:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h2:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)] THEN
    REWRITE_TAC[REAL_ARITH
     `s * (h - h') / x:real = s * h / x - s * h' / x`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRAL_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= e / &16 * &4 /\ abs(y) <= e / &16 * &4
      ==> abs(x - y) <= e / &2`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 < &n + &1 / &2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. h x / x) absolutely_real_integrable_on real_interval[k,d]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      EXISTS_TAC `inv k:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. sin((&n + &1 / &2) * x) * h x / x) absolutely_real_integrable_on
        real_interval[k,d]`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x. if k <= x /\ x <= d then h x / x else &0`
        RIEMANN_LEBESGUE_SIN_HALF) THEN
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REWRITE_TAC[MESON[REAL_ABS_NUM]
   `abs(if p then x else &0) = if p then abs x else &0`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV; GSYM
                   REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `(if P then s * (if Q then a else &0) else &0) =
    (if P /\ Q then s * a else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[MESON[] `(if P then if Q then x else &0 else &0) =
                       (if P /\ Q then x else &0)`] THEN
  SUBGOAL_THEN `!x. (--pi <= x /\ x <= pi) /\ k <= x /\ x <= d <=>
                    k <= x /\ x <= d`
   (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV;
              REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `n:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x + y = z ==> abs(x) <= e / &2 ==> abs(y) < e / &2 ==> abs(z) < e`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `k:real` THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
Let $f$ be a function satisfying the following conditions:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$
- $d > 0$
- $f$ has bounded variation on the interval $[x-d, x+d]$

Then the Fourier series of $f$ at point $x$ converges to the average of the left and right limits of $f$ at $x$:

$$\lim_{n \to \infty} \sum_{k=0}^{n} \hat{f}(k) \cdot \phi_k(x) = \frac{f(x-)+ f(x+)}{2}$$

where:
- $\hat{f}(k)$ is the $k$-th Fourier coefficient of $f$
- $\phi_k(x)$ is the $k$-th trigonometric function in the orthonormal basis
- $f(x-)$ denotes the limit from the left $\lim_{t \to x^-} f(t)$
- $f(x+)$ denotes the limit from the right $\lim_{t \to x^+} f(t)$

### Informal proof
This theorem is a version of the classical Dirichlet-Jordan theorem, which states that the Fourier series of a function of bounded variation converges pointwise to the average of the left and right limits.

The proof proceeds through several key steps:

1. First, we introduce a lemma showing that the limit at $0$ within the interval $[0,d]$ is equivalent to the limit within the right half-line $\{x : x \geq 0\}$.

2. We abbreviate the target value $s = \frac{f(t-) + f(t+)}{2}$ (the average of left and right limits) and introduce the function $h(u) = (f(t+u) + f(t-u)) - 2s$.

3. We show that $h$ has bounded variation on $[0,d]$ using the bounded variation property of $f$.

4. We prove that $h$ approaches $0$ as $u$ approaches $0$ from the right, by showing that:
   - $f$ has a limit from the left at $t$ (using the bounded variation property)
   - $f$ has a limit from the right at $t$ (using the bounded variation property)
   - These limits equal the values used in defining $s$

5. We apply the Fourier sum limit method (FOURIER_SUM_LIMIT_SINE_PART) to transform our goal into showing that:
   $$\lim_{n \to \infty} \int_0^d \frac{\sin((n+\frac{1}{2})x) \cdot h(x)}{x} dx = 0$$

6. For the function $h$ with bounded variation, we decompose it as the difference of two increasing functions $h_1$ and $h_2$.

7. We choose a small $k < d$ such that both $h_1(k)$ and $h_2(k)$ are close to zero.

8. We apply the Second Mean Value Theorem for integrals to handle the integrals involving $h_1$ and $h_2$.

9. For the remaining parts, we use the Riemann-Lebesgue lemma to show that:
   $$\lim_{n \to \infty} \int_k^d \frac{\sin((n+\frac{1}{2})x) \cdot h(x)}{x} dx = 0$$

10. Combining these results, we obtain the desired convergence of the Fourier series.

### Mathematical insight
This theorem is a key result in Fourier analysis, known as the Dirichlet-Jordan theorem. It provides sufficient conditions for pointwise convergence of Fourier series. While the standard Dirichlet theorem requires continuity for convergence, the Jordan extension shows that bounded variation is sufficient, with the series converging to the average of left and right limits at each point.

The bounded variation condition is particularly useful because:
1. It encompasses functions with jump discontinuities (common in physical applications)
2. It includes all continuously differentiable functions
3. It allows for the decomposition of a function into the difference of two monotone functions

This result highlights the connection between smoothness properties of a function and the convergence behavior of its Fourier series, which is fundamental in harmonic analysis and signal processing.

### Dependencies
- `trigonometric_set`: Defines the orthonormal trigonometric basis functions
- `fourier_coefficient`: Definition of Fourier coefficients based on orthonormal coefficients
- `FOURIER_SUM_LIMIT_SINE_PART`: Relates Fourier series convergence to a specific integral involving sine functions
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that shifting a periodic absolutely integrable function preserves the integrability property
- `REAL_INTEGRAL_SIN_OVER_X_BOUND`: Provides bounds for integrals involving sine functions divided by x
- `RIEMANN_LEBESGUE_SIN_HALF`: A variant of the Riemann-Lebesgue lemma for integrals with sine factors

### Porting notes
When porting this theorem:
1. You'll need to ensure your system has a well-defined notion of bounded variation. This is typically defined as the supremum of sums of absolute differences over all partitions of an interval.
2. The proof relies heavily on the Second Mean Value Theorem for integrals, which should be available or derivable in most proof assistants.
3. The Riemann-Lebesgue lemma is used in a critical way, and your target system should have this or be able to prove it.
4. The decomposition of functions of bounded variation into differences of monotone functions is an important technique used here.
5. Consider whether your target system uses a different orthonormal basis for Fourier series; adjustments may be needed.

---

## FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE

### FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE = prove
 (`!f x. f has_bounded_real_variation_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k x))
              ---> ((reallim (atreal x within {l | l <= x}) f +
                     reallim (atreal x within {r | r >= x}) f) / &2))
             sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_JORDAN_BOUNDED_VARIATION THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INCREASING THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!n. integer n
          ==> f has_bounded_real_variation_on
              real_interval [(&2 * n - &1) * pi,(&2 * n + &1) * pi]`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&2 * --n * pi` o
       MATCH_MP HAS_BOUNDED_REAL_VARIATION_TRANSLATION) THEN
      REWRITE_TAC[INTEGER_NEG; GSYM REAL_INTERVAL_TRANSLATION] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
      DISCH_THEN(MP_TAC o GEN `x:real` o SPECL [`x:real`; `--n:real`]) THEN
      ASM_REWRITE_TAC[REAL_ARITH `x + n * &2 * pi = &2 * n * pi + x`] THEN
      ASM_REWRITE_TAC[INTEGER_NEG] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. f has_bounded_real_variation_on
          real_interval[--pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID] THEN
      MP_TAC(ISPECL [`f:real->real`; `--pi`; `&((2 + 2 * n) + 1) * pi`;
                     `&(2 * n + 1) * pi`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `--pi = --(&1) * pi`] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
         `(&2 * n + &1) * pi = (&2 * (n + &1) - &1) * pi`] THEN
        REWRITE_TAC[REAL_ARITH
         `((&2 + &2 * n) + &1) * pi = (&2 * (n + &1) + &1) * pi`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m n. f has_bounded_real_variation_on
            real_interval[--(&(2 * m + 1)) * pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID; REAL_MUL_LNEG] THEN
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`f:real->real`; `--(&((2 + 2 * m) + 1) * pi)`;
                     `&(2 * n + 1) * pi`; `--(&(2 * m + 1) * pi)`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        REWRITE_TAC[REAL_LE_NEG2; REAL_ARITH `--a <= b <=> &0 <= a + b`] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
          `--(&2 * m + &1) = &2 * --(m + &1) + &1`] THEN
        REWRITE_TAC[REAL_ARITH
          `--((&2 + &2 * m) + &1) = &2 * --(m + &1) - &1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `&2 * pi` REAL_ARCH) THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `abs x + &3`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC HAS_BOUNDED_REAL_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `real_interval[-- &(2 * N + 1) * pi,&(2 * N + 1) * pi]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For any function $f$ that has bounded variation on the interval $[-\pi, \pi]$ and is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$), the sequence of partial sums of the Fourier series
$$ \left(\sum_{k=0}^n c_k(f) \cdot t_k(x)\right)_{n=0}^{\infty}$$
converges to $\frac{f(x-) + f(x+)}{2}$, where:
- $c_k(f)$ is the $k$-th Fourier coefficient of $f$
- $t_k(x)$ is the $k$-th trigonometric basis function
- $f(x-)$ is the left-hand limit of $f$ at $x$, i.e., $\lim_{t \to x, t \leq x} f(t)$
- $f(x+)$ is the right-hand limit of $f$ at $x$, i.e., $\lim_{t \to x, t \geq x} f(t)$

### Informal proof
This theorem is a simplified version of the more general Fourier-Jordan theorem for functions of bounded variation. The proof proceeds as follows:

- Apply the more general theorem `FOURIER_JORDAN_BOUNDED_VARIATION`, which requires:
  * $f$ is absolutely integrable on $[-\pi, \pi]$
  * $f$ is $2\pi$-periodic
  * For some $d > 0$, $f$ has bounded variation on $[x-d, x+d]$

- We set $d = 1$ and need to verify these conditions:
  
  1. First, we prove that $f$ is absolutely integrable on $[-\pi, \pi]$:
     * Use the Darboux characterization of bounded variation functions
     * This gives us that $f$ can be written as the difference of two increasing functions
     * Each increasing function is absolutely integrable (by `ABSOLUTELY_REAL_INTEGRABLE_INCREASING`)
     * Therefore, their difference $f$ is also absolutely integrable

  2. Second, we verify that $f$ has bounded variation on $[x-1, x+1]$:
     * Prove an intermediate result that $f$ has bounded variation on $[(2n-1)\pi, (2n+1)\pi]$ for any integer $n$
       * This follows from the $2\pi$-periodicity of $f$ and the translation property of bounded variation functions
     
     * Show that $f$ has bounded variation on $[-\pi, (2n+1)\pi]$ for any natural number $n$
       * Prove by induction, using the property that bounded variation extends across intervals
     
     * Extend to show $f$ has bounded variation on $[-(2m+1)\pi, (2n+1)\pi]$ for any natural numbers $m, n$
       * Again use induction and combination of bounded variation intervals
     
     * By the Archimedean property, for any $x$ we can find a sufficiently large $N$ such that the interval $[x-1, x+1]$ is contained in $[-(2N+1)\pi, (2N+1)\pi]$
     
     * By the subset property of bounded variation, $f$ has bounded variation on $[x-1, x+1]$

- Since all conditions of the more general theorem are satisfied, the desired result follows.

### Mathematical insight
This theorem is a special case of the Fourier-Jordan bounded variation theorem, which describes the pointwise convergence of Fourier series for functions of bounded variation. The key insight is that functions of bounded variation can be expressed as the difference of two monotone functions, which have well-defined limits from the left and right at every point.

The result connects the convergence behavior of Fourier series to the one-sided limits of the function. At points of continuity, where the left and right limits are equal, the Fourier series converges to the function value. At points of discontinuity, it converges to the average of the left and right limits.

This theorem is important because it provides a significant extension beyond continuous functions, establishing pointwise convergence behavior for a much broader class of functions (those with bounded variation).

### Dependencies
- `FOURIER_JORDAN_BOUNDED_VARIATION`: The more general theorem on convergence of Fourier series for functions of bounded variation with additional conditions
- `trigonometric_set`: Definition of the trigonometric basis functions
- `REAL_PERIODIC_INTEGER_MULTIPLE`: Relates periodicity with period $a$ to periodicity with integer multiples of $a$
- `HAS_BOUNDED_REAL_VARIATION_DARBOUX`: Characterizes bounded variation functions as differences of increasing functions
- `HAS_BOUNDED_REAL_VARIATION_TRANSLATION`: Translation property of bounded variation
- `HAS_BOUNDED_REAL_VARIATION_ON_COMBINE`: Combination property for bounded variation on adjacent intervals
- `HAS_BOUNDED_REAL_VARIATION_ON_SUBSET`: Subset property for bounded variation
- `ABSOLUTELY_REAL_INTEGRABLE_INCREASING`: Increasing functions are absolutely integrable
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`: Difference of absolutely integrable functions is absolutely integrable
- `REAL_ARCH`: Archimedean property of real numbers

### Porting notes
When porting this theorem:
1. Ensure the target system has a theory of functions of bounded variation
2. Check that the notion of Fourier coefficients and trigonometric basis functions match
3. The proof relies heavily on properties of bounded variation that might need to be established first
4. The periodicity and Archimedean arguments require careful handling of real arithmetic
5. Be attentive to how the target system handles limits (one-sided limits in particular)

---

## fejer_kernel

### Name of formal statement
fejer_kernel

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let fejer_kernel = new_definition
  `fejer_kernel n x = if n = 0 then &0
                      else sum(0..n-1) (\r. dirichlet_kernel r x) / &n`;;
```

### Informal statement
The Fejer kernel $F_n(x)$ is defined for $n \in \mathbb{N}$ and $x \in \mathbb{R}$ as:

$$F_n(x) = \begin{cases}
0 & \text{if } n = 0 \\
\frac{1}{n}\sum_{r=0}^{n-1} D_r(x) & \text{if } n > 0
\end{cases}$$

where $D_r(x)$ is the Dirichlet kernel.

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
The Fejer kernel is a fundamental concept in Fourier analysis, especially for proving the convergence of Fourier series. While the Dirichlet kernel $D_n$ is used in the partial sums of Fourier series, the Fejer kernel represents the arithmetic mean (Cesàro mean) of the first $n$ Dirichlet kernels.

The key properties of the Fejer kernel include:
1. It is non-negative everywhere, unlike the Dirichlet kernel
2. Its integral over $[-\pi, \pi]$ equals $2\pi$
3. It concentrates around zero as $n$ increases, behaving like an approximate identity

These properties make the Fejer kernel particularly useful in proving Fejer's theorem, which states that the Cesàro means of the Fourier series of a continuous function converge uniformly to the function. This provides a more robust convergence result than can be obtained with the Dirichlet kernel alone.

### Dependencies
#### Definitions
- `dirichlet_kernel`: Defines the Dirichlet kernel $D_n(x)$, which is used in the partial sums of Fourier series

### Porting notes
When porting this definition:
1. Ensure the underlying `dirichlet_kernel` definition is ported correctly first
2. Be careful with the indexing of the sum (from 0 to n-1)
3. Note that the HOL Light type system implicitly requires n to be a natural number and x to be a real number

---

## FEJER_KERNEL

### FEJER_KERNEL
- `FEJER_KERNEL`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FEJER_KERNEL = prove
 (`fejer_kernel n x =
        if n = 0 then &0
        else if x = &0 then &n / &2
        else sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2)`,
  REWRITE_TAC[fejer_kernel; dirichlet_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[SUM_0] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG;
                REWRITE_RULE[ETA_AX] SUM_NUMBERS] THEN
    ASM_SIMP_TAC[SUB_ADD; GSYM REAL_OF_NUM_SUB; LE_1; SUB_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `sin(x / &2) = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; real_div;
                    REAL_INV_0; SUM_0; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) /\ ~(s = &0) /\ &2 * s pow 2 * l = r
    ==> l / n = r / (&2 * n * s pow 2)`) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(s = &0) ==> &2 * s pow 2 * a / (&2 * s) = s * a`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 - (&n + &1 / &2) * x = --(&n * x)`;
              REAL_ARITH `x / &2 + (&n + &1 / &2) * x = (&n + &1) * x`] THEN
  REWRITE_TAC[real_div; SUM_RMUL; COS_NEG; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[SUM_DIFFS; LE_0; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; REAL_SUB_COS] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; real_div; REAL_MUL_AC] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
The Fejer kernel function can be expressed as:

$$\text{fejer\_kernel}(n, x) = \begin{cases} 
0 & \text{if } n = 0 \\
\frac{n}{2} & \text{if } n > 0 \text{ and } x = 0 \\
\frac{\sin^2(\frac{nx}{2})}{2n\sin^2(\frac{x}{2})} & \text{if } n > 0 \text{ and } x \neq 0
\end{cases}$$

This theorem provides an explicit closed-form expression for the Fejer kernel in terms of trigonometric functions.

### Informal proof
The proof begins by applying the definitions of `fejer_kernel` and `dirichlet_kernel`:

* First, handle the case when $n = 0$ directly from the definition.

* When $x = 0$:
  - Expand the sum in the definition: $\frac{1}{n}\sum_{r=0}^{n-1}(r + \frac{1}{2})$
  - Apply `SUM_ADD_NUMSEG` and `SUM_CONST_NUMSEG` to split this into simpler sums
  - Use the formula for the sum of natural numbers (from `SUM_NUMBERS`): $\sum_{r=0}^{n-1}r = \frac{(n-1)n}{2}$
  - Simplify algebraically to get $\frac{n}{2}$

* When $x \neq 0$:
  - Consider the special case when $\sin(\frac{x}{2}) = 0$, which is handled separately
  - For the general case, rewrite the sum of dirichlet kernels using trigonometric identities
  - Convert the sum of cosines by applying the formula for $\sum_{r=0}^{n-1}\cos(rx)$, which can be expressed in closed form
  - Use trigonometric identities and algebraic manipulations to simplify the expression to $\frac{\sin^2(\frac{nx}{2})}{2n\sin^2(\frac{x}{2})}$

The core of the proof uses the sum of cosine formula and trigonometric identities to transform the original definition involving a sum into a closed form expression.

### Mathematical insight
The Fejer kernel is a fundamental concept in Fourier analysis, particularly in the theory of Fourier series. It provides a way to construct the Cesàro means of Fourier series, which have better convergence properties than the partial sums of Fourier series.

The closed-form expression proven here is significant because:
1. It transforms a sum definition into an explicit formula, making both theoretical analysis and computation more efficient
2. It shows the Fejer kernel is always non-negative (due to the squared sine term in the numerator), which is crucial for proving convergence properties
3. It helps establish the Fejer kernel as an approximation to the identity operator, which is useful in proving convergence of Fourier series under Cesàro summation

This result plays an important role in harmonic analysis and the theory of function approximation.

### Dependencies
- **Definitions**
  - `fejer_kernel`: defined as the normalized sum of Dirichlet kernels
  - `dirichlet_kernel`: defined as a specific trigonometric function 

- **Theorems**
  - `SUM_NUMBERS`: formula for the sum of the first $n$ natural numbers
  - Various standard theorems about sums and trigonometric identities

### Porting notes
When porting this theorem:
- The proof relies heavily on trigonometric identities and algebraic manipulations
- Special attention should be paid to how divisibility conditions are handled for the case distinctions
- The definition of the Dirichlet kernel should be ported before attempting this proof
- The manipulations of sums and application of the sum of cosines formula are key steps that would need corresponding theorems in the target system

---

## FEJER_KERNEL_CONTINUOUS_STRONG

### FEJER_KERNEL_CONTINUOUS_STRONG
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FEJER_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (fejer_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; DIRICHLET_KERNEL_CONTINUOUS_STRONG]);;
```

### Informal statement
For all natural numbers $n$, the Fejer kernel of order $n$ is real-continuous on the real interval $[-2\pi, 2\pi]$.

In symbols: $\forall n. \text{fejer\_kernel}(n) \text{ real\_continuous\_on } \text{real\_interval}(-2\pi, 2\pi)$

### Informal proof
The proof establishes that the Fejer kernel is continuous on the interval $[-2\pi, 2\pi]$ for any natural number $n$.

* First, we consider the case when $n = 0$:
  - By definition, $\text{fejer\_kernel}(0) = 0$
  - A constant function is continuous, so this case is trivial.

* For the case where $n \neq 0$:
  - The Fejer kernel is defined as: $\text{fejer\_kernel}(n)(x) = \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r)(x)$
  - We rewrite the division as multiplication by the reciprocal: $\frac{1}{n} = \text{real\_mul}(\frac{1}{n})$
  - The sum $\sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r)(x)$ is continuous as:
    * Each Dirichlet kernel $\text{dirichlet\_kernel}(r)$ is continuous on $[-2\pi, 2\pi]$ by theorem `DIRICHLET_KERNEL_CONTINUOUS_STRONG`
    * The sum of continuous functions is continuous
  - Multiplication by the constant $\frac{1}{n}$ preserves continuity
  - Therefore, the Fejer kernel is continuous on $[-2\pi, 2\pi]$

### Mathematical insight
The Fejer kernel is a fundamental tool in Fourier analysis, particularly in the study of convergence of Fourier series. It represents a type of averaging of Dirichlet kernels, which helps smooth out the oscillatory behavior of Fourier series.

The continuity of the Fejer kernel on $[-2\pi, 2\pi]$ is crucial for many results in harmonic analysis, including Fejer's theorem on the convergence of Fourier series. This result shows that the mathematical definition of the Fejer kernel has the expected analytical properties needed for its applications.

The Fejer kernel has better convergence properties than the Dirichlet kernel, particularly because it is non-negative everywhere, which makes it particularly useful for proving density results and approximation theorems.

### Dependencies
- **Theorems**:
  - `DIRICHLET_KERNEL_CONTINUOUS_STRONG`: The Dirichlet kernel is continuous on the interval $[-2\pi, 2\pi]$
  - `REAL_CONTINUOUS_ON_CONST`: Constant functions are continuous
  - `REAL_CONTINUOUS_ON_RMUL`: Multiplication by a real constant preserves continuity
  - `REAL_CONTINUOUS_ON_SUM`: The sum of continuous functions is continuous
  - `FINITE_NUMSEG`: The natural number interval is finite

- **Definitions**:
  - `fejer_kernel`: The Fejer kernel of order n is defined as 0 if n=0, or otherwise as the average of the first n Dirichlet kernels

### Porting notes
When porting this theorem:
- Ensure that your system has the proper definition of continuity for real functions on closed intervals
- The Fejer kernel definition should be carefully checked as it involves a summation of Dirichlet kernels
- The handling of the special case where n=0 might need explicit attention in some proof assistants

---

## FEJER_KERNEL_CONTINUOUS

### Name of formal statement
FEJER_KERNEL_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL_CONTINUOUS = prove
 (`!n. (fejer_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[FEJER_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the Fejer kernel function $\text{fejer\_kernel}(n)$ is real continuous on the closed interval $[-\pi, \pi]$.

### Informal proof
The proof shows that the Fejer kernel is continuous on $[-\pi, \pi]$ by using a stronger result and a subset relation:

1. We apply the theorem `REAL_CONTINUOUS_ON_SUBSET`, which states that if a function is continuous on a set $A$ and $B \subseteq A$, then the function is continuous on $B$.

2. We choose the open interval $(-2\pi, 2\pi)$ as our superset.

3. We use the previously established theorem `FEJER_KERNEL_CONTINUOUS_STRONG`, which states that the Fejer kernel is continuous on the interval $(-2\pi, 2\pi)$.

4. Finally, we verify that $[-\pi, \pi] \subseteq (-2\pi, 2\pi)$ using `SUBSET_REAL_INTERVAL` and the fact that $\pi > 0$ (`PI_POS`), which is established by real arithmetic.

### Mathematical insight
The Fejer kernel is a fundamental tool in Fourier analysis and the theory of trigonometric series. It is defined as:

$$\text{fejer\_kernel}(n)(x) = \begin{cases}
0 & \text{if } n = 0 \\
\frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r)(x) & \text{if } n > 0
\end{cases}$$

This theorem establishes the continuity of the Fejer kernel on the standard interval $[-\pi, \pi]$, which is crucial for many applications in harmonic analysis. The continuity property is essential when using the Fejer kernel for approximation of periodic functions, as it ensures that the approximation behaves well.

This result is derived from a stronger version (`FEJER_KERNEL_CONTINUOUS_STRONG`) that proves continuity on a wider interval. This approach is common in analysis: prove a stronger property and then derive specific cases as needed.

### Dependencies
- **Theorems**:
  - `FEJER_KERNEL_CONTINUOUS_STRONG`: The Fejer kernel is continuous on $(-2\pi, 2\pi)$
  - `REAL_CONTINUOUS_ON_SUBSET`: Continuity preserved on subsets
  - `PI_POS`: $\pi > 0$
  - `SUBSET_REAL_INTERVAL`: Subset relation for real intervals
  
- **Definitions**:
  - `fejer_kernel`: Definition of the Fejer kernel function

### Porting notes
When porting this theorem to another system:
1. Ensure that the Fejer kernel and Dirichlet kernel are properly defined first
2. The proof relies on standard results about continuity being preserved under restriction to subsets 
3. Make sure that interval notations are consistent with the target system's conventions (closed versus open intervals)
4. The main theorem and its stronger version might be combined in other systems, depending on how interval types are handled

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. fejer_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;
```

### Informal statement
For any function $f$ and natural number $n$, if $f$ is absolutely integrable on the real interval $[-\pi, \pi]$, then the product of the Fejér kernel of degree $n$ and $f$, given by $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(x)$, is also absolutely integrable on the real interval $[-\pi, \pi]$.

### Informal proof
To prove this theorem, we apply a general result about the absolute integrability of products of bounded measurable functions. The proof proceeds as follows:

- We apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`, which states that if $f$ is absolutely integrable on a set $s$ and $g$ is both bounded and measurable on $s$, then their product $x \mapsto g(x) \cdot f(x)$ is absolutely integrable on $s$.

- We need to prove two conditions about the Fejér kernel:
  1. The Fejér kernel $\text{fejer\_kernel}(n)$ is measurable on $[-\pi, \pi]$.
  2. The Fejér kernel $\text{fejer\_kernel}(n)$ is bounded on $[-\pi, \pi]$.

- For the first condition, we use the fact that any continuous function on a closed subset is measurable, applying `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`. The Fejér kernel is continuous on $[-\pi, \pi]$ by `FEJER_KERNEL_CONTINUOUS`, and $[-\pi, \pi]$ is a closed interval by `REAL_CLOSED_REAL_INTERVAL`.

- For the second condition, we use the fact that the continuous image of a compact set is bounded, applying `REAL_COMPACT_IMP_BOUNDED` and `REAL_COMPACT_CONTINUOUS_IMAGE`. The interval $[-\pi, \pi]$ is compact (`REAL_COMPACT_INTERVAL`), and the Fejér kernel is continuous on it (`FEJER_KERNEL_CONTINUOUS`).

- Since both conditions are satisfied, the product of the Fejér kernel and $f$ is absolutely integrable on $[-\pi, \pi]$.

### Mathematical insight
This theorem is important in Fourier analysis, particularly in the theory of Fejér summation. The Fejér kernel plays a crucial role in approximating periodic functions by trigonometric polynomials. It has better convergence properties than the Dirichlet kernel.

The result demonstrates that multiplying an absolutely integrable function by the Fejér kernel preserves absolute integrability, which is a key step in proving convergence properties of Fejér means. This is particularly useful because the Fejér kernel possesses several nice properties, including non-negativity and normalization, making it a good averaging operator.

The theorem forms part of the foundation for proving that Fejér means of Fourier series converge uniformly to the original function under certain conditions, which is a central result in harmonic analysis.

### Dependencies
- **Theorems**:
  - `FEJER_KERNEL_CONTINUOUS`: The Fejér kernel is continuous on the interval $[-\pi, \pi]$.
  - `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT` (implicit): Product of an absolutely integrable function and a bounded measurable function is absolutely integrable.
  - `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET` (implicit): A continuous function on a closed set is measurable.
  - `REAL_COMPACT_IMP_BOUNDED` (implicit): A function on a compact set is bounded.
  - `REAL_COMPACT_CONTINUOUS_IMAGE` (implicit): The continuous image of a compact set is compact.
  - `REAL_CLOSED_REAL_INTERVAL` (implicit): Real intervals are closed.
  - `REAL_COMPACT_INTERVAL` (implicit): Real intervals are compact.

- **Definitions**:
  - `fejer_kernel`: Defined as $\text{fejer\_kernel}(n, x) = \begin{cases} 0 & \text{if } n = 0 \\ \frac{1}{n}\sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x) & \text{otherwise} \end{cases}$

### Porting notes
When porting this theorem, note that:
1. The implementation of the Fejér kernel and its properties may differ between systems.
2. The theory of absolute integrability and measurability might be structured differently in other proof assistants.
3. The compactness and boundedness theorems used in the proof are standard mathematical results, but their formulations may vary.

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;
```

### Informal statement
For any function $f$, natural number $n$, real constant $c$, and parameter $t$, if:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is periodic with period $2\pi$ (that is, $f(x + 2\pi) = f(x)$ for all $x$)

Then the following functions are all absolutely integrable on the interval $[-\pi, \pi]$:
1. $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t + x)$
2. $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t - x)$
3. $x \mapsto \text{fejer\_kernel}(n, x) \cdot c$

where $\text{fejer\_kernel}(n, x)$ is defined as $0$ if $n = 0$, and $\frac{1}{n}\sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x)$ otherwise.

### Informal proof
We need to prove that three functions involving the Fejér kernel are absolutely integrable. We'll prove each part separately:

1. For $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t + x)$:
   - We apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL`, which states that if a function is absolutely integrable on $[-\pi, \pi]$, then its product with the Fejér kernel is also absolutely integrable.
   - First, we rewrite the function as $\text{fejer\_kernel}(n, x) \cdot f(x + t)$ by applying commutativity of addition.
   - Next, we use `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` to show that $x \mapsto f(x + t)$ is absolutely integrable on $[-\pi, \pi]$, given that $f$ is absolutely integrable and $2\pi$-periodic.
   - This completes the proof of the first part.

2. For $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t - x)$:
   - We rewrite in terms of absolute integrability.
   - We apply the reflection property of real integrable functions (`REAL_INTEGRABLE_REFLECT`).
   - After simplifying the negations, we rewrite to set up an application of `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`.
   - This establishes that $x \mapsto f(t - x)$ is absolutely integrable, and therefore its product with the Fejér kernel is as well.

3. For $x \mapsto \text{fejer\_kernel}(n, x) \cdot c$:
   - This is a direct application of the theorem `ABSOLUTELY_REAL_INTEGRABLE_CONST`, which states that the product of an absolutely integrable function with a constant is absolutely integrable.

### Mathematical insight
This theorem extends the properties of absolute integrability of functions multiplied by the Fejér kernel to include both translated and reflected versions of a function. The Fejér kernel is a fundamental tool in Fourier analysis, used for smoothing Fourier series. 

The key insight is that the nice properties of the Fejér kernel (continuity and boundedness) allow it to be multiplied by various transformations of an integrable function while preserving absolute integrability. This is especially important for applications in harmonic analysis and the theory of Fourier series, where reflections and translations of functions frequently occur.

The theorem also shows that these properties hold for arbitrary constant functions, which is useful as a base case in many proofs involving convolutions with the Fejér kernel.

### Dependencies
- Theorems:
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Shows that translating a periodic, absolutely integrable function preserves absolute integrability.
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL`: Establishes that multiplying a function by the Fejér kernel preserves absolute integrability.
  - `ABSOLUTELY_REAL_INTEGRABLE_CONST`: Shows that constant functions multiplied by absolutely integrable functions remain absolutely integrable.
  - `REAL_INTEGRABLE_REFLECT`: Used for handling the reflection case.

- Definitions:
  - `fejer_kernel`: Defines the Fejér kernel in terms of the Dirichlet kernel.

### Porting notes
When porting to other proof assistants, pay attention to:
1. The handling of the Fejér kernel and Dirichlet kernel definitions, which may require preliminary work.
2. The approach to absolute integrability, which may differ across systems.
3. The handling of function reflection and translation, which might have different conventions or notation in other systems.

---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;
```

### Informal statement
For all functions $f$, natural numbers $n$, real numbers $d$ and $c$, and real number $t$ (which appears free in the statement):

If:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic, i.e., $f(x + 2\pi) = f(x)$ for all $x$
- $d \leq \pi$

Then all of the following functions are absolutely integrable on the interval $[0, d]$:
1. $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t + x)$
2. $x \mapsto \text{fejer\_kernel}(n, x) \cdot f(t - x)$
3. $x \mapsto \text{fejer\_kernel}(n, x) \cdot c$
4. $x \mapsto \text{fejer\_kernel}(n, x) \cdot (f(t + x) + f(t - x))$
5. $x \mapsto \text{fejer\_kernel}(n, x) \cdot ((f(t + x) + f(t - x)) - c)$

where $\text{fejer\_kernel}(n, x)$ is the Fejér kernel defined as:
$\text{fejer\_kernel}(n, x) = \begin{cases} 
0 & \text{if } n = 0 \\
\frac{1}{n}\sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x) & \text{otherwise}
\end{cases}$

### Informal proof
The proof proceeds as follows:

* First, we apply `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED` to obtain that the first three functions (involving $f(t + x)$, $f(t - x)$, and the constant $c$) are absolutely integrable on $[-\pi, \pi]$.

* Then we prove that these functions are also absolutely integrable on $[0, d]$, which is a subinterval of $[-\pi, \pi]$ (since $d \leq \pi$):
  - We apply `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL` to show that absolute integrability on $[-\pi, \pi]$ implies absolute integrability on $[0, d]$
  - We verify that $[0, d]$ is indeed a subset of $[-\pi, \pi]$ using the fact that $\pi > 0$ and $d \leq \pi$

* For the last two functions (involving the sum $f(t + x) + f(t - x)$ and the difference $(f(t + x) + f(t - x)) - c$), we apply:
  - The distributivity of multiplication: $\text{fejer\_kernel}(n, x) \cdot (f(t + x) + f(t - x)) = \text{fejer\_kernel}(n, x) \cdot f(t + x) + \text{fejer\_kernel}(n, x) \cdot f(t - x)$
  - Similar distributivity for the subtraction term
  - The theorems `ABSOLUTELY_REAL_INTEGRABLE_ADD` and `ABSOLUTELY_REAL_INTEGRABLE_SUB` which state that the sum and difference of absolutely integrable functions are also absolutely integrable

This establishes that all five functions are absolutely integrable on $[0, d]$.

### Mathematical insight
This theorem extends the property of absolute integrability of functions multiplied by the Fejér kernel from the full interval $[-\pi, \pi]$ to a smaller interval $[0, d]$ where $d \leq \pi$. The Fejér kernel appears frequently in Fourier analysis and is particularly important for approximation theory and proving convergence properties of Fourier series.

The theorem specifically addresses the absolute integrability of functions involving both forward and backward shifts ($f(t + x)$ and $f(t - x)$), which is useful when analyzing symmetric properties of Fourier approximations. The inclusion of terms like $f(t + x) + f(t - x)$ is related to studying even components of functions, while the difference term $(f(t + x) + f(t - x)) - c$ allows for analyzing deviations from a constant value.

These properties are crucial for establishing convergence results in Fourier analysis, particularly for proving that Fejér means of Fourier series converge uniformly to the original function under certain conditions.

### Dependencies
- Theorems:
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED`: Establishes absolute integrability on $[-\pi, \pi]$ for the key functions
  - `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`: Allows restricting absolute integrability to subintervals
  - `ABSOLUTELY_REAL_INTEGRABLE_ADD`: Shows that the sum of absolutely integrable functions is absolutely integrable
  - `ABSOLUTELY_REAL_INTEGRABLE_SUB`: Shows that the difference of absolutely integrable functions is absolutely integrable
  - `PI_POS`: States that $\pi > 0$

- Definitions:
  - `fejer_kernel`: Defines the Fejér kernel in terms of Dirichlet kernels

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate definitions for absolute integrability and the Fejér kernel
2. Note that the variable $t$ appears free in the statement (it's not quantified), which might require explicit handling in systems with stricter variable binding
3. The proof relies on simplification tactics that combine distributivity laws with theorems about preservation of absolute integrability - these might need explicit application in systems with less powerful simplification

---

## FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF

### FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF = prove
 (`!f n t.
     f absolutely_real_integrable_on real_interval[--pi,pi] /\
     (!x. f (x + &2 * pi) = f x) /\
     0 < n
     ==> sum(0..n-1) (\r. sum (0..2*r)
                              (\k. fourier_coefficient f k *
                                   trigonometric_set k t)) / &n - l =
         real_integral (real_interval[&0,pi])
                       (\x. fejer_kernel n x *
                            ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ; REAL_FIELD
   `~(n = &0) ==> (x / n - l = y <=> x - n * l = n * y)`] THEN
  MP_TAC(ISPECL [`l:real`; `0`; `n - 1`] SUM_CONST_NUMSEG) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div; SUM_RMUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               FINITE_NUMSEG; REAL_LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_LE_REFL;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[fejer_kernel; LE_1] THEN MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) ==> s * f = n * s / n * f`) THEN
  ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ]);;
```

### Informal statement
Let $f$ be a function that is absolutely integrable on the interval $[-\pi, \pi]$ and $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$). Let $n > 0$ be a natural number, $t$ be a real number, and $l$ be a constant. Then:

$$\frac{1}{n} \sum_{r=0}^{n-1} \sum_{k=0}^{2r} \hat{f}(k) \cdot \varphi_k(t) - l = \frac{1}{\pi} \int_0^{\pi} F_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

where:
- $\hat{f}(k)$ is the Fourier coefficient of $f$ for index $k$
- $\varphi_k(t)$ is the $k$-th trigonometric basis function evaluated at $t$
- $F_n(x)$ is the Fejér kernel of order $n$ evaluated at $x$

### Informal proof
We need to prove a relationship between the average of partial Fourier sums and an integral involving the Fejér kernel. 

First, we apply algebraic manipulation to simplify the goal. Since $n > 0$, the equation 
$$\frac{1}{n} \sum_{r=0}^{n-1} \sum_{k=0}^{2r} \hat{f}(k) \cdot \varphi_k(t) - l = \frac{1}{\pi} \int_0^{\pi} F_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

is equivalent to:
$$\sum_{r=0}^{n-1} \sum_{k=0}^{2r} \hat{f}(k) \cdot \varphi_k(t) - n \cdot l = n \cdot \frac{1}{\pi} \int_0^{\pi} F_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

We observe that $\sum_{r=0}^{n-1} l = n \cdot l$ for the constant $l$. This allows us to distribute the subtraction:

$$\sum_{r=0}^{n-1} \left(\sum_{k=0}^{2r} \hat{f}(k) \cdot \varphi_k(t) - l\right)$$

For each term in this sum, we apply the theorem `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`, which states:

$$\sum_{k=0}^{2r} \hat{f}(k) \cdot \varphi_k(t) - l = \frac{1}{\pi} \int_0^{\pi} D_r(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

where $D_r(x)$ is the Dirichlet kernel of order $r$.

After replacing each term, we get:

$$\sum_{r=0}^{n-1} \frac{1}{\pi} \int_0^{\pi} D_r(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

By linearity of integration, we can move the summation inside the integral:

$$\frac{1}{\pi} \int_0^{\pi} \left(\sum_{r=0}^{n-1} D_r(x)\right) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

We note that by definition of the Fejér kernel: $F_n(x) = \frac{1}{n} \sum_{r=0}^{n-1} D_r(x)$ for $n > 0$, so:

$$\sum_{r=0}^{n-1} D_r(x) = n \cdot F_n(x)$$

Substituting this into our integral:

$$\frac{1}{\pi} \int_0^{\pi} n \cdot F_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx = n \cdot \frac{1}{\pi} \int_0^{\pi} F_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

Which matches the right-hand side of our goal, completing the proof.

### Mathematical insight
This theorem establishes a connection between averaging partial Fourier sums and an integral representation using the Fejér kernel. It's an important result in Fourier analysis related to the convergence of Fourier series. 

The Fejér kernel $F_n$ serves as a smoothing kernel and produces better convergence properties than the Dirichlet kernel. The theorem essentially shows that the average of the first $n$ partial Fourier sums minus some constant $l$ can be represented as an integral involving the Fejér kernel.

This result is part of the theory underlying Fejér's theorem, which states that for any continuous periodic function, the arithmetic means of the partial sums of its Fourier series converge uniformly to the function. The integral representation using the Fejér kernel provides a way to analyze this convergence process.

### Dependencies
- `trigonometric_set`: Defines the trigonometric basis functions
- `fourier_coefficient`: Defines the Fourier coefficients as orthonormal coefficients
- `fejer_kernel`: Defines the Fejér kernel in terms of Dirichlet kernels
- `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`: Provides a similar relation for the Dirichlet kernel
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART`: Ensures integrability of Dirichlet kernel products
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART`: Ensures integrability of Fejér kernel products

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate definitions of Fourier coefficients, trigonometric basis functions, and Fejér kernels.
2. The proof relies on algebraic manipulations and properties of integrals, which should translate well to other proof assistants.
3. You may need to reformulate the theorem slightly if the target system uses different conventions for Fourier series or handles periodic functions differently.
4. Be aware that HOL Light's handling of real integrals might differ from other systems, so the integration theory parts may need adaptation.

---

## FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum(0..n-1) (\r. sum (0..2*r)
                                        (\k. fourier_coefficient f k *
                                             trigonometric_set k t)) / &n)
               ---> l) sequentially <=>
             ((\n. real_integral (real_interval[&0,pi])
                                 (\x. fejer_kernel n x *
                                      ((f(t + x) + f(t - x)) - &2 * l)))
              ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REALLIM_NULL_RMUL_EQ PI_NZ)] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF; LE_1] THEN
  ASM_SIMP_TAC[PI_POS; REAL_LT_IMP_NZ; REAL_DIV_RMUL; REAL_SUB_REFL]);;
```

### Informal statement
For any function $f$ and real values $t$ and $l$, if:
- $f$ is absolutely integrable on the interval $[-\pi, \pi]$
- $f$ is $2\pi$-periodic (i.e., $\forall x. f(x + 2\pi) = f(x)$)

Then the following statements are equivalent:
1. The sequence $\left(\frac{1}{n} \sum_{r=0}^{n-1} \sum_{k=0}^{2r} c_k f \cdot \phi_k(t)\right)$ converges to $l$ as $n \to \infty$
2. The sequence $\left(\int_{0}^{\pi} K_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx\right)$ converges to $0$ as $n \to \infty$

where:
- $c_k f$ denotes the $k^{th}$ Fourier coefficient of $f$
- $\phi_k(t)$ is the $k^{th}$ trigonometric basis function at point $t$
- $K_n(x)$ is the Fejér kernel of order $n$

### Informal proof
The proof connects the Fejér means of the Fourier series with an integral form using the Fejér kernel. The structure follows:

- First, apply the theorem `FOURIER_SUM_LIMIT_PAIR` to transform the first limit condition to use a different summation structure, establishing that the limit of partial sums up to $2n$ terms is equivalent to the limit of partial sums up to $n$ terms.

- Convert the second limit condition to the form of a "limit equals zero" statement by applying `REALLIM_NULL`.

- Multiply both sides by $\pi$ (which is non-zero) to simplify the equivalence using `REALLIM_NULL_RMUL_EQ`.

- Apply the transformational equivalence for limits using `REALLIM_TRANSFORM_EQ` and `REALLIM_EVENTUALLY`.

- The key step uses `FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF` which establishes the connection between the sum of Fourier coefficients and the integral with Fejér kernel:
  $$\frac{\sum_{r=0}^{n-1} \sum_{k=0}^{2r} c_k f \cdot \phi_k(t)}{n} - l = \frac{1}{\pi}\int_{0}^{\pi} K_n(x) \cdot ((f(t+x) + f(t-x)) - 2l) \, dx$$

- After simplification using basic properties of real numbers and the positivity of $\pi$, the equivalence is established.

### Mathematical insight
This theorem provides a fundamental connection between two ways of viewing Fourier series convergence:
1. The convergence of Cesàro means (Fejér sums) of the Fourier series
2. The convergence of an integral form using the Fejér kernel

This connection is crucial for proving Fejér's theorem, which states that the arithmetic means of partial sums of the Fourier series of a continuous periodic function converge uniformly to the function. The result provides a way to analyze the convergence behavior of Fourier series through the lens of integral transforms.

The theorem essentially reformulates the question of whether the Fejér means converge to $l$ into a question about whether a specific integral approaches zero. This is significant because the Fejér kernel has better convergence properties than the Dirichlet kernel, making it a valuable tool for analyzing Fourier series.

### Dependencies
- **Theorems:**
  - `FOURIER_SUM_LIMIT_PAIR`: Relates different ways of summing Fourier coefficients
  - `FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF`: Connects sum of Fourier coefficients with Fejér kernel integral
  - `REALLIM_NULL`: Reformulates a limit to a statement about approaching zero
  - `REALLIM_NULL_RMUL_EQ`: Property of limits with multiplication
  - `REALLIM_TRANSFORM_EQ`: Theorem for transforming equivalent limits
  - `REALLIM_EVENTUALLY`: Theorem about eventual behavior of sequences
  - `PI_NZ`: The constant $\pi$ is non-zero
  - `PI_POS`: The constant $\pi$ is positive
  - `REAL_LT_IMP_NZ`: Real number inequality implies non-zero
  - `REAL_DIV_RMUL`: Property of division of real numbers
  - `REAL_SUB_REFL`: Self-subtraction equals zero

- **Definitions:**
  - `fourier_coefficient`: Defines Fourier coefficients via orthonormal basis
  - `fejer_kernel`: Defines the Fejér kernel in terms of the Dirichlet kernel
  - `trigonometric_set`: Defines the trigonometric basis functions

### Porting notes
When implementing this theorem in other systems:
1. Ensure that the definitions of Fourier coefficients, trigonometric basis functions, and Fejér kernel are consistent with HOL Light's implementation.
2. Pay attention to the handling of limits and sequences, as different systems may have different conventions for representing convergence.
3. The proof relies heavily on properties of real integrals and limits, so make sure these foundations are in place.
4. The periodicity condition on the function is crucial and should be explicitly preserved in the statement.

---

## HAS_REAL_INTEGRAL_FEJER_KERNEL

### Name of formal statement
HAS_REAL_INTEGRAL_FEJER_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_FEJER_KERNEL = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi = sum(0..n-1) (\r. pi) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]]);;
```

### Informal statement
For all natural numbers $n$, the Fejér kernel of order $n$ has a real integral over the interval $[-\pi, \pi]$ equal to $\pi$ if $n \neq 0$, and equal to $0$ if $n = 0$.

Formally, for all $n \in \mathbb{N}$:
$$\int_{-\pi}^{\pi} \text{fejer\_kernel}(n, x) \, dx = \begin{cases} 0 & \text{if } n = 0 \\ \pi & \text{if } n \neq 0 \end{cases}$$

where the Fejér kernel is defined as:
$$\text{fejer\_kernel}(n, x) = \begin{cases} 0 & \text{if } n = 0 \\ \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x) & \text{if } n \neq 0 \end{cases}$$

### Informal proof
We prove this theorem by examining the two cases separately:

* When $n = 0$:
  - By definition, $\text{fejer\_kernel}(0, x) = 0$.
  - The integral of the zero function is zero.

* When $n \neq 0$:
  - We first observe that $\pi = \frac{\sum_{r=0}^{n-1} \pi}{n}$ for $n \neq 0$. This is true because $\sum_{r=0}^{n-1} \pi = n\pi$.
  
  - Next, we express the Fejér kernel using its definition:
    $$\text{fejer\_kernel}(n, x) = \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x)$$
  
  - To compute the integral, we use linearity properties:
    $$\int_{-\pi}^{\pi} \text{fejer\_kernel}(n, x) \, dx = \int_{-\pi}^{\pi} \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x) \, dx$$
    $$= \frac{1}{n} \int_{-\pi}^{\pi} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r, x) \, dx$$
    $$= \frac{1}{n} \sum_{r=0}^{n-1} \int_{-\pi}^{\pi} \text{dirichlet\_kernel}(r, x) \, dx$$
  
  - Using the fact that for each $r$, $\int_{-\pi}^{\pi} \text{dirichlet\_kernel}(r, x) \, dx = \pi$ (by the theorem `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`), we have:
    $$\frac{1}{n} \sum_{r=0}^{n-1} \int_{-\pi}^{\pi} \text{dirichlet\_kernel}(r, x) \, dx = \frac{1}{n} \sum_{r=0}^{n-1} \pi = \frac{n\pi}{n} = \pi$$

Therefore, the integral of the Fejér kernel over $[-\pi, \pi]$ is $0$ when $n = 0$ and $\pi$ when $n \neq 0$.

### Mathematical insight
The Fejér kernel is a fundamental concept in Fourier analysis, particularly in the study of convergence of Fourier series. It is defined as the arithmetic mean of the first $n$ Dirichlet kernels. 

The Fejér kernel has several important properties:
1. It is non-negative everywhere (unlike the Dirichlet kernel)
2. Its integral over $[-\pi, \pi]$ is $\pi$ (when $n \neq 0$)
3. It forms an approximate identity as $n$ approaches infinity

These properties make the Fejér kernel particularly useful in proving Fejér's theorem, which states that the arithmetic means of the partial sums of a Fourier series converge uniformly to the original function under certain conditions. This is a more robust convergence result than can be obtained with the Dirichlet kernel alone.

This theorem specifically establishes the normalization property of the Fejér kernel, showing that its integral over the fundamental period is $\pi$ (or 0 when $n=0$), which is essential for its application in Fourier analysis.

### Dependencies
#### Theorems
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`: The Dirichlet kernel of order n has a real integral equal to π over the interval [-π, π].
- `HAS_REAL_INTEGRAL_0`: The zero function has a real integral equal to 0.
- `HAS_REAL_INTEGRAL_SUM`: Linearity of integration with respect to summation.
- `HAS_REAL_INTEGRAL_RMUL`: Linearity of integration with respect to scalar multiplication.

#### Definitions
- `fejer_kernel`: Definition of the Fejér kernel as either 0 (when n=0) or the average of Dirichlet kernels (when n≠0).

### Porting notes
When porting this theorem to other systems:
- Ensure that the Dirichlet kernel and its integration property are already defined.
- The proof relies heavily on linearity properties of integration which should be available in most systems.
- Be careful with the case distinction for n=0, as some systems might handle empty sums differently.
- In systems with strong automation for integrals, some of the steps might be automated, especially the calculation of trivial integrals.

---

## HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF

### Name of formal statement
HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi / &2 = sum(0..n-1) (\r. pi / &2) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF]]);;
```

### Informal statement
For all natural numbers $n$, the Fejér kernel $\text{fejer\_kernel}(n)$ has real integral equal to $\begin{cases} 0 & \text{if } n = 0 \\ \frac{\pi}{2} & \text{if } n > 0 \end{cases}$ over the interval $[0, \pi]$.

### Informal proof
We prove this by case analysis on whether $n = 0$:

1. First, we use the ETA expansion to handle the function application and rewrite using the definition of the Fejér kernel.

2. **Case $n = 0$**: When $n = 0$, the Fejér kernel is defined as the constant function 0, which has an integral of 0 over any interval.

3. **Case $n > 0$**: For $n > 0$, we need to show that the integral of the Fejér kernel equals $\frac{\pi}{2}$.

   * We first rewrite $\frac{\pi}{2}$ as $\frac{\sum_{r=0}^{n-1} \frac{\pi}{2}}{n} = \frac{\pi}{2} \cdot \frac{n}{n} = \frac{\pi}{2}$
   
   * By definition, $\text{fejer\_kernel}(n)(x) = \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r)(x)$

   * We apply the theorem about the integral of a scaled function (`HAS_REAL_INTEGRAL_RMUL`) to handle the division by $n$

   * Then we use the theorem about the integral of a sum (`HAS_REAL_INTEGRAL_SUM`) to distribute the integral

   * Finally, we apply the known result that for all $r$, $\int_{0}^{\pi} \text{dirichlet\_kernel}(r)(x) \, dx = \frac{\pi}{2}$ (`HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`)

### Mathematical insight
The Fejér kernel is a key concept in Fourier analysis, commonly used for approximation of periodic functions. This theorem establishes that the integral of the Fejér kernel over the half-period $[0,\pi]$ is $\frac{\pi}{2}$ for $n > 0$, which matches the integral of the Dirichlet kernel used in its definition. This result is important for applications in harmonic analysis and the theory of Fourier series.

The case $n = 0$ is treated separately because the Fejér kernel is defined to be identically zero in this case, which is a conventional choice to maintain certain properties of the kernel family.

### Dependencies
#### Theorems
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`: The Dirichlet kernel has real integral equal to $\frac{\pi}{2}$ over the interval $[0, \pi]$
- `HAS_REAL_INTEGRAL_0`: A constant zero function has a zero integral
- `HAS_REAL_INTEGRAL_RMUL`: Rule for the integral of a scaled function
- `HAS_REAL_INTEGRAL_SUM`: Rule for the integral of a sum of functions

#### Definitions
- `fejer_kernel`: The Fejér kernel defined as $\text{fejer\_kernel}(n)(x) = \begin{cases} 0 & \text{if } n = 0 \\ \frac{1}{n} \sum_{r=0}^{n-1} \text{dirichlet\_kernel}(r)(x) & \text{if } n > 0 \end{cases}$

### Porting notes
When porting this theorem, ensure that the definition of the Fejér kernel follows the same convention for $n = 0$ as in HOL Light. Different proof assistants might handle division by zero differently, so special care should be taken for the case analysis. The proof relies on linearity of integration, which should be available in any standard mathematical library.

---

## FEJER_KERNEL_POS_LE

### Name of formal statement
FEJER_KERNEL_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL_POS_LE = prove
 (`!n x. &0 <= fejer_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FEJER_KERNEL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV]) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```

### Informal statement
For all natural numbers $n$ and real numbers $x$, the Fejér kernel is non-negative:
$$\forall n, x. 0 \leq \text{fejer\_kernel}(n, x)$$

### Informal proof
We prove that the Fejér kernel is always non-negative by using its explicit formula from the `FEJER_KERNEL` theorem, which states:

$$\text{fejer\_kernel}(n, x) = 
\begin{cases} 
0 & \text{if } n = 0 \\
\frac{n}{2} & \text{if } n \neq 0 \text{ and } x = 0 \\
\frac{\sin^2\left(\frac{n}{2} \cdot x\right)}{2n \sin^2\left(\frac{x}{2}\right)} & \text{if } n \neq 0 \text{ and } x \neq 0 
\end{cases}$$

The proof proceeds by case analysis:

- For the case $n = 0$: We have $\text{fejer\_kernel}(n, x) = 0$, which satisfies $0 \leq \text{fejer\_kernel}(n, x)$.
  
- For the case $n \neq 0$ and $x = 0$: We have $\text{fejer\_kernel}(n, x) = \frac{n}{2}$. Since $n > 0$, we have $\frac{n}{2} > 0$, so $0 \leq \text{fejer\_kernel}(n, x)$.
  
- For the case $n \neq 0$ and $x \neq 0$: We need to show that $\frac{\sin^2\left(\frac{n}{2} \cdot x\right)}{2n \sin^2\left(\frac{x}{2}\right)} \geq 0$.
  
  This follows because:
  - $\sin^2(\frac{n}{2} \cdot x) \geq 0$ (square of any real number is non-negative)
  - $n > 0$ (from our case assumption)
  - $\sin^2(\frac{x}{2}) \geq 0$ (square of any real number is non-negative)
  - The product $2n \sin^2(\frac{x}{2})$ is non-negative
  - Therefore, the quotient of non-negative numbers is non-negative when the denominator is positive

In all cases, we have $0 \leq \text{fejer\_kernel}(n, x)$.

### Mathematical insight
The Fejér kernel is a fundamental object in Fourier analysis, particularly for studying the convergence of Fourier series. It is formed by taking the arithmetic mean of the first $n$ Dirichlet kernels.

The non-negativity of the Fejér kernel is a crucial property that distinguishes it from the Dirichlet kernel, which can take negative values. This non-negativity is what makes the Fejér kernel particularly useful in proving convergence results for Fourier series, as it leads to better approximation properties.

The Fejér kernel, unlike the Dirichlet kernel, provides a smoother approximation, and this theorem establishes that the kernel produces positive averages. This non-negativity property of the Fejér kernel is essential for the Fejér summation method, which is used to show that the Fourier series of a continuous periodic function converges uniformly to the function.

### Dependencies
- Theorems:
  - `FEJER_KERNEL`: Provides the explicit formula for the Fejér kernel

- Definitions:
  - `fejer_kernel`: Defines the Fejér kernel as the average of the first n Dirichlet kernels

### Porting notes
When implementing this theorem in other proof assistants, ensure that:
- The definition of the Fejér kernel is properly established
- The case analysis in the proof is handled correctly
- The non-negativity of squares and products/quotients of non-negative numbers is available

The proof is straightforward and should translate well to other systems, as it relies on basic properties of real numbers and case analysis.

---

## FOURIER_FEJER_CESARO_SUMMABLE

### FOURIER_FEJER_CESARO_SUMMABLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FOURIER_FEJER_CESARO_SUMMABLE = prove
 (`!f x l r.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        (f ---> l) (atreal x within {x' | x' <= x}) /\
        (f ---> r) (atreal x within {x' | x' >= x})
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> (l + r) / &2)
            sequentially`,
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `l:real`; `r:real`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - (l + r)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_ARITH
     `(f' + f) - (l + l'):real = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f ---> l) (atreal t within {x' | x' <= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `(f ---> r) (atreal t within {x' | x' >= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < pi /\
        (!x. &0 < x /\ x <= k ==> abs(h x) < e / &2 / pi)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(h ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
    REWRITE_TAC[REALLIM_WITHINREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; PI_POS; IN_ELIM_THM; REAL_SUB_RZERO;
                 LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN EXISTS_TAC `min k pi / &2` THEN
    REPEAT(CONJ_TAC THENL
     [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. real_integral (real_interval[k,pi])
                        (\x. fejer_kernel n x * h x))
     ---> &0) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC
     `\n. real_integral (real_interval[k,pi])
                        (\x. abs(h x) / (&2 * sin(x / &2) pow 2)) / &n` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N]] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FEJER_KERNEL; LE_1] THEN
    SUBGOAL_THEN
     `(\x. h x / (&2 * sin(x / &2) pow 2))
      absolutely_real_integrable_on real_interval[k,pi]`
    MP_TAC THENL
     [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
      REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS;
        MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[REAL_COMPACT_INTERVAL];
        EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
        REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
           [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
            REWRITE_TAC[real_sub; absolutely_real_integrable_on] THEN
            ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
            REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
            REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
            ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]] THEN
      (REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
       STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
         REAL_DIFFERENTIABLE_TAC;
         REWRITE_TAC[REAL_RING `&2 * x pow 2 = &0 <=> x = &0`] THEN
         MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
         ASM_REAL_ARITH_TAC]);
      DISCH_THEN(fun th -> ASSUME_TAC th THEN
        MP_TAC(MATCH_MP ABSOLUTELY_REAL_INTEGRABLE_ABS th)) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_POW] THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN DISCH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [real_div] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM REAL_INV_MUL; REAL_ABS_MUL] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> x <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 <= x ==> abs x <= y`) THEN
      REWRITE_TAC[GSYM real_div; REAL_LE_INV_EQ] THEN
      SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_MUL_AC];
      DISCH_TAC] THEN
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x.  abs(h x) / (&2 * sin(x / &2) pow 2) * inv(&n)` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\x. sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2) * h(x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `s * t * n * i * h:real = n * s * h * (t * i)`] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `MAX 1 N` THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= x <=> a <= x /\ b <= x`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x. fejer_kernel n x * h x`; `&0`; `pi`; `k:real`]
        REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= e / &2 ==> x + y = z ==> abs y < e / &2 ==> abs z < e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,k])
                            (\x. fejer_kernel n x * e / &2 / pi)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `real_integral (real_interval [&0,k]) (\x. fejer_kernel n x * h x) =
      real_integral (real_interval [&0,k])
                    (\x. fejer_kernel n x * (if x = &0 then &0 else h x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN SIMP_TAC[IN_DIFF; IN_SING] THEN
      REWRITE_TAC[REAL_NEGLIGIBLE_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      MAP_EVERY EXISTS_TAC [`\x. fejer_kernel n x * h x`; `{&0}`] THEN
      SIMP_TAC[IN_DIFF; IN_SING; REAL_NEGLIGIBLE_SING] THEN
      EXPAND_TAC "h" THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_LT_IMP_LE];
      MP_TAC(ISPECL
       [`\x:real. e / &2 / pi`; `n:num`; `k:real`; `&0`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART) THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST; REAL_LT_IMP_LE;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_NUM; REAL_POS;
                   PI_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF) THEN
    ASM_SIMP_TAC[LE_1] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `real_integral (real_interval[&0,pi])
                    (\x. fejer_kernel n x * e / &2 / pi)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[&0,pi]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[real_integrable_on];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[real_integrable_on];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
        MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
      SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      REPEAT STRIP_TAC THEN SIMP_TAC[PI_POS; REAL_FIELD
       `&0 < pi ==> pi / &2 * e / &2 / pi = e / &4`] THEN
      ASM_REAL_ARITH_TAC]]);;
```

### Informal statement
For a function $f$ that is absolutely integrable on the interval $[-\pi, \pi]$ and has period $2\pi$ (i.e., $f(x + 2\pi) = f(x)$ for all $x$), if $f$ has left and right limits at a point $x$:
- $f(t) \to l$ as $t \to x$ with $t \leq x$ (left limit)
- $f(t) \to r$ as $t \to x$ with $t \geq x$ (right limit)

Then the Cesàro means of the partial sums of the Fourier series of $f$ at $x$ converge to the average of the left and right limits:

$$\lim_{n\to\infty} \frac{1}{n}\sum_{m=0}^{n-1} \sum_{k=0}^{2m} \left(\text{fourier\_coefficient}(f,k) \cdot \text{trigonometric\_set}(k,x)\right) = \frac{l+r}{2}$$

### Informal proof
We will prove this theorem by relating the Cesàro means of the Fourier series to the Fejér kernel integral.

1. First, apply `FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF` to transform the problem:
   - The limit of the Cesàro means equals $\frac{l+r}{2}$ if and only if the sequence of integrals 
     $$\int_0^{\pi} \text{fejer\_kernel}(n,x) \cdot ((f(t+x) + f(t-x)) - 2\cdot\frac{l+r}{2}) dx$$ 
     converges to 0.

2. Let $h(u) = f(t+u) + f(t-u) - (l+r)$. Note that $h(0) = 0$.

3. Show that $h(u) \to 0$ as $u \to 0^+$:
   - Using the assumption that $f(t) \to l$ as $t \to x$ with $t \leq x$, we get $f(t-u) \to l$ as $u \to 0^+$
   - Similarly, using $f(t) \to r$ as $t \to x$ with $t \geq x$, we get $f(t+u) \to r$ as $u \to 0^+$
   - Therefore $h(u) \to 0$ as $u \to 0^+$

4. For any $\epsilon > 0$, there exists $k$ such that $0 < k < \pi$ and $|h(x)| < \frac{\epsilon}{2\pi}$ for all $x$ with $0 < x \leq k$.

5. Split the integral into two parts: $[0,k]$ and $[k,\pi]$.
   
6. For the integral over $[k,\pi]$, show that:
   $$\lim_{n\to\infty} \int_k^{\pi} \text{fejer\_kernel}(n,x) \cdot h(x) dx = 0$$
   - This is done by comparing with the integral of $\frac{|h(x)|}{2\sin^2(x/2)} \cdot \frac{1}{n}$
   - Using properties of the Fejér kernel, we can show that the limit is 0

7. For the integral over $[0,k]$, bound it by:
   $$\left|\int_0^k \text{fejer\_kernel}(n,x) \cdot h(x) dx\right| \leq \int_0^k \text{fejer\_kernel}(n,x) \cdot \frac{\epsilon}{2\pi} dx$$

8. Using the fact that $\int_0^{\pi} \text{fejer\_kernel}(n,x) dx = \frac{\pi}{2}$ (for $n > 0$), we can show the bound is at most $\frac{\epsilon}{4}$

9. Combining these results, for sufficiently large $n$, the original integral is less than $\epsilon$.

Therefore, the Cesàro means of the Fourier series converge to $\frac{l+r}{2}$.

### Mathematical insight
This theorem is a version of Fejér's theorem that establishes the convergence of Cesàro means (also called Fejér sums) of Fourier series at points of discontinuity. The key insight is that even though the Fourier series might not converge at points of discontinuity, the Cesàro means of the partial sums will still converge to the average of the left and right limits.

The proof uses the Fejér kernel, which is a positive kernel that approximates a delta function as n approaches infinity. This positivity is crucial as it allows us to apply certain integral inequalities and convergence properties that wouldn't be possible with the Dirichlet kernel (associated with partial sums of Fourier series).

This result is significant because:
1. It guarantees convergence at all points, including discontinuities
2. It provides a constructive way to recover a function from its Fourier coefficients
3. It demonstrates that Cesàro summation is a powerful regularization method for Fourier series

### Dependencies
- **Theorems**:
  - `trigonometric_set`: Definition of the trigonometric basis functions
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`: Preserves absolute integrability under periodic shifts
  - `FEJER_KERNEL`: Explicit formula for the Fejér kernel
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART`: Integrability properties of products with Fejér kernel
  - `FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF`: Relates Fourier series convergence to Fejér kernel integrals
  - `HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF`: Integral of the Fejér kernel on [0,π]
  - `FEJER_KERNEL_POS_LE`: Non-negativity of the Fejér kernel

- **Definitions**:
  - `fourier_coefficient`: Coefficients of function expansions in the trigonometric basis
  - `fejer_kernel`: Definition of the Fejér kernel in terms of Dirichlet kernels

### Porting notes
When porting this theorem:

1. The Fejér kernel may be defined differently in other systems - ensure consistency with the definition used here.

2. Pay attention to the normalization of the trigonometric basis functions, which affects the scaling of Fourier coefficients.

3. The proof relies heavily on integral properties and convergence arguments that might require different approaches in other systems.

4. Some systems might have built-in libraries for Fourier analysis which could simplify the port, but verify the definitions match.

---

## FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE

### Name of formal statement
FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE = prove
 (`!f x l r.
        f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> f(x))
            sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = (x + x) / &2`] THEN
  MATCH_MP_TAC FOURIER_FEJER_CESARO_SUMMABLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    CONJ_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                  IN_UNIV]]);;
```

### Informal statement
For any real-valued function $f$ on $\mathbb{R}$, if:
- $f$ is continuous on all of $\mathbb{R}$
- $f$ is $2\pi$-periodic (i.e., $f(x + 2\pi) = f(x)$ for all $x$)

Then the Cesàro means of the partial sums of the Fourier series of $f$ converge to $f(x)$. That is:

$$\lim_{n\to\infty} \frac{1}{n}\sum_{m=0}^{n-1}\sum_{k=0}^{2m} c_k \cdot e_k(x) = f(x)$$

where:
- $c_k = \text{fourier\_coefficient}(f, k)$ are the Fourier coefficients of $f$
- $e_k(x) = \text{trigonometric\_set}(k, x)$ are the trigonometric basis functions

### Informal proof
The proof involves rewriting the statement using a more general theorem. The steps are:

1. First, we rewrite $f(x)$ as $\frac{f(x) + f(x)}{2}$ using algebraic manipulation.

2. We then apply the more general theorem `FOURIER_FEJER_CESARO_SUMMABLE`, which states that for any $2\pi$-periodic function that is absolutely integrable on $[-\pi, \pi]$ and has left and right limits at every point, the Cesàro means of the Fourier series converge to the average of these limits.

3. To use this theorem, we verify its preconditions:
   - The function $f$ is absolutely integrable on $[-\pi, \pi]$ because it's continuous on all of $\mathbb{R}$
   - $f$ is $2\pi$-periodic by assumption
   - Since $f$ is continuous on $\mathbb{R}$, the left limit and right limit at any point $x$ both equal $f(x)$, so $\frac{l+r}{2} = \frac{f(x)+f(x)}{2} = f(x)$

4. Therefore, the sequence converges to $f(x)$ as required.

### Mathematical insight
This theorem is a simplification of the more general Fejér-Cesàro summability result. While the general theorem applies to functions with potential discontinuities (where the Fourier series converges to the average of left and right limits), this simplified version applies to continuous functions where the Fourier series converges exactly to the function value.

The result is significant because it shows that while the partial sums of a Fourier series might not converge for all continuous functions, their Cesàro means always converge to the original function. This is a fundamental result in Fourier analysis that ensures that continuous periodic functions can be effectively represented by their Fourier series.

### Dependencies
- `FOURIER_FEJER_CESARO_SUMMABLE`: The more general theorem about convergence of Cesàro means to the average of left and right limits
- `fourier_coefficient`: Definition of Fourier coefficients as orthonormal coefficients on $[-\pi, \pi]$
- `trigonometric_set`: Definition of the trigonometric basis functions

### Porting notes
When implementing this in other systems:
1. Ensure the trigonometric basis functions are properly normalized according to the same conventions
2. The treatment of Fourier coefficients may differ between systems - check normalization constants
3. The Cesàro means (arithmetic means of partial sums) must be carefully implemented
4. The definition of convergence "sequentially" should be translated to the target system's notion of sequence convergence

---

