# cayley_hamilton.ml

## Overview

Number of statements: 14

This file formalizes the Cayley-Hamilton theorem for real matrices, which states that a square matrix satisfies its own characteristic polynomial. It develops the necessary infrastructure for polynomials of matrices, including definitions for the characteristic polynomial and adjugate matrix. The implementation builds on complex analysis and summation operations from the multivariate analysis library. The file culminates in a formal proof of the theorem, establishing one of the fundamental results in linear algebra.

## MATRIC_POLYFUN_EQ_0

### Name of formal statement
MATRIC_POLYFUN_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_POLYFUN_EQ_0 = prove
 (`!n A:num->real^N^M.
        (!x. msum(0..n) (\i. x pow i %% A i) = mat 0) <=>
        (!i. i IN 0..n ==> A i = mat 0)`,
  SIMP_TAC[CART_EQ; MSUM_COMPONENT; MAT_COMPONENT; LAMBDA_BETA;
           FINITE_NUMSEG; COND_ID;
           ONCE_REWRITE_RULE[REAL_MUL_SYM] MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[MESON[]
   `(!x i. P i ==> !j. Q j ==> R x i j) <=>
    (!i. P i ==> !j. Q j ==> !x. R x i j)`] THEN
  REWRITE_TAC[REAL_POLYFUN_EQ_0] THEN MESON_TAC[]);;
```

### Informal statement
For any natural number $n$ and a family of matrices $A: \mathbb{N} \to \mathbb{R}^{N \times M}$, the matrix polynomial $\sum_{i=0}^{n} x^i A_i$ equals the zero matrix for all $x$ if and only if each coefficient matrix $A_i$ is the zero matrix for all $i \in \{0,1,\ldots,n\}$.

Formally:
$$\forall n, A: \mathbb{N} \to \mathbb{R}^{N \times M}. \left(\forall x. \sum_{i=0}^{n} x^i A_i = 0 \right) \iff \left(\forall i \in \{0,1,\ldots,n\}. A_i = 0\right)$$

where:
- $\sum$ is the matrix summation operation (`msum`)
- $x^i$ is scalar power
- $\%\%$ represents scalar-matrix multiplication
- `mat 0` is the zero matrix

### Informal proof
The proof proceeds by showing that the matrix polynomial equals zero if and only if each component of each coefficient matrix equals zero:

1. First, we use `CART_EQ` to reduce the matrix equality to component-wise equality.

2. We apply `MSUM_COMPONENT` to break down the matrix summation into component-wise sums:
   $$\sum_{i=0}^{n} x^i A_i[j,k] = \sum_{i=0}^{n} (x^i (A_i[j,k]))$$
   
3. We use `MAT_COMPONENT` and `LAMBDA_BETA` to extract the components of the zero matrix.

4. We apply `MATRIX_CMUL_COMPONENT` (after rewriting to switch the order of multiplication) to simplify the scalar-matrix multiplication components.

5. We reorder the quantifiers to separate variables appropriately.

6. Finally, we use `REAL_POLYFUN_EQ_0` (the scalar version of this theorem) to conclude that a real polynomial equals zero if and only if all its coefficients are zero.

7. The result follows directly by `MESON_TAC`, connecting the matrix result to the scalar result.

### Mathematical insight
This theorem establishes the fundamental property that a matrix polynomial is the zero polynomial if and only if all its coefficient matrices are zero. This is a matrix extension of the familiar result for scalar polynomials, which states that a polynomial is identically zero if and only if all its coefficients are zero.

This result is essential for the Cayley-Hamilton theorem mentioned in the comments. The Cayley-Hamilton theorem states that every square matrix satisfies its own characteristic polynomial, which is a key result in linear algebra with applications in differential equations, control theory, and other areas of mathematics.

### Dependencies
- **Theorems**:
  - `MSUM_COMPONENT`: Relates the components of a matrix sum to sums of components
  - `REAL_POLYFUN_EQ_0`: The scalar version of this theorem for real polynomials
  - Various basic matrix and component manipulation theorems: `CART_EQ`, `MAT_COMPONENT`, `LAMBDA_BETA`, `MATRIX_CMUL_COMPONENT`
  
- **Definitions**:
  - `msum`: Matrix summation operation
  - `real`: Definition of real numbers in the complex number setting

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate matrix component access operations.
2. The theorem relies on the scalar version `REAL_POLYFUN_EQ_0`, which should be ported first.
3. The proof strategy uses MESON for automated reasoning at the end - in other proof assistants, more explicit reasoning might be needed to connect the matrix result to the scalar result.
4. Ensure that matrix indexing conventions are consistent with the target system, as the proof makes heavy use of component-wise reasoning.

---

## MATRIC_POLY_LEMMA

### Name of formal statement
MATRIC_POLY_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_POLY_LEMMA = prove
 (`!(A:real^N^N) B (C:real^N^N) n.
        (!x. msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C)
        ==> C = mat 0`,
  SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG; MATRIX_SUB_LDISTRIB] THEN
  REWRITE_TAC[MATRIX_MUL_RMUL] THEN ONCE_REWRITE_TAC[MATRIX_MUL_LMUL] THEN
  ONCE_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  SIMP_TAC[MSUM_SUB; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. msum(0..SUC n)
         (\i. x pow i %% (((if i = 0 then (--C:real^N^N) else mat 0) +
                           (if i <= n then B i ** (A:real^N^N) else mat 0)) -
                          (if i = 0 then mat 0 else B(i - 1) ** mat 1))) =
        mat 0`
  MP_TAC THENL
   [SIMP_TAC[MATRIX_CMUL_SUB_LDISTRIB; MSUM_SUB; FINITE_NUMSEG;
             MATRIX_CMUL_ADD_LDISTRIB; MSUM_ADD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MATRIX_CMUL_RZERO] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(if p then mat 0 else x) = (if ~p then x else mat 0)`] THEN
    REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i = 0 <=> i = 0`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ ~(i = 0) <=>
                  1 <= i /\ i <= SUC n`] THEN
    REWRITE_TAC[SING_GSPEC; GSYM numseg; MSUM_SING; real_pow] THEN
    REWRITE_TAC[MATRIX_CMUL_LID] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM th]) THEN
    REWRITE_TAC[MATRIX_NEG_SUB] THEN REWRITE_TAC[MATRIX_SUB; AC MATRIX_ADD_AC
     `(((A:real^N^N) + --B) + B) + C = (--B + B) + A + C`] THEN
    REWRITE_TAC[MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
    REWRITE_TAC[num_CONV `1`] THEN REWRITE_TAC[ADD1; MSUM_OFFSET] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD_SUB; MATRIX_ADD_RNEG];
    REWRITE_TAC[MATRIC_POLYFUN_EQ_0; IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!i:num. B(n - i) = (mat 0:real^N^N)` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
        REWRITE_TAC[LE_REFL; SUB_0; NOT_SUC; ARITH_RULE `~(SUC n <= n)`] THEN
        REWRITE_TAC[MATRIX_ADD_LID; SUC_SUB1; MATRIX_MUL_RID] THEN
        REWRITE_TAC[MATRIX_SUB_LZERO; MATRIX_NEG_EQ_0];
        X_GEN_TAC `m:num` THEN DISCH_TAC THEN
        DISJ_CASES_TAC(ARITH_RULE `n - SUC m = n - m \/ m < n`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num`) THEN
        ASM_SIMP_TAC[ARITH_RULE `m < n ==> ~(n - m = 0)`;
                     ARITH_RULE `n - m <= SUC n /\ n - m <= n`] THEN
        REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_ADD_LID; MATRIX_SUB_LZERO] THEN
        REWRITE_TAC[MATRIX_MUL_RID; MATRIX_NEG_EQ_0] THEN
        ASM_SIMP_TAC[ARITH_RULE `n - m - 1 = n - SUC m`]];
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[SUB_REFL] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[LE_0; MATRIX_MUL_LZERO; MATRIX_ADD_RID] THEN
      REWRITE_TAC[MATRIX_SUB_RZERO; MATRIX_NEG_EQ_0]]]);;
```

### Informal statement
For all square matrices $A$, $B$ (indexed by a natural number), $C$ of dimension $N \times N$ over the real numbers, and for all natural numbers $n$, if for all real numbers $x$ the following equation holds:
$$\sum_{i=0}^{n} x^i B_i \cdot (A - x I) = C$$

where $I$ is the identity matrix, then $C = 0$.

### Informal proof
Let's prove that if $\sum_{i=0}^{n} x^i B_i \cdot (A - x I) = C$ holds for all $x$, then $C = 0$.

* First, we distribute the matrix multiplication over the sum:
  $$\sum_{i=0}^{n} x^i B_i \cdot (A - x I) = \sum_{i=0}^{n} (x^i B_i \cdot A - x^{i+1} B_i)$$

* We can rewrite the right-hand side as the difference of two sums:
  $$\sum_{i=0}^{n} x^i B_i \cdot A - \sum_{i=0}^{n} x^{i+1} B_i = C$$

* For the second sum, we can substitute $j = i+1$ to get:
  $$\sum_{i=0}^{n} x^i B_i \cdot A - \sum_{j=1}^{n+1} x^j B_{j-1} = C$$

* We rearrange this to:
  $$\sum_{i=0}^{n+1} x^i \cdot \left(\begin{cases}
  -C & \text{if } i = 0 \\
  B_i \cdot A & \text{if } 0 < i \leq n \\
  0 & \text{if } i = n+1
  \end{cases} - \begin{cases}
  0 & \text{if } i = 0 \\
  B_{i-1} & \text{if } 0 < i \leq n+1
  \end{cases}\right) = 0$$

* By the matrix polynomial identity principle (indicated by `MATRIC_POLYFUN_EQ_0`), all coefficients must be zero.

* Starting with the highest coefficient at $i = n+1$, we get $B_n = 0$.
* By induction (working backward from $n$ to $0$), we show that $B_i = 0$ for all $i \leq n$.
* Finally, looking at the coefficient for $i = 0$, we get $-C = 0$, thus $C = 0$.

### Mathematical insight
This theorem proves a fundamental property about matrix polynomial equations. It states that if a specific matrix polynomial expression equals a constant matrix $C$ for all values of the variable $x$, then $C$ must be the zero matrix.

The result is similar to the polynomial identity principle where if a polynomial equals zero for all inputs, then all its coefficients must be zero. Here we have a matrix-valued polynomial identity involving a specific structure on the right-hand side.

The theorem is particularly useful in matrix theory and can be applied when analyzing characteristic polynomials, minimal polynomials, and matrix equations more generally. It highlights the connection between matrix algebra and polynomial algebra.

### Dependencies
#### Theorems
- `MSUM_ADD`: Sum of matrix-valued functions distributes over addition
- `MSUM_SUB`: Sum of matrix-valued functions distributes over subtraction
- `MSUM_MATRIX_RMUL`: Right multiplication can be pulled out of matrix sum
- `MSUM_RESTRICT_SET`: Sum over a restricted set equals sum with conditional values
- `MSUM_SING`: Sum over a singleton equals the function evaluated at that element
- `MSUM_OFFSET`: Shifting the index set in a matrix sum

#### Definitions
- `msum`: Matrix sum defined as elementwise application of scalar summation
- `real`: Real part of a complex number

### Porting notes
When porting this theorem:
1. The proof relies heavily on manipulating polynomial expressions with matrix coefficients. Ensure your target system has good support for matrix polynomials.
2. The proof uses the matrix polynomial identity principle (`MATRIC_POLYFUN_EQ_0`), which states that if a matrix polynomial equals zero for all values of the variable, then all coefficient matrices must be zero. This result may need to be established first.
3. The HOL Light notation for matrix multiplication (`**`) and scalar multiplication (`%%`) might differ in other proof assistants.
4. Pay attention to how matrix indexing is handled in the target system, as it may differ significantly from HOL Light.

---

## POLYFUN_N_CONST

### Name of formal statement
POLYFUN_N_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_CONST = prove
 (`!c n. ?b. !x. c = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. if i = 0 then c else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= n) /\ i = 0 <=> i = 0`] THEN
  REWRITE_TAC[SING_GSPEC; SUM_SING; real_pow; REAL_MUL_RID]);;
```

### Informal statement
For any real constant $c$ and natural number $n$, there exists a function $b$ such that:

$$c = \sum_{i=0}^{n} b(i) \cdot x^i$$

for all real values $x$. In other words, any constant can be represented as a polynomial of degree $n$ (or less).

### Informal proof
We need to show the existence of a function $b$ that satisfies the equation for all $x$. There's a simple construction for this:

- Define $b$ as the function that returns $c$ when $i = 0$ and returns $0$ for all other values of $i$. 
  This can be written as: $b(i) = \begin{cases} c & \text{if } i = 0 \\ 0 & \text{otherwise} \end{cases}$

With this definition:
1. The sum $\sum_{i=0}^{n} b(i) \cdot x^i$ simplifies to only the term where $i = 0$
2. When $i = 0$, we have $b(0) \cdot x^0 = c \cdot 1 = c$
3. All other terms in the sum are zero because $b(i) = 0$ for $i \neq 0$

Therefore, the sum equals $c$ for all values of $x$, as required.

### Mathematical insight
This theorem establishes that any constant can be represented as a polynomial of arbitrary degree $n$. While seemingly obvious, this is a foundational result that helps with uniformly representing expressions in polynomial forms of specific degrees.

In context, this theorem is used as part of showing that cofactors and determinants can be expressed as polynomials of specific degrees (degree $n-1$ for cofactors and degree $n$ for determinants). This allows for consistent handling of these expressions in further mathematical development.

The proof uses the simplest possible construction - making only the constant term non-zero. This is the canonical way to represent a constant as a polynomial.

### Dependencies
No significant dependencies from the given information.

### Porting notes
This theorem should port straightforwardly to other proof assistants. The main consideration would be ensuring that the system has:
- Support for polynomial expressions and operations
- The ability to work with functions represented as lambda abstractions
- The concept of summation over ranges

Most proof assistants have these capabilities, making this theorem relatively easy to port.

---

## POLYFUN_N_ADD

### Name of formal statement
POLYFUN_N_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_ADD = prove
 (`!f g. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i)) /\
         (?c. !x. g(x) = sum(0..n) (\i. c i * x pow i))
         ==> ?d. !x. f(x) + g(x) = sum(0..n) (\i. d i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. (b:num->real) i + c i` THEN
  ASM_REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_RDISTRIB]);;
```

### Informal statement
For any functions $f$ and $g$, if:
- there exists coefficients $b_0, b_1, \ldots, b_n$ such that $f(x) = \sum_{i=0}^{n} b_i x^i$ for all $x$, and
- there exists coefficients $c_0, c_1, \ldots, c_n$ such that $g(x) = \sum_{i=0}^{n} c_i x^i$ for all $x$,

then there exists coefficients $d_0, d_1, \ldots, d_n$ such that $f(x) + g(x) = \sum_{i=0}^{n} d_i x^i$ for all $x$.

In other words, the sum of two polynomial functions of degree at most $n$ is also a polynomial function of degree at most $n$.

### Informal proof
The proof shows that we can construct the coefficients $d_i$ of the sum directly from the coefficients of the original polynomials.

1. We define $d_i = b_i + c_i$ for all $i \in \{0,1,\ldots,n\}$.

2. Then:
   $f(x) + g(x) = \sum_{i=0}^{n} b_i x^i + \sum_{i=0}^{n} c_i x^i$
   $= \sum_{i=0}^{n} (b_i + c_i) x^i$
   $= \sum_{i=0}^{n} d_i x^i$

The formal proof uses:
- `SUM_ADD_NUMSEG` to combine the two sums
- `REAL_ADD_RDISTRIB` to handle the distributivity of multiplication over addition for real numbers

### Mathematical insight
This theorem formalizes a fundamental property of polynomial functions: their closure under addition. Given two polynomials of degree at most n, their sum is also a polynomial of degree at most n. The coefficients of the resulting polynomial are simply the sums of the corresponding coefficients of the original polynomials.

This property is part of establishing that polynomials of bounded degree form a vector space, which is a foundational result in polynomial algebra. This particular theorem specifically addresses the vector space axiom of closure under addition.

### Dependencies
- Definitions:
  - `real` - Definition that a complex number is real when its imaginary part is zero

- Theorems (implicitly used):
  - `SUM_ADD_NUMSEG` - Theorem about adding sums over the same range
  - `REAL_ADD_RDISTRIB` - Real number distributivity property

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that polynomials are represented similarly, either as functions or coefficient lists/vectors.
2. The theorem relies on properties of sums and real number arithmetic, which should be available in most systems.
3. The degree bound n is fixed for both polynomials - some systems might prefer a more general formulation where the degrees can differ.

---

## POLYFUN_N_CMUL

### Name of formal statement
POLYFUN_N_CMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_CMUL = prove
 (`!f c. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. c * f(x) = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. c * (b:num->real) i` THEN
  ASM_REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC]);;
```

### Informal statement
For any function $f$ and constant $c$, if $f$ can be expressed as a polynomial of degree at most $n$, i.e., there exists a sequence of coefficients $b_0, b_1, \ldots, b_n$ such that $f(x) = \sum_{i=0}^{n} b_i \cdot x^i$ for all $x$, then the function $c \cdot f$ can also be expressed as a polynomial of degree at most $n$, i.e., there exists a sequence of coefficients $b_0', b_1', \ldots, b_n'$ such that $c \cdot f(x) = \sum_{i=0}^{n} b_i' \cdot x^i$ for all $x$.

### Informal proof
Given a function $f$ that can be expressed as a polynomial of degree at most $n$ with coefficients $b_i$, we need to show that $c \cdot f$ can also be expressed as a polynomial of the same degree.

We propose that the new coefficients are $b_i' = c \cdot b_i$ for all $i$.

Then for any $x$, we have:
\begin{align}
c \cdot f(x) &= c \cdot \sum_{i=0}^{n} b_i \cdot x^i \\
&= \sum_{i=0}^{n} c \cdot b_i \cdot x^i \\
&= \sum_{i=0}^{n} b_i' \cdot x^i
\end{align}

The second equality uses the fact that multiplication by a scalar distributes over summation (this is the `SUM_LMUL` theorem used in the proof). The third equality uses the definition of $b_i'$.

In the HOL Light proof, the associativity of real multiplication (`GSYM REAL_MUL_ASSOC`) is also used to rewrite $c \cdot (b_i \cdot x^i)$ as $(c \cdot b_i) \cdot x^i$.

### Mathematical insight
This theorem establishes that the set of polynomials of degree at most $n$ forms a vector space, as it is closed under scalar multiplication. This is a fundamental property in linear algebra and polynomial theory.

The result is straightforward but essential for establishing the vector space structure of polynomials. When combined with a similar theorem about closure under addition, this would establish that polynomials of bounded degree form a vector space.

### Dependencies
#### Theorems
- `SUM_LMUL`: States that multiplication by a constant can be distributed over a sum: $c \cdot \sum_{i=a}^{b} f(i) = \sum_{i=a}^{b} (c \cdot f(i))$
- `GSYM REAL_MUL_ASSOC`: The associativity of real multiplication, in the form $(c \cdot b) \cdot x = c \cdot (b \cdot x)$

#### Definitions
- `real`: Defines a real number as a complex number with imaginary part equal to zero

### Porting notes
This theorem should be straightforward to port to most proof assistants, as it relies on basic properties of real arithmetic and summation. The proof structure is simple and direct:
1. Introduce the new coefficient sequence $b_i' = c \cdot b_i$
2. Apply scalar multiplication over summation
3. Use associativity of multiplication

Notice that in many systems, this might be a trivial application of existing theorems about polynomial rings or vector spaces, depending on how polynomials are defined.

---

## POLYFUN_N_SUM

### Name of formal statement
POLYFUN_N_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_SUM = prove
 (`!f s. FINITE s /\
         (!a. a IN s ==> ?b. !x. f x a = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. sum s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY; POLYFUN_N_CONST] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_ADD THEN ASM_SIMP_TAC[]);;
```

### Informal statement
Let $f$ be a function of two variables, and let $s$ be a finite set. If for each $a \in s$, there exists a sequence $(b_i)_{i=0}^n$ such that $f(x, a) = \sum_{i=0}^n b_i x^i$ for all $x$, then there exists a sequence $(b_i)_{i=0}^n$ such that $\sum_{a \in s} f(x, a) = \sum_{i=0}^n b_i x^i$ for all $x$.

### Informal proof
This theorem is proved by strong induction on the finite set $s$:

* **Base case**: When $s = \emptyset$, the sum over an empty set is 0, which is a polynomial of degree 0, so the result holds by `POLYFUN_N_CONST`.

* **Inductive step**: Assume the theorem holds for a finite set $t$. We need to show it holds for $s = \{a\} \cup t$ where $a \not\in t$.
  
  By the set sum properties, we have:
  $\sum_{x \in s} f(x, a) = f(x, a) + \sum_{x \in t} f(x, a)$
  
  By our assumption, there exists a sequence $(b_i)_{i=0}^n$ such that $f(x, a) = \sum_{i=0}^n b_i x^i$ for all $x$.
  
  By the inductive hypothesis, there exists a sequence $(c_i)_{i=0}^n$ such that $\sum_{x \in t} f(x, a) = \sum_{i=0}^n c_i x^i$ for all $x$.
  
  Using `POLYFUN_N_ADD`, the sum of two polynomials of degree at most $n$ is also a polynomial of degree at most $n$. Therefore, there exists a sequence $(d_i)_{i=0}^n$ such that:
  $\sum_{x \in s} f(x, a) = f(x, a) + \sum_{x \in t} f(x, a) = \sum_{i=0}^n b_i x^i + \sum_{i=0}^n c_i x^i = \sum_{i=0}^n d_i x^i$
  
  where $d_i = b_i + c_i$ for each $i$.

### Mathematical insight
This theorem extends the polynomial nature of functions to their sums over finite sets. It shows that if each function in a collection is a polynomial of degree at most $n$, then their sum is also a polynomial of degree at most $n$. This result is useful in contexts where we need to manipulate polynomial functions, particularly in algebraic structures, interpolation theory, or numerical analysis.

The theorem provides a constructive result—not only does it state the existence of coefficients for the resulting polynomial, but these coefficients can be computed as sums of the corresponding coefficients of the individual polynomials.

### Dependencies
- **Theorems**:
  - `POLYFUN_N_ADD`: Shows that the sum of two polynomials of degree at most n is also a polynomial of degree at most n
  - `POLYFUN_N_CONST`: Shows that constants are polynomials of degree 0
  - `SUM_CLAUSES`: Properties of summations over sets
  - `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets

### Porting notes
When porting this theorem:
1. Ensure the target system has support for finite sets and summation operations
2. Check that polynomial representation (as coefficient sequences) is compatible with your target system
3. The proof relies heavily on HOL Light's induction tactics for finite sets, so you may need to adapt this approach based on the available induction principles in your target system

---

## POLYFUN_N_PRODUCT

### Name of formal statement
POLYFUN_N_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_PRODUCT = prove
 (`!f s n. FINITE s /\
           (!a:A. a IN s ==> ?c d. !x. f x a = c + d * x) /\ CARD(s) <= n
           ==> ?b. !x. product s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; POLYFUN_N_CONST; FORALL_IN_INSERT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  INDUCT_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_SUC]] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->real`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `d:real`)) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\i. (if i <= n then c * b i else &0) +
                  (if ~(i = 0) then d * b(i - 1) else &0)` THEN
  X_GEN_TAC `x:real` THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; GSYM SUM_LMUL; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE
   `((0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n) /\
    ((0 <= i /\ i <= SUC n) /\ ~(i = 0) <=> 1 <= i /\ i <= SUC n)`] THEN
  REWRITE_TAC[GSYM numseg] THEN
  REWRITE_TAC[MESON[num_CONV `1`; ADD1] `1..SUC n = 0+1..n+1`] THEN
  REWRITE_TAC[SUM_OFFSET; ADD_SUB; REAL_POW_ADD] THEN
  BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function $f: \mathbb{R} \times A \to \mathbb{R}$, finite set $s \subseteq A$, and natural number $n$, if:
- For all $a \in s$, there exist constants $c$ and $d$ such that $f(x, a) = c + d \cdot x$ for all $x \in \mathbb{R}$ (i.e., $f$ is linear in $x$ for each $a$)
- The cardinality of $s$ is at most $n$ ($|s| \leq n$)

Then there exists a sequence of coefficients $b_0, b_1, \ldots, b_n$ such that:
$$\prod_{a \in s} f(x, a) = \sum_{i=0}^{n} b_i \cdot x^i$$

In other words, the product of linear functions over a finite set results in a polynomial of degree at most $n$.

### Informal proof
The proof proceeds by strong induction on the finite set $s$:

- **Base case**: When $s$ is empty, the product becomes 1 (the empty product), which equals $\sum_{i=0}^{n} b_i \cdot x^i$ where $b_0 = 1$ and $b_i = 0$ for $i > 0$. This is handled by the `POLYFUN_N_CONST` theorem.

- **Inductive step**: Assume the result holds for a set $s$, and consider adding an element $a$ to form $s \cup \{a\}$.
  - For $s$, we have $\prod_{a' \in s} f(x, a') = \sum_{i=0}^{n} b_i \cdot x^i$ for some coefficients $b_i$.
  - For the new element $a$, we have $f(x, a) = c + d \cdot x$ for some constants $c$ and $d$.
  - The product over $s \cup \{a\}$ is $(c + d \cdot x) \cdot \sum_{i=0}^{n} b_i \cdot x^i$.
  - Distributing, we get:
    - $c \cdot \sum_{i=0}^{n} b_i \cdot x^i + d \cdot x \cdot \sum_{i=0}^{n} b_i \cdot x^i$
    - $= \sum_{i=0}^{n} c \cdot b_i \cdot x^i + \sum_{i=0}^{n} d \cdot b_i \cdot x^{i+1}$
    - $= \sum_{i=0}^{n} c \cdot b_i \cdot x^i + \sum_{i=1}^{n+1} d \cdot b_{i-1} \cdot x^i$
  
  - Now we need coefficients for $\sum_{i=0}^{n+1} b'_i \cdot x^i$. We set:
    - $b'_i = c \cdot b_i + d \cdot b_{i-1}$ for $1 \leq i \leq n$
    - $b'_0 = c \cdot b_0$ (since there is no $b_{-1}$)
    - $b'_{n+1} = d \cdot b_n$ (since there is no $b_{n+1}$ in the original sum)
  
  - This is implemented in the code as:
    ```
    \i. (if i <= n then c * b i else &0) + (if ~(i = 0) then d * b(i - 1) else &0)
    ```

The proof handles the algebraic manipulations using operations on sums over intervals, with appropriate range adjustments to align the indices correctly when shifting the summation.

### Mathematical insight
This theorem captures an important property about products of linear functions: they produce polynomials with degree bounded by the number of factors. This is a foundational result in polynomial algebra, showing how degree grows under multiplication.

The result generalizes the well-known fact that the product of $n$ linear polynomials $(a_1 + b_1x)(a_2 + b_2x)\cdots(a_n + b_nx)$ yields a polynomial of degree at most $n$. 

This theorem is particularly useful in formal developments of polynomial theory, algebraic manipulations, and in contexts where polynomials arise from products of simpler functions.

### Dependencies
- **Definitions**
  - `real`: Defines a real number as a complex number with zero imaginary part

- **Theorems** (inferred from the proof)
  - `POLYFUN_N_CONST`: Likely states that a constant function can be represented as a polynomial
  - `PRODUCT_CLAUSES`: Properties of product operation over sets
  - `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets
  - Various arithmetic and sum manipulation theorems

### Porting notes
- The proof relies on HOL Light's handling of polynomials and summations. When porting to another system:
  - Ensure the target system has a good library for polynomial operations
  - Pay attention to how empty products are defined (typically as 1)
  - The indexing in summations and the offset calculations may need adjustments based on how the target system handles index shifts in sums
  - The conditional expression for constructing the new coefficient sequence may need reformulation depending on the syntax of the target system

---

## COFACTOR_ENTRY_AS_POLYFUN

### Name of formal statement
COFACTOR_ENTRY_AS_POLYFUN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COFACTOR_ENTRY_AS_POLYFUN = prove
 (`!A:real^N^N x i j.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> ?c. !x. cofactor(A - x %% mat 1)$i$j =
                    sum(0..dimindex(:N)-1) (\i. c(i) * x pow i)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cofactor; LAMBDA_BETA; det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  SUBGOAL_THEN `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN ASM_ARITH_TAC;
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG]] THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[CARD_DELETE; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; IN_DELETE; CARD_NUMSEG_1; LE_REFL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:num->num) k = j` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(EXISTS_TAC `&0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;
```

### Informal statement
For any $A \in \mathbb{R}^{N \times N}$, any $x \in \mathbb{R}$, and any indices $i, j$ such that $1 \leq i \leq N$ and $1 \leq j \leq N$, there exists a function $c$ such that the cofactor of the matrix $(A - x \cdot I)$ at position $(i,j)$ can be expressed as a polynomial in $x$ of the form:

$$\text{cofactor}(A - x \cdot I)_{i,j} = \sum_{k=0}^{N-1} c(k) \cdot x^k$$

where $I$ is the identity matrix.

### Informal proof
The proof shows that the cofactor entry is a polynomial function of $x$:

1. We begin by simplifying using the definition of cofactor and determinant:
   - The cofactor at position $(i,j)$ is $(-1)^{i+j}$ times the determinant of the minor obtained by deleting row $i$ and column $j$.
   - The determinant is a sum over all permutations of products of matrix entries.

2. We apply `POLYFUN_N_SUM` to establish that a sum of polynomial functions is a polynomial function.

3. For each permutation $p$ in the determinant formula, we need to show its contribution is a polynomial in $x$.
   
4. We express the set $\{1, 2, \ldots, N\}$ as $\{i\} \cup (\{1, 2, \ldots, N\} \setminus \{i\})$ to separate the term containing row $i$.

5. Using `PRODUCT_CLAUSES`, we split the product into the entry at row $i$ and the product of remaining entries.

6. Since each matrix entry of $(A - x \cdot I)$ is of the form $A_{kl} - x \cdot \delta_{kl}$ (where $\delta_{kl}$ is the Kronecker delta), each entry is a linear function of $x$.

7. We have two cases for the entry at position $(i, p(k))$:
   - If $p(k) = j$, the term contains $(A_{ij} - x)$, a linear function of $x$.
   - If $p(k) \neq j$, the term is $A_{i,p(k)}$, a constant with respect to $x$.

8. The product of these entries results in a polynomial in $x$ of degree at most $N-1$.

9. Therefore, the cofactor can be expressed as a sum of polynomial functions of $x$ with degree at most $N-1$.

### Mathematical insight
This theorem establishes that each cofactor entry of a matrix of the form $(A - xI)$ can be expressed as a polynomial in the variable $x$. This is a key component in understanding the characteristic polynomial of a matrix and the adjugate (classical adjoint) matrix.

The result has important applications in linear algebra, particularly in the study of eigenvalues and the characteristic polynomial. It shows that cofactors of the characteristic matrix are themselves polynomials of one degree less than the characteristic polynomial itself (which is of degree $N$).

This is useful for various matrix decompositions, Cramer's rule applications, and when working with the adjugate matrix in the context of matrix inverses and eigenvalue problems.

### Dependencies
- **Definitions:**
  - `real`: Defines a complex number to be real when its imaginary part is zero.
- **Theorems used in proof:**
  - `cofactor`: Definition of matrix cofactor.
  - `det`: Definition of matrix determinant.
  - `POLYFUN_N_SUM`: States that a sum of polynomial functions is a polynomial function.
  - `POLYFUN_N_CMUL`: States that a constant multiple of a polynomial function is a polynomial function.
  - `POLYFUN_N_PRODUCT`: States that a product of polynomial functions is a polynomial function.
  - `PERMUTES_IN_IMAGE`: Property of permutation functions.
  - Various simplification theorems for sets, matrices, and arithmetic operations.

### Porting notes
When porting this theorem:
1. Ensure that the destination system has a well-defined notion of cofactors and determinants for matrices.
2. The representation of polynomials may differ between systems - some may use explicit polynomial types rather than functional representation.
3. The theorem relies heavily on the permutation-based definition of determinants, which might require adaptation in systems using different determinant definitions.
4. The identity matrix is represented as `mat 1` in HOL Light, which may have a different notation in other systems.
5. In the proof, indices start at 1, which might need adjustment in systems with 0-based indexing.

---

## DETERMINANT_AS_POLYFUN

### Name of formal statement
DETERMINANT_AS_POLYFUN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DETERMINANT_AS_POLYFUN = prove
 (`!A:real^N^N.
        ?c. !x. det(A - x %% mat 1) =
                sum(0..dimindex(:N)) (\i. c(i) * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; LE_REFL; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;
```

### Informal statement
For any $A \in \mathbb{R}^{N \times N}$ (represented as `A:real^N^N`), there exists a function $c$ such that for all $x$, the determinant of $A - x \cdot I$ can be expressed as a polynomial:

$$\text{det}(A - x \cdot I) = \sum_{i=0}^N c(i) \cdot x^i$$

where $I$ is the identity matrix (represented as `mat 1` in HOL Light).

### Informal proof
This theorem states that the characteristic polynomial of a matrix can be written as a sum of monomials. The proof proceeds as follows:

* Begin by expanding the determinant using its definition as a sum over permutations.
* Apply `POLYFUN_N_SUM` to show that a sum of polynomial functions is also a polynomial function.
* For each permutation $p$ in the determinant formula, we need to show that the corresponding term is a polynomial in $x$.
* Use `POLYFUN_N_CMUL` to handle the sign term (which is independent of $x$).
* Apply `POLYFUN_N_PRODUCT` to handle the product of matrix entries.
* For each index $k$ in the range $1..N$, show that $(A - x \cdot I)_{k,p(k)}$ is a polynomial in $x$.
* Simplify the matrix components: 
  * $(A - x \cdot I)_{k,p(k)} = A_{k,p(k)} - x \cdot I_{k,p(k)}$
  * When $k = p(k)$, this equals $A_{k,k} - x$
  * When $k \neq p(k)$, this equals $A_{k,p(k)}$ (since $I_{k,p(k)} = 0$)
* Rewrite the subtraction as addition with negative coefficient: $a - x \cdot d = a + (-d) \cdot x$
* This shows each component is a polynomial in $x$, completing the proof.

### Mathematical insight
This theorem establishes the well-known result that the characteristic polynomial of a matrix can be expressed as a polynomial in the eigenvalue variable. This is a foundational result in linear algebra, enabling the computation of eigenvalues through the roots of the characteristic polynomial.

The determinant of $A - x \cdot I$ is precisely the characteristic polynomial of matrix $A$, and this theorem confirms that it has the polynomial form $\sum_{i=0}^N c(i) \cdot x^i$. The coefficients $c(i)$ capture important invariants of the matrix, with $c(N) = (-1)^N$ and the constant term $c(0) = \det(A)$.

This polynomial representation is crucial for studying the spectral properties of matrices and is connected to the Cayley-Hamilton theorem, which states that every matrix satisfies its own characteristic polynomial.

### Dependencies
- Definitions:
  - `real` - Defines a real number as a complex number with zero imaginary part

- Implicit theorems:
  - `POLYFUN_N_SUM` - Shows that a sum of polynomial functions is also a polynomial function
  - `POLYFUN_N_CMUL` - Shows that a constant multiple of a polynomial function is also a polynomial function
  - `POLYFUN_N_PRODUCT` - Shows that a product of polynomial functions is also a polynomial function
  - `FINITE_PERMUTATIONS` - States that the set of permutations on a finite set is finite
  - `PERMUTES_IN_IMAGE` - Property of permutation functions

### Porting notes
When porting this theorem to another system:

1. Ensure the target system has a well-developed theory of matrices, determinants, and polynomials.
2. The identity matrix representation may differ between systems - in HOL Light it's `mat 1`.
3. The proof relies on characterizing the determinant as a sum over permutations, which might be defined differently in other systems.
4. The polynomial manipulation theorems (`POLYFUN_N_SUM`, `POLYFUN_N_CMUL`, `POLYFUN_N_PRODUCT`) will need equivalent versions in the target system.

---

## char_poly

### Name of formal statement
char_poly

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let char_poly = new_specification ["char_poly"]
  (REWRITE_RULE[SKOLEM_THM] DETERMINANT_AS_POLYFUN);;
```

### Informal statement
The `char_poly` is a specification that defines the characteristic polynomial of a matrix. It is derived from the determinant as a polynomial function, using the result `DETERMINANT_AS_POLYFUN` which expresses the determinant in polynomial form.

### Informal proof
The definition is established through a specification using the Skolemization of the theorem `DETERMINANT_AS_POLYFUN`. This is not a proof but a definition created by extracting the existential witness from the `DETERMINANT_AS_POLYFUN` theorem.

The process involves:
1. Taking the theorem `DETERMINANT_AS_POLYFUN` which asserts the existence of coefficients that express the determinant as a polynomial function
2. Applying `SKOLEM_THM` to eliminate the existential quantifier and obtain a concrete function
3. Using `REWRITE_RULE` to substitute this into a new specification named "char_poly"

### Mathematical insight
The characteristic polynomial of a matrix A is defined as the polynomial $\det(A - \lambda I)$ where $\lambda$ is a variable, $I$ is the identity matrix, and $\det$ is the determinant. This is a fundamental concept in linear algebra with numerous applications:

- The roots of the characteristic polynomial are the eigenvalues of the matrix
- It's used in diagonalization and computing matrix exponentials
- It appears in the Cayley-Hamilton theorem, which states that a matrix satisfies its own characteristic polynomial

This specification likely creates a function that computes the coefficients of this polynomial, rather than requiring the symbolic computation of the determinant expression each time.

### Dependencies
- Theorems:
  - `DETERMINANT_AS_POLYFUN`: Expresses the determinant as a polynomial function
  - `SKOLEM_THM`: Used for extracting a witness from an existentially quantified theorem

### Porting notes
When porting this to other systems:
1. You'll need to ensure the target system has a theory of polynomials and matrices
2. Verify that the target system has an equivalent to HOL Light's `new_specification` mechanism, which introduces a constant based on an existentially quantified theorem
3. The implementation will depend on how the determinant is defined in the target system
4. Consider whether the target system requires explicit type annotations for the matrix elements and the polynomial coefficients

---

## COFACTOR_AS_MATRIC_POLYNOMIAL

### Name of formal statement
COFACTOR_AS_MATRIC_POLYNOMIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COFACTOR_AS_MATRIC_POLYNOMIAL = prove
 (`!A:real^N^N. ?C.
      !x. cofactor(A - x %% mat 1) =
          msum(0..dimindex(:N)-1) (\i. x pow i %% C i)`,
  GEN_TAC THEN SIMP_TAC[CART_EQ; MSUM_COMPONENT; FINITE_NUMSEG] THEN
  MP_TAC(ISPEC `A:real^N^N` COFACTOR_ENTRY_AS_POLYFUN) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LAMBDA_SKOLEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(num->real)^N^N` ASSUME_TAC) THEN
  EXISTS_TAC `(\i. lambda j k. ((c:(num->real)^N^N)$j$k) i):num->real^N^N` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `i:num`] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; LAMBDA_BETA] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any matrix $A \in \mathbb{R}^{N \times N}$, there exists a sequence of matrices $C_0, C_1, \ldots, C_{N-1} \in \mathbb{R}^{N \times N}$ such that the cofactor matrix of $(A - x \cdot I)$ can be expressed as a polynomial in $x$ with matrix coefficients:

$$\text{cofactor}(A - x \cdot I) = \sum_{i=0}^{\text{dimindex}(:N)-1} x^i \cdot C_i$$

where $I$ is the identity matrix (represented as `mat 1` in HOL Light), and $\text{dimindex}(:N)$ is the dimension of the type $\mathbb{R}^N$.

### Informal proof
The proof proceeds as follows:

- Begin by establishing that to prove equality between matrices, it's sufficient to show equality of all their components.

- Apply the `COFACTOR_ENTRY_AS_POLYFUN` theorem to $A$, which gives for each entry of the cofactor matrix, a polynomial representation in $x$. Specifically, for any indices $j$ and $i$ in the appropriate ranges, the $(j,i)$-th component of $\text{cofactor}(A - x \cdot I)$ can be written as $\sum_{k=0}^{\text{dimindex}(:N)-1} c_{j,i}(k) \cdot x^k$ for some coefficient functions $c_{j,i}$.

- Define the sequence of matrices $C$ where each $C_i$ is the matrix with entries $(C_i)_{j,k} = c_{j,k}(i)$.

- Verify that with this definition, the component-wise equality holds:
  $$[\text{cofactor}(A - x \cdot I)]_{i,j} = \sum_{k=0}^{\text{dimindex}(:N)-1} x^k \cdot (C_k)_{i,j}$$

- Use algebraic manipulations and the properties of matrix multiplication to establish the desired equality.

### Mathematical insight
This theorem provides a polynomial representation of the cofactor matrix of $(A - xI)$, which is an important step toward proving the Cayley-Hamilton theorem. The Cayley-Hamilton theorem states that every square matrix satisfies its own characteristic polynomial.

The representation established here expresses the cofactor matrix as a polynomial in $x$ with matrix coefficients. This structural insight allows us to relate the cofactor matrix to the characteristic polynomial, which is the determinant of $(A - xI)$.

This result demonstrates how matrix operations can be reduced to polynomial operations, allowing powerful algebraic techniques to be applied to matrix theory.

### Dependencies
#### Theorems
- `MSUM_COMPONENT`: Relates the components of a matrix sum to the sum of the corresponding components
- `COFACTOR_ENTRY_AS_POLYFUN`: Expresses each entry of the cofactor matrix as a polynomial function

#### Definitions
- `msum`: Matrix summation operation
- `real`: Condition for a complex number to be real (Im z = 0)

### Porting notes
When porting this theorem:
- Ensure that the target system has a suitable representation of matrices and their operations
- The proof relies heavily on component-wise reasoning about matrices, which might need different tactics in systems with a more abstract approach to linear algebra
- The handling of finite summations might differ between systems, especially in how indexed families of objects are represented

---

## MATRIC_POWER_DIFFERENCE

### MATRIC_POWER_DIFFERENCE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let MATRIC_POWER_DIFFERENCE = prove
 (`!A:real^N^N x n.
        A mpow (SUC n) - x pow (SUC n) %% mat 1 =
        msum (0..n) (\i. x pow i %% A mpow (n - i)) ** (A - x %% mat 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MSUM_CLAUSES_NUMSEG; real_pow; SUB_0; mpow] THEN
    REWRITE_TAC[MATRIX_MUL_RID; MATRIX_CMUL_LID; MATRIX_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(A mpow SUC n - x pow SUC n %% mat 1) ** A +
      (x pow (SUC n) %% mat 1 :real^N^N) ** (A - x %% mat 1:real^N^N)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MPOW_SUC] THEN
      REWRITE_TAC[MATRIX_SUB_RDISTRIB; MATRIX_SUB_LDISTRIB] THEN
      REWRITE_TAC[MATRIX_SUB; MATRIX_MUL_LMUL; MATRIX_MUL_LID] THEN
      REWRITE_TAC[GSYM MATRIX_ADD_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
      REWRITE_TAC[real_pow; MATRIX_CMUL_ASSOC] THEN REWRITE_TAC[REAL_MUL_AC];

      ASM_REWRITE_TAC[MSUM_CLAUSES_NUMSEG; LE_0] THEN
      REWRITE_TAC[SUB_REFL; mpow; MATRIX_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC MSUM_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MATRIX_MUL_LMUL] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
      REWRITE_TAC[MPOW_SUC; GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN
      REWRITE_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_LMUL] THEN
      REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]]]);;
```

### Informal statement
For any matrix $A \in \mathbb{R}^{N \times N}$, scalar $x \in \mathbb{R}$, and natural number $n$:

$$A^{n+1} - x^{n+1} I = \sum_{i=0}^{n} x^i A^{n-i} (A - xI)$$

where $A^n$ represents the $n$-th power of matrix $A$, $I$ is the identity matrix, and $x^n$ is the $n$-th power of the scalar $x$.

### Informal proof
We prove this by induction on $n$.

**Base case**: $n = 0$
We need to show: $A^1 - x^1 I = \sum_{i=0}^{0} x^i A^{0-i} (A - xI)$

The right side simplifies to $x^0 A^{0} (A - xI) = 1 \cdot I \cdot (A - xI) = A - xI$
The left side is $A - xI$
So both sides are equal.

**Inductive step**: Assume the formula holds for $n$, we'll show it for $n+1$.

We need to show:
$$A^{n+2} - x^{n+2}I = \sum_{i=0}^{n+1} x^i A^{n+1-i} (A - xI)$$

We'll transform the left side as follows:
$$(A^{n+1} - x^{n+1}I)A + x^{n+1}I(A - xI)$$

The first term $(A^{n+1} - x^{n+1}I)A$ expands using the inductive hypothesis:
$$\left(\sum_{i=0}^{n} x^i A^{n-i} (A - xI)\right)A$$

The second term $x^{n+1}I(A - xI)$ equals $x^{n+1}A - x^{n+2}I$

For the sum, we apply the distributive property of matrix multiplication and use:
$$\sum_{i=0}^{n} x^i A^{n-i} (A - xI)A = \sum_{i=0}^{n} x^i A^{n+1-i} (A - xI)$$

This gives us:
$$\sum_{i=0}^{n} x^i A^{n+1-i} (A - xI) + x^{n+1}A - x^{n+2}I$$

The $x^{n+1}A$ term can be written as $x^{n+1}A^1(A-xI) + x^{n+2}I$, which gives the term for $i=n+1$ in our summation, plus a cancellation term.

This completes the sum from $i=0$ to $i=n+1$ as required.

### Mathematical insight
This theorem presents a matrix analog of the familiar difference of powers formula from algebra:
$$a^{n+1} - b^{n+1} = (a-b)(a^n + a^{n-1}b + a^{n-2}b^2 + ... + ab^{n-1} + b^n)$$

In our case, we're dealing with a matrix $A$ and a scalar $x$ times the identity matrix. The formula gives a decomposition of $A^{n+1} - x^{n+1}I$ in terms of the difference $A - xI$.

This result is particularly useful in spectral theory and when studying matrix functions, especially when considering how powers of a matrix relate to its eigenvalues.

### Dependencies
- **Theorems**
  - `MSUM_MATRIX_RMUL`: For matrices and finite sums, $\sum_{i \in s} f(i)A = (\sum_{i \in s} f(i))A$
  - `MSUM_EQ`: For equal functions on a set, their matrix sums are equal
  - `MSUM_CLAUSES_NUMSEG`: Properties of matrix sums over numeric segments
- **Definitions**
  - `msum`: Matrix sum over a set
  - `real`: Real numbers as complex numbers with zero imaginary part

### Porting notes
When porting this theorem, note that:
1. The matrix power notation in HOL Light (`mpow`) may differ from other systems
2. Matrix multiplication is denoted by `**` in HOL Light
3. Scalar multiplication of matrices uses `%%` in HOL Light
4. The identity matrix is represented as `mat 1` in HOL Light

---

## MATRIC_CHARPOLY_DIFFERENCE

### Name of formal statement
MATRIC_CHARPOLY_DIFFERENCE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_CHARPOLY_DIFFERENCE = prove
 (`!A:real^N^N. ?B.
      !x. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) -
          sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1 =
          msum(0..(dimindex(:N)-1)) (\i. x pow i %% B i) ** (A - x %% mat 1)`,
  GEN_TAC THEN SPEC_TAC(`dimindex(:N)`,`n:num`) THEN
  SPEC_TAC(`char_poly(A:real^N^N)`,`c:num->real`) THEN
  GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[MSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0] THENL
   [EXISTS_TAC `(\i. mat 0):num->real^N^N` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[real_pow; MATRIX_MUL_LMUL; MATRIX_MUL_LZERO; mpow;
                REAL_MUL_RID; MATRIX_CMUL_RZERO; MATRIX_SUB_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:num->real^N^N`) THEN
    REWRITE_TAC[MATRIX_SUB; MATRIX_NEG_ADD; MATRIX_CMUL_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC MATRIX_ADD_AC
     `(A + B) + (C + D):real^N^N = (A + C) + (B + D)`] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_SUB] THEN
    REWRITE_TAC[GSYM MATRIX_CMUL_ASSOC; GSYM MATRIX_CMUL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATRIC_POWER_DIFFERENCE; SUC_SUB1] THEN
    EXISTS_TAC `(\i. (if i <= n - 1 then B i else mat 0) +
                     c(SUC n) %% A mpow (n - i)):num->real^N^N` THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB] THEN
    SIMP_TAC[MSUM_ADD; FINITE_NUMSEG; MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_LMUL] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THENL
     [REWRITE_TAC[COND_RAND; COND_RATOR; MATRIX_CMUL_RZERO] THEN
      REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
      REWRITE_TAC[numseg; ARITH_RULE
       `(0 <= i /\ i <= n) /\ i <= n - 1 <=> 0 <= i /\ i <= n - 1`];
      SIMP_TAC[GSYM MSUM_LMUL; FINITE_NUMSEG; MATRIX_CMUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_SYM]]]);;
```

### Informal statement
For any square matrix $A \in \mathbb{R}^{N \times N}$, there exists a function $B : \mathbb{N} \rightarrow \mathbb{R}^{N \times N}$ such that for all $x \in \mathbb{R}$:

$$\sum_{i=0}^{N} c_i A^i - \left(\sum_{i=0}^{N} c_i x^i\right) I = \left(\sum_{i=0}^{N-1} x^i B_i\right) (A - xI)$$

where:
- $c_i = \text{char_poly}(A)(i)$ is the $i$-th coefficient of the characteristic polynomial of $A$
- $I$ is the identity matrix (denoted as $\text{mat}\ 1$ in HOL Light)
- $A^i$ is the $i$-th power of matrix $A$ (denoted as $A\ \text{mpow}\ i$ in HOL Light)

### Informal proof
The proof proceeds by induction on the dimension $N$ of the matrix.

**Base case (n = 0):**
- When $n = 0$, we define $B_i = 0$ for all $i$.
- The left-hand side reduces to $c_0 I - c_0 I = 0$
- The right-hand side becomes $0 \cdot (A - xI) = 0$
- So the equation holds trivially.

**Induction step:**
- Assume the statement holds for dimension $n$, i.e., there exists $B$ such that:
  $$\sum_{i=0}^{n} c_i A^i - \left(\sum_{i=0}^{n} c_i x^i\right) I = \left(\sum_{i=0}^{n-1} x^i B_i\right) (A - xI)$$
  
- For dimension $n+1$, we need to show there exists $B'$ such that:
  $$\sum_{i=0}^{n+1} c_i A^i - \left(\sum_{i=0}^{n+1} c_i x^i\right) I = \left(\sum_{i=0}^{n} x^i B'_i\right) (A - xI)$$

- We rearrange the left-hand side:
  $$\left(\sum_{i=0}^{n} c_i A^i - \sum_{i=0}^{n} c_i x^i I\right) + (c_{n+1}A^{n+1} - c_{n+1}x^{n+1}I)$$

- Using the induction hypothesis for the first term, and the identity $A^{n+1} - x^{n+1}I = A^n(A - xI) + x^n(A - xI)$ for the second, we simplify.

- We define $B'_i$ as:
  $$B'_i = \begin{cases}
    B_i + c_{n+1}A^{n-i} & \text{if } i \leq n-1 \\
    c_{n+1}I & \text{if } i = n
  \end{cases}$$

- With this definition, the equation for dimension $n+1$ is satisfied.

### Mathematical insight
This theorem provides a factorization result for the difference between the evaluation of the characteristic polynomial at the matrix itself and the scalar evaluation times the identity matrix. This factorization shows that this difference is always divisible (in the matrix sense) by $(A - xI)$.

The result is closely related to the Cayley-Hamilton theorem, which states that a square matrix satisfies its own characteristic polynomial. It provides algebraic insight into the relationship between a matrix, its characteristic polynomial, and polynomial evaluations.

The theorem can be seen as a matrix analogue of the polynomial remainder theorem, which states that a polynomial $p(x)$ evaluated at $a$ equals the remainder when $p(x)$ is divided by $(x - a)$.

### Dependencies
- **Theorems**:
  - `MSUM_LMUL`: Matrix sum of scalar multiples equals scalar multiple of matrix sum
  - `MSUM_ADD`: Matrix sum distributes over matrix addition
  - `MSUM_RESTRICT_SET`: Matrix sum over a restricted set equals sum with conditional values
  - `MSUM_CLAUSES_NUMSEG`: Matrix sum clauses for number segments

- **Definitions**:
  - `real`: Definition of real numbers
  - `msum`: Matrix sum over a set

### Porting notes
- The proof relies heavily on matrix algebra and the characteristic polynomial. In other systems, ensure that the matrix operations (especially power and multiplication) are properly defined.
- The inductive approach on dimension might need adaptation in systems where matrices are defined differently.
- HOL Light's `mpow` for matrix power and characteristic polynomial computation may have different interfaces in other systems.
- Some systems might already have built-in theorems about the relationship between matrices and their characteristic polynomials, which could simplify the port.

---

## CAYLEY_HAMILTON

### Name of formal statement
CAYLEY_HAMILTON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CAYLEY_HAMILTON = prove
 (`!A:real^N^N. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0`,
  GEN_TAC THEN MATCH_MP_TAC MATRIC_POLY_LEMMA THEN MATCH_MP_TAC(MESON[]
   `!g. (!x. g x = k) /\ (?a b c. !x. f a b c x = g x)
        ==> ?a b c. !x. f a b c x = k`) THEN
  EXISTS_TAC
   `\x. (msum(0..dimindex(:N)) (\i. char_poly A i %% (A:real^N^N) mpow i) -
         sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1) +
        sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_SUB; GSYM MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG] THEN
    REWRITE_TAC[MATRIX_ADD_RID];
    X_CHOOSE_THEN `B:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `A:real^N^N` MATRIC_CHARPOLY_DIFFERENCE) THEN
    REWRITE_TAC[GSYM char_poly; GSYM MATRIX_MUL_LEFT_COFACTOR] THEN
    REWRITE_TAC[GSYM MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM COFACTOR_TRANSP; TRANSP_MATRIX_SUB] THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
    X_CHOOSE_THEN `C:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `transp A:real^N^N` COFACTOR_AS_MATRIC_POLYNOMIAL) THEN
    MAP_EVERY EXISTS_TAC
     [`A:real^N^N`; `(\i. B i + C i):num->real^N^N`; `dimindex(:N)-1`] THEN
    SIMP_TAC[GSYM MSUM_ADD; FINITE_NUMSEG; MATRIX_CMUL_ADD_LDISTRIB]]);;
```

### Informal statement
For any square matrix $A$ of size $N \times N$ over the real numbers, the sum
$$\sum_{i=0}^{N} c_i A^i = 0$$
where $c_i$ are the coefficients of the characteristic polynomial of $A$, and $A^i$ represents the $i$-th power of the matrix $A$.

More precisely, if we denote by $\text{char\_poly}(A, i)$ the $i$-th coefficient of the characteristic polynomial of $A$, then
$$\sum_{i=0}^{\text{dimindex}(:N)} \text{char\_poly}(A, i) \cdot A^i = 0_{N \times N}$$
where $0_{N \times N}$ is the zero matrix of size $N \times N$.

### Informal proof
The proof follows these main steps:

* We apply `MATRIC_POLY_LEMMA` which allows us to work with matrix polynomial expressions.
* We introduce a function $g(x)$ that represents the left side of our equation.
* We show that $g(x)$ can be rewritten as the sum of two terms:
  - The difference between the original polynomial applied to $A$ and the scalar polynomial times the identity matrix
  - The scalar polynomial times the identity matrix
* These terms are constructed so that their sum equals $g(x)$ but we can prove the sum is zero.

* For the first part, we simplify the expression using matrix algebra, showing that the difference of these terms cancels out.

* For the second part:
  - We apply `MATRIC_CHARPOLY_DIFFERENCE` to express the relationship between $A$ and its characteristic polynomial
  - We use cofactor properties (`MATRIX_MUL_LEFT_COFACTOR`)
  - We apply transpose properties (`COFACTOR_TRANSP`, `TRANSP_MATRIX_SUB`, etc.)
  - We use `COFACTOR_AS_MATRIC_POLYNOMIAL` to represent the cofactor in polynomial form
  - Finally we combine all these results to demonstrate that the expression equals the zero matrix

* The proof concludes by showing that the matrix polynomial evaluates to the zero matrix, confirming the Cayley-Hamilton theorem.

### Mathematical insight
The Cayley-Hamilton theorem is a fundamental result in linear algebra stating that every square matrix satisfies its own characteristic polynomial. This theorem connects the algebraic properties of matrices (specifically their eigenvalues) with their power structure.

The characteristic polynomial of a matrix $A$ is defined as $\det(A - λI)$, where $λ$ is a variable. The theorem states that if we substitute the matrix $A$ itself for $λ$ in this polynomial, the result is the zero matrix.

This theorem has numerous applications:
- It provides a way to express higher powers of a matrix in terms of lower powers
- It's central to understanding minimal polynomials and matrix diagonalization
- It helps establish connections between matrices' eigenvalues and their behavior under functional calculus

The proof approach used here involves manipulating matrix polynomials and using properties of cofactors and the characteristic polynomial's definition.

### Dependencies
#### Theorems
- `MSUM_ADD`: For finite sets, the matrix sum of a sum of functions equals the sum of the matrix sums
- `MATRIC_POLY_LEMMA`: Lemma about matrix polynomials
- `MATRIC_CHARPOLY_DIFFERENCE`: Relationship between a matrix and its characteristic polynomial
- `MATRIX_MUL_LEFT_COFACTOR`: Property of matrix multiplication with cofactors
- `COFACTOR_AS_MATRIC_POLYNOMIAL`: Representation of cofactors as matrix polynomials

#### Definitions
- `msum`: Matrix summation, defined as $(msum\ s\ f)_{ij} = \sum_{x \in s} f(x)_{ij}$
- `char_poly`: The coefficients of the characteristic polynomial of a matrix
- `mpow`: Matrix power operation

### Porting notes
When porting this theorem:
1. Ensure the characteristic polynomial coefficients are defined consistently (some systems use reversed order)
2. Pay attention to matrix power indexing (whether $A^0$ is included and how it's handled)
3. The proof relies heavily on matrix polynomial manipulation, so similar lemmas about matrix polynomials and cofactor representations will be needed in the target system
4. Verify that matrix operations like addition, multiplication, and transposes have equivalent properties in the target system

---

