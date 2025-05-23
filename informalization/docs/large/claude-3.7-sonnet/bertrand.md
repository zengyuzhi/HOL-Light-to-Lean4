# bertrand.ml

## Overview

Number of statements: 88

This file contains a formalization of Bertrand's postulate, which states that for any n > 3, there is always at least one prime p such that n < p < 2n. It also includes a proof of a weak form of the Prime Number Theorem, characterizing the asymptotic distribution of prime numbers. The development builds upon HOL Light's libraries for prime numbers, analysis, and transcendental functions to establish these significant number-theoretic results.

## num_of_float

### Name of formal statement
num_of_float

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let num_of_float =
  let p22 = ( ** ) 2.0 22.0
  and p44 = ( ** ) 2.0 44.0
  and p66 = ( ** ) 2.0 66.0
  and q22 = pow2 22 and q44 = pow2 44 and q66 = pow2 66 in
  fun x ->
    let y0,n = frexp x in
    let u0 = int_of_float(y0 *. p22) in
    let y1 = p22 *. y0 -. float_of_int u0 in
    let u1 = int_of_float(y1 *. p22) in
    let y2 = p22 *. y1 -. float_of_int u1 in
    let u2 = int_of_float(y2 *. p22) in
    let y3 = p22 *. y2 -. float_of_int u2 in
    if y3 <> 0.0 then failwith "num_of_float: inexactness!" else
    (num u0 // q22 +/ num u1 // q44 +/ num u2 // q66) */ pow2 n;;
```

### Informal statement
The function `num_of_float` converts a floating-point number into a rational number in the HOL Light's numerics system. It takes a float `x` and:

1. Decomposes `x` as `y0 * 2^n` using `frexp`.
2. Precisely represents `y0` using a series of three 22-bit approximations:
   * Computes `u0` by scaling `y0` up by $2^{22}$ and converting to an integer
   * Finds the remaining fraction `y1`, scales it up by $2^{22}$, and extracts `u1`
   * Finds the next remaining fraction `y2`, scales it up by $2^{22}$, and extracts `u2`
   * Computes `y3` to check if the conversion is exact

3. The function fails with "num_of_float: inexactness!" if `y3` is not zero (indicating the float cannot be precisely represented).
4. If successful, returns the rational number: 
   $$\left(\frac{u_0}{2^{22}} + \frac{u_1}{2^{44}} + \frac{u_2}{2^{66}}\right) \cdot 2^n$$

### Informal proof
This is a definition, not a theorem, so it doesn't have a proof.

### Mathematical insight
This function addresses an omission in the OCaml Num library by providing a way to convert floating-point numbers to exact rational numbers. The implementation:

1. Uses a technique similar to continued fractions to capture the binary representation precisely.
2. Leverages the binary nature of floating-point numbers by working with powers of 2.
3. Handles precision limits by using three 22-bit segments, which together can represent the mantissa of a standard IEEE 754 double-precision float (which has a 52-bit significand).
4. Captures the exact value when the floating-point number has a finite binary representation, and fails explicitly when it doesn't.

This function is particularly useful for numerical analysis in theorem proving where maintaining exactness is critical, especially when interacting between the floating-point world and the exact rational representation used in formal proofs.

### Dependencies
- `frexp`: Standard floating-point function that decomposes a float into a normalized fraction and a power of 2
- `pow2`: Function that computes powers of 2 as an integer
- `int_of_float`, `float_of_int`: Type conversion functions
- `num`, `(//)`': Number construction and rational number creation
- `(+/)`, `(*/)`': Operations for adding and multiplying rational numbers

### Porting notes
When porting this function to other proof assistants:
1. Ensure the target system has similar capabilities for working with floating-point decomposition (like `frexp`).
2. Be aware of how the target system represents rational numbers and adjust the construction accordingly.
3. The function assumes IEEE 754 double-precision floats; verify if the target system uses the same representation.
4. Consider adding tests to verify the exactness check works as expected in the new environment.

---

## ISQRT

### ISQRT
- ISQRT

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let ISQRT = new_definition
  `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`;;
```

### Informal statement
The function $\text{ISQRT}$ is defined as the integer square root function. For a natural number $n$, $\text{ISQRT}(n)$ is the unique natural number $m$ such that:

$$m^2 \leq n < (m+1)^2$$

In other words, $\text{ISQRT}(n)$ is the largest integer whose square does not exceed $n$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The integer square root function is a fundamental mathematical operation that finds the largest integer whose square does not exceed the given number. This is equivalent to taking the square root and then truncating (rounding down) to the nearest integer.

The definition uses the HOL Light choice operator (`@`) to select the unique value of $m$ satisfying the condition. This is well-defined because for any natural number $n$, there exists exactly one natural number $m$ such that $m^2 \leq n < (m+1)^2$.

This function is useful in many number-theoretic applications, particularly in algorithms involving divisors, factorization, and other computations where we need to bound values related to square roots without using floating-point approximations.

### Dependencies
#### Definitions
- `ISQRT`: The integer square root function

### Porting notes
When porting this definition to other proof assistants:
- The definition uses the choice operator (`@`). In systems without a native choice operator, you may need to define this function constructively, perhaps using recursion or as the inverse of a monotonic function.
- Alternatively, you could define it as a function that takes the largest $m$ such that $m^2 \leq n$, which is equivalent but avoids the choice operator.
- In type-theoretic proof assistants like Lean or Coq, you might want to make the domain explicit as natural numbers.

---

## ISQRT_WORKS

### Name of formal statement
ISQRT_WORKS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_WORKS = prove
 (`!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[ISQRT] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `(?m. m EXP 2 <= n) /\ (?a. !m. m EXP 2 <= n ==> m <= a)`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[num_MAX] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[ARITH_RULE `~(m + 1 <= m)`; NOT_LE]] THEN
  CONJ_TAC THENL [EXISTS_TAC `0` THEN REWRITE_TAC[ARITH; LE_0]; ALL_TAC] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  MESON_TAC[LE_SQUARE_REFL; EXP_2; LE_TRANS]);;
```

### Informal statement
For any natural number $n$, the integer square root function `ISQRT(n)` satisfies the following properties:
- $\text{ISQRT}(n)^2 \leq n$
- $n < (\text{ISQRT}(n) + 1)^2$

This theorem states that `ISQRT(n)` is indeed the greatest integer whose square does not exceed $n$.

### Informal proof
We need to prove that for any natural number $n$, the integer square root function `ISQRT(n)` satisfies $\text{ISQRT}(n)^2 \leq n$ and $n < (\text{ISQRT}(n) + 1)^2$.

The proof proceeds as follows:

1. We first use the definition of `ISQRT` which states that $\text{ISQRT}(n) = \epsilon m. m^2 \leq n \land n < (m+1)^2$, where $\epsilon$ is the choice operator.

2. To use the choice operator effectively, we need to establish that:
   - There exists at least one $m$ such that $m^2 \leq n$
   - There exists an upper bound $a$ such that for all $m$ satisfying $m^2 \leq n$, we have $m \leq a$

3. For the first condition:
   - We show that $0$ satisfies this property since $0^2 = 0 \leq n$ for any natural number $n$

4. For the second condition:
   - We choose $n$ itself as an upper bound
   - For any $m$ such that $m^2 \leq n$, we must have $m \leq n$
   - This follows from the fact that if $m > n$, then $m^2 > n^2 \geq n$ (using the properties of squares for positive numbers)

5. With these two conditions established, we can apply the choice operator's properties to conclude that the chosen value `ISQRT(n)` indeed satisfies the required properties: $\text{ISQRT}(n)^2 \leq n$ and $n < (\text{ISQRT}(n) + 1)^2$.

This completes the proof that `ISQRT(n)` works as intended.

### Mathematical insight
The integer square root function `ISQRT(n)` is the mathematical floor of the square root of $n$, also denoted as $\lfloor\sqrt{n}\rfloor$. This theorem establishes that the definition using the Hilbert choice operator correctly captures this concept by proving the two characteristic inequalities that define the integer square root.

This function is important in number theory and computational mathematics as it gives the largest integer whose square does not exceed a given number. It's used in many algorithms and has applications in areas like prime number generation and factorization.

The proof demonstrates a common pattern when using the choice operator in HOL Light: first showing existence of at least one value satisfying the property, then showing that there exists a bound on all such values, which together ensure that the choice is well-defined.

### Dependencies
**Definitions:**
- `ISQRT`: The integer square root function defined as `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`

**Theorems used in the proof:**
- `LE_0`: Basic theorem about zero being less than or equal to any natural number
- `LE_SQUARE_REFL`: If $a \leq b$ then $a^2 \leq b^2$ for natural numbers
- `LE_TRANS`: Transitivity of the less-than-or-equal relation
- `EXP_2`: Definition or theorem about the square operation
- Various arithmetic rules and properties of natural numbers

### Porting notes
When porting this theorem:
1. Ensure your system has a good representation of the choice operator (often written as ε or @ in different systems)
2. The definition of `ISQRT` using the choice operator is crucial - ensure it's correctly implemented first
3. If your target system doesn't support the choice operator directly, you may need to define `ISQRT` constructively, for example using a bounded search algorithm
4. In systems with dependent types, you might need to provide evidence that the choice is well-defined
5. The proof relies heavily on basic properties of natural numbers, squares, and ordering, which should be available in most proof assistants

---

## ISQRT_0

### Name of formal statement
ISQRT_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_0 = prove
 (`ISQRT 0 = 0`,
  MP_TAC(SPEC `0` ISQRT_WORKS) THEN
  SIMP_TAC[ARITH_RULE `x <= 0 <=> (x = 0)`; EXP_EQ_0; ARITH_EQ]);;
```

### Informal statement
The integer square root of 0 is 0, i.e., $\text{ISQRT}(0) = 0$.

### Informal proof
To prove that $\text{ISQRT}(0) = 0$, we use the theorem `ISQRT_WORKS` which states that for any natural number $n$, the integer square root $\text{ISQRT}(n)$ satisfies:
$\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n) + 1)^2$.

Applying this theorem with $n = 0$:
1. We get $\text{ISQRT}(0)^2 \leq 0 < (\text{ISQRT}(0) + 1)^2$
2. For the first inequality, since $\text{ISQRT}(0)^2 \leq 0$, and any square of a natural number is non-negative, we must have $\text{ISQRT}(0)^2 = 0$
3. A natural number squared equals 0 if and only if the number itself is 0
4. Therefore, $\text{ISQRT}(0) = 0$

The proof uses simplification with the arithmetic facts that:
- $x \leq 0 \Leftrightarrow x = 0$ for natural numbers
- $x^2 = 0 \Leftrightarrow x = 0$

### Mathematical insight
The integer square root function $\text{ISQRT}(n)$ gives the largest integer $m$ such that $m^2 \leq n$. This is a fundamental operation in computational number theory. The case $\text{ISQRT}(0) = 0$ is a boundary case that confirms the function's expected behavior for the smallest natural number input.

This result is consistent with the definition of $\text{ISQRT}$ as the unique natural number $m$ satisfying $m^2 \leq n < (m+1)^2$. For $n = 0$, we have $0^2 \leq 0 < 1^2$, which shows that $m = 0$ is the correct value.

### Dependencies
- Definitions:
  - `ISQRT`: Integer square root function defined as $\text{ISQRT}(n) = \varepsilon m. m^2 \leq n < (m+1)^2$

- Theorems:
  - `ISQRT_WORKS`: States that for all natural numbers $n$, $\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n) + 1)^2$
  - Various arithmetic lemmas used implicitly: `ARITH_RULE`, `EXP_EQ_0`, `ARITH_EQ`

---

## ISQRT_UNIQUE

### ISQRT_UNIQUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_UNIQUE = prove
 (`!m n. (ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MP_TAC (SPEC `n:num` ISQRT_WORKS) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ISQRT n) EXP 2 < (m + 1) EXP 2 /\
                m EXP 2 < (ISQRT n + 1) EXP 2`
  MP_TAC THENL
   [ASM_MESON_TAC[LT_SUC_LE; LE_SUC_LT; LET_TRANS; LTE_TRANS];
    SIMP_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC; GSYM LE_ANTISYM] THEN ARITH_TAC]);;
```

### Informal statement
For all natural numbers $m$ and $n$, we have $\textrm{ISQRT}(n) = m$ if and only if $m^2 \leq n < (m+1)^2$.

This theorem characterizes the integer square root function by the property that $\textrm{ISQRT}(n)$ is the unique integer $m$ such that $n$ lies in the half-open interval $[m^2, (m+1)^2)$.

### Informal proof
We prove the equivalence by showing both directions:

1. First direction ($\Rightarrow$): 
   - Assume $\textrm{ISQRT}(n) = m$.
   - Apply theorem `ISQRT_WORKS`, which states that $\textrm{ISQRT}(n)^2 \leq n < (\textrm{ISQRT}(n) + 1)^2$ for any $n$.
   - Substituting $\textrm{ISQRT}(n) = m$, we get $m^2 \leq n < (m+1)^2$.

2. Second direction ($\Leftarrow$):
   - Assume $m^2 \leq n < (m+1)^2$.
   - Apply `ISQRT_WORKS` again to get $\textrm{ISQRT}(n)^2 \leq n < (\textrm{ISQRT}(n) + 1)^2$.
   - From these two inequalities, we can deduce:
     * $\textrm{ISQRT}(n)^2 < (m+1)^2$ (since $\textrm{ISQRT}(n)^2 \leq n < (m+1)^2$)
     * $m^2 < (\textrm{ISQRT}(n)+1)^2$ (since $m^2 \leq n < (\textrm{ISQRT}(n)+1)^2$)
   - These inequalities, by the monotonicity of the square function, imply:
     * $\textrm{ISQRT}(n) < m+1$, which means $\textrm{ISQRT}(n) \leq m$
     * $m < \textrm{ISQRT}(n)+1$, which means $m \leq \textrm{ISQRT}(n)$
   - By antisymmetry of $\leq$, we conclude that $\textrm{ISQRT}(n) = m$.

### Mathematical insight
This theorem provides a precise characterization of the integer square root function $\textrm{ISQRT}$. It states that $\textrm{ISQRT}(n)$ is the unique integer $m$ such that $n$ lies in $[m^2, (m+1)^2)$. This is exactly how we intuitively define the integer square root - it's the largest integer whose square doesn't exceed $n$.

The result shows that the definition of `ISQRT` using the Hilbert choice operator (`@`) indeed gives us the desired mathematical object. This characterization is essential for working with integer square roots in number theory and for numerical algorithms.

### Dependencies
- **Theorems**:
  - `ISQRT_WORKS`: For any natural number $n$, $\textrm{ISQRT}(n)^2 \leq n < (\textrm{ISQRT}(n) + 1)^2$
  
- **Definitions**:
  - `ISQRT`: $\textrm{ISQRT}(n) = \epsilon m. (m^2 \leq n \wedge n < (m+1)^2)$, where $\epsilon$ denotes the Hilbert choice operator

### Porting notes
When porting this theorem:
1. Ensure your system has a way to define the integer square root function. If your system doesn't support Hilbert choice operators, you might need to define `ISQRT` constructively.
2. The proof relies on basic properties of inequalities and monotonicity of squares, which should be available in most proof assistants.
3. The antisymmetry property of $\leq$ is used in the final step, so make sure this is accessible in your target system.

---

## ISQRT_SUC

### Name of formal statement
ISQRT_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_SUC = prove
 (`!n. ISQRT(SUC n) =
       if ?m. SUC n = m EXP 2 then SUC(ISQRT n) else ISQRT n`,
  GEN_TAC THEN REWRITE_TAC[ISQRT_UNIQUE] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[ISQRT_WORKS; ARITH_RULE
     `a <= n /\ n < b /\ ~(SUC n = a) /\ ~(SUC n = b)
      ==> a <= SUC n /\ SUC n < b`]] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(CONJUNCT2(SPEC `n:num` ISQRT_WORKS)) THEN
    REWRITE_TAC[EXP_2; GSYM ADD1; MULT_CLAUSES; ADD_CLAUSES; LT_SUC] THEN
    ARITH_TAC] THEN
  POP_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `m = SUC(ISQRT n)` SUBST_ALL_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[LE_REFL]] THEN
  SUBGOAL_THEN `ISQRT(n) EXP 2 < m EXP 2 /\ m EXP 2 <= SUC(ISQRT n) EXP 2`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LE; EXP_MONO_LT; NOT_SUC] THEN
    ARITH_TAC] THEN
  MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN REWRITE_TAC[ADD1] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LT_SUC_LE; LE_SUC_LT]);;
```

### Informal statement
For any natural number $n$, the integer square root of $n+1$ is given by:
$$\text{ISQRT}(n+1) = \begin{cases}
\text{ISQRT}(n) + 1 & \text{if } \exists m \text{ such that } n+1 = m^2 \\
\text{ISQRT}(n) & \text{otherwise}
\end{cases}$$

Where $\text{ISQRT}(n)$ is the integer square root of $n$, defined as the unique integer $m$ such that $m^2 \leq n < (m+1)^2$.

### Informal proof
We'll prove the statement by cases, based on whether there exists an $m$ such that $n+1 = m^2$.

First, we rewrite the goal using `ISQRT_UNIQUE`, which states that $\text{ISQRT}(n) = m$ if and only if $m^2 \leq n < (m+1)^2$.

**Case 1:** Suppose $\exists m$ such that $n+1 = m^2$.
- We need to show that $m = \text{ISQRT}(n) + 1$.
- From `ISQRT_WORKS`, we know that $\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n) + 1)^2$.
- Since $n+1 = m^2$, we have $n < m^2$.
- Also, $m^2 = n+1 \leq (\text{ISQRT}(n) + 1)^2$.
- By the monotonicity of the square function and these inequalities, we can deduce that $\text{ISQRT}(n) < m \leq \text{ISQRT}(n) + 1$.
- Since both $m$ and $\text{ISQRT}(n) + 1$ are integers, we conclude $m = \text{ISQRT}(n) + 1$.
- Therefore, $(\text{ISQRT}(n) + 1)^2 = m^2 = n+1$.
- This satisfies the conditions for $\text{ISQRT}(n+1) = \text{ISQRT}(n) + 1$.

**Case 2:** Suppose $\nexists m$ such that $n+1 = m^2$.
- We need to show that $\text{ISQRT}(n+1) = \text{ISQRT}(n)$.
- From `ISQRT_WORKS`, we know that $\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n) + 1)^2$.
- Since there is no $m$ such that $n+1 = m^2$, we know that $n+1 \neq (\text{ISQRT}(n) + 1)^2$.
- Also, $n+1 \neq \text{ISQRT}(n)^2$ (since $\text{ISQRT}(n)^2 \leq n$).
- These conditions imply that $\text{ISQRT}(n)^2 \leq n+1 < (\text{ISQRT}(n) + 1)^2$.
- By `ISQRT_UNIQUE`, this means that $\text{ISQRT}(n+1) = \text{ISQRT}(n)$.

Thus, in both cases, the statement holds.

### Mathematical insight
This theorem provides a recursive relation for computing integer square roots. It shows that the integer square root of a number either remains the same as the previous number or increases by one, depending on whether the new number is a perfect square.

This relationship is particularly useful for algorithms that need to compute sequential integer square roots efficiently, as it avoids recomputing from scratch for each new number.

The result is intuitive when visualizing the number line: the integer square root function creates "steps" where the function value remains constant between perfect squares, then increases by one at each perfect square.

### Dependencies
- Definitions:
  - `ISQRT`: The integer square root function defined as `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`

- Theorems:
  - `ISQRT_WORKS`: Establishes that `ISQRT(n)` satisfies the defining property: `ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`
  - `ISQRT_UNIQUE`: Establishes the uniqueness of `ISQRT` values: `(ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2`

### Porting notes
When porting this theorem:
- Ensure the integer square root function is properly defined with the same properties.
- The proof relies on case analysis and manipulation of inequalities, which should be straightforward in most proof assistants.
- Pay attention to how the existence case is handled - some systems may require more explicit reasoning about the uniqueness of the integer square root.

---

## LN_2_COMPOSITION

### Name of formal statement
LN_2_COMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_2_COMPOSITION = prove
 (`ln(&2) =
   &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))`,
  CONV_TAC(GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4
        [GSYM LN_POW; GSYM LN_MUL; GSYM LN_DIV; REAL_POW_LT; real_div;
         REAL_LT_ADD; REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH]) THEN
  AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
The logarithm of 2 can be expressed as:

$$\ln(2) = 7 \ln(1 + \frac{1}{8}) - 2 \ln(1 + \frac{1}{24}) - 4 \ln(1 + \frac{1}{80})$$

where $\ln$ is the natural logarithm function.

### Informal proof
The proof works by simplifying expressions involving logarithms of products, quotients, and powers.

* First, the proof uses simplification conversions that apply the following logarithmic properties:
  - For powers: $\ln(x^n) = n\ln(x)$
  - For products: $\ln(x \cdot y) = \ln(x) + \ln(y)$ when $x,y > 0$
  - For quotients: $\ln(\frac{x}{y}) = \ln(x) - \ln(y)$ when $x,y > 0$

* The simplification also handles positivity conditions of terms, leveraging properties of real number arithmetic including addition, multiplication, and inequalities.

* Finally, after applying these logarithm transformations, the proof completes by showing equality between the resulting rational expressions using rational number reduction.

The proof essentially shows that certain combinations of logarithms of rational expressions simplify exactly to $\ln(2)$.

### Mathematical insight
This theorem provides a specific decomposition of $\ln(2)$ in terms of logarithms of expressions involving simple fractions. Such compositions are valuable for numerical approximations of $\ln(2)$, as the component logarithms may be easier to compute or approximate than $\ln(2)$ directly. This particular composition could be used in numerical algorithms for computing logarithms accurately.

The formula is likely derived from a specific continued fraction approximation or similar mathematical transformation. These types of decompositions are important for high-precision numerical calculations in computational mathematics.

### Dependencies
#### Logarithm properties
- `LN_POW`: $\ln(x^n) = n\ln(x)$ for $x > 0$
- `LN_MUL`: $\ln(xy) = \ln(x) + \ln(y)$ for $x,y > 0$  
- `LN_DIV`: $\ln(\frac{x}{y}) = \ln(x) - \ln(y)$ for $x,y > 0$

#### Real number arithmetic
- `REAL_LT_ADD`: If $x > 0$ and $y > 0$, then $x + y > 0$
- Various arithmetic conversions and simplification rules

### Porting notes
When porting this theorem:
1. Ensure the target system's logarithm function has the same properties as HOL Light's natural logarithm.
2. The proof relies heavily on automatic simplification conversions like `REAL_RAT_REDUCE_CONV`. You might need to develop similar tactics or apply manual algebraic steps in other systems.
3. Verify that the rational expressions simplify correctly in the target system, as numerical precision and rational number handling might differ between systems.

---

## LN_N_CONV

### Name of formal statement
LN_N_CONV

### Type of the formal statement
Conversion (HOL Light function that transforms a term)

### Formal Content
```ocaml
let LN_N_CONV =
  let pth = prove
   (`x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) =
          &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &1 + inv(&8)`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y +/ y // num 8 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (num 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5;;
```

### Informal statement
`LN_N_CONV` is a conversion function that evaluates the natural logarithm of rational constants. Given a term of the form `ln(r)` where `r` is a rational constant, it transforms it into an equivalent form:

$$\ln(r) = n \cdot \ln(1 + \frac{1}{8}) + \ln(1 + (r / (1 + \frac{1}{8})^n - 1))$$

where $n$ is chosen appropriately to express the rational constant.

### Informal proof
The implementation works by transforming a logarithm of a rational constant into a form that can be easily computed:

1. First, it proves an auxiliary theorem `pth` that establishes:
   $$x = (1 + \frac{1}{8})^n \cdot \frac{x}{(1 + \frac{1}{8})^n}$$
   This is proven by simple algebraic manipulation and the fact that $(1 + \frac{1}{8})^n \neq 0$.

2. Then it proves another theorem `qth` that states:
   $$\ln((1 + \frac{1}{8})^n \cdot \frac{x}{(1 + \frac{1}{8})^n}) = n \cdot \ln(1 + \frac{1}{8}) + \ln(1 + (\frac{x}{(1 + \frac{1}{8})^n} - 1))$$
   for $x > 0$. This uses the properties of logarithm:
   - $\ln(a \cdot b) = \ln(a) + \ln(b)$ from `LN_MUL`
   - $\ln(a^n) = n \cdot \ln(a)$ from `LN_POW`

3. For a given rational constant $r$, the implementation:
   - Finds an appropriate $n$ such that $(1 + \frac{1}{8})^n$ is close to but smaller than $r$
   - Applies the transformation using theorems `pth` and `qth`
   - Simplifies the resulting expression with rational arithmetic conversions

This effectively computes the logarithm by expressing it in terms of the known constant $\ln(1 + \frac{1}{8})$ and a correction term.

### Mathematical insight
This conversion provides an efficient way to compute logarithms of rational constants in HOL Light. The key insight is to express any rational number $r$ in terms of powers of a convenient base $(1 + \frac{1}{8})$, allowing the logarithm to be computed using properties of logarithms.

The approach is similar to how calculators compute logarithms: by reducing the problem to known logarithm values and applying logarithm identities. The particular choice of $(1 + \frac{1}{8})$ as the base is likely because it provides a good balance between numerical stability and computation speed.

This conversion is part of the computational infrastructure in HOL Light that allows automatic simplification of expressions involving transcendental functions with rational arguments.

### Dependencies
- **Theorems**:
  - `LN_MUL`: The logarithm of a product equals the sum of logarithms ($\ln(x \cdot y) = \ln(x) + \ln(y)$ for positive $x$ and $y$)
  - `LN_POW`: The logarithm of a power equals the power times the logarithm ($\ln(x^n) = n \cdot \ln(x)$ for positive $x$)

- **Definitions**:
  - `ln`: The natural logarithm function, defined as $\ln(x) = u$ where $\exp(u) = x$

### Porting notes
When porting this conversion to other proof assistants:

1. The approach relies on having good support for rational arithmetic evaluation, similar to HOL Light's `REAL_RAT_REDUCE_CONV`.

2. The implementation uses HOL Light's term manipulation and proof construction functions. These would need to be adapted to the target system's proof infrastructure.

3. The conversion is essentially an algorithm for computing logarithms of rational constants, which may be implemented differently in other systems that might have built-in support for numerical evaluation.

4. Theorem matching and instantiation in the target system might require different approaches than the `PART_MATCH` and `INST` used in HOL Light.

---

## LN_N2_CONV

### LN_N2_CONV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Conversion function

### Formal Content
```ocaml
let LN_N2_CONV =
  let pth = prove
   (`x = &2 pow n * (x / &2 pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln(&2 pow n * x / &2 pow n) =
          &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &2`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y */ num 2 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (num 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    let th6 = CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5 in
    let th7 = CONV_RULE (funpow 3 RAND_CONV REAL_RAT_REDUCE_CONV) th6 in
    CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV LN_N_CONV)) th7;;
```

### Informal statement
This defines a conversion function `LN_N2_CONV` that computes logarithms of rational constants by first extracting factors of $2^n$. The function works as follows:

Given a term of the form `ln(x)` where `x` is a rational constant, the conversion:
1. Determines the largest integer $n$ such that $2^n \leq x$
2. Decomposes $x$ as $x = 2^n \cdot (x/2^n)$
3. Applies logarithm properties to express $\ln(x)$ as $n \cdot \ln(2) + \ln(1 + (x/2^n - 1))$
4. Computes this expression numerically

### Informal proof
The implementation consists of a conversion function built on two key theorems:

1. First, we prove that for any real $x$ and natural number $n$:
   $x = 2^n \cdot (x/2^n)$

   This is proven by:
   - Using `REAL_RAT_REDUCE_CONV` to handle rational arithmetic
   - Taking the symmetric form
   - Applying `REAL_DIV_LMUL` which states that if $y \neq 0$ then $x = (x \cdot y)/y$
   - Using `REAL_POW_NZ` to show that $2^n \neq 0$

2. Second, we prove that for any real $x > 0$ and natural number $n$:
   $\ln(2^n \cdot x/2^n) = n \cdot \ln(2) + \ln(1 + (x/2^n - 1))$

   This is proven by:
   - Using the algebraic simplification that $1 + (x - 1) = x$
   - Applying logarithm properties:
     * `LN_MUL`: $\ln(a \cdot b) = \ln(a) + \ln(b)$ for $a,b > 0$
     * `LN_POW`: $\ln(a^n) = n \cdot \ln(a)$ for $a > 0$
   - Simplifying with facts about division and powers

The main function then:
- Takes a term of form `ln(x)` where `x` is a rational constant
- Computes the largest $n$ such that $2^n \leq x$ through the recursive `dlog` function
- Instantiates the first theorem with this $n$ to rewrite `x`
- Applies the logarithm operator to both sides
- Uses the second theorem to simplify the result
- Performs rational arithmetic simplifications
- Recursively handles remaining logarithms with `LN_N_CONV`

### Mathematical insight
This conversion provides an efficient way to compute logarithms of rational constants by exploiting the additive property of logarithms. The approach is to extract powers of 2 from the input, which simplifies the computation since $\ln(2)$ is a well-known constant. This reduces the problem to computing the logarithm of a smaller number.

The algorithm effectively implements the identity:
$\ln(x) = n\ln(2) + \ln(x/2^n)$

where $n$ is chosen to make $x/2^n$ close to 1. This is an optimization over the more basic `LN_N_CONV` which appears to work with factors of $(1 + 1/8)$ instead of powers of 2.

This approach aligns with common techniques in numerical analysis where logarithms of large numbers are computed by normalization and series expansion.

### Dependencies
- **Theorems**:
  - `LN_MUL`: $\forall x, y. 0 < x \land 0 < y \Rightarrow \ln(x \cdot y) = \ln(x) + \ln(y)$
  - `LN_POW`: $\forall n, x. 0 < x \Rightarrow \ln(x^n) = n \cdot \ln(x)$
  - `LN_N_CONV`: A conversion for computing logarithms of rational constants

- **Definitions**:
  - `ln`: $\ln x = @u. \exp(u) = x$, where $@$ is the epsilon (choice) operator

### Porting notes
When porting this conversion:
1. Ensure your system has efficient rational arithmetic and a way to extract powers of 2 from rational constants
2. The recursive approach using `dlog` may need adjustment depending on how your system handles numeric computations
3. Note that this conversion relies on `LN_N_CONV` for final simplification, so that would need to be ported first
4. In systems with different conversion/rewriting mechanisms, you'll need to adapt the pattern matching and rule application strategy

---

## FLOOR_DOUBLE_NUM

### Name of formal statement
FLOOR_DOUBLE_NUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DOUBLE_NUM = prove
 (`!n r d.
        d < 2 /\ 0 < r
        ==> &2 * floor(&n / &r) <= floor(&(2 * n + d) / &r) /\
            floor(&(2 * n + d) / &r) <= &2 * floor(&n / &r) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `floor(&n / &r) = floor((&n + &d / &2) / &r)` SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&2 * &n + &d = &2 * (&n + &d / &2)` SUBST1_TAC THENL
     [SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_MUL_ASSOC; real_div] THEN
    REWRITE_TAC[GSYM real_div; FLOOR_DOUBLE]] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  MP_TAC(SPEC `&n / &r` FLOOR) THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n / &r` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_LE_ADDR] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  UNDISCH_TAC `&n / &r < floor (&n / &r) + &1` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
  SIMP_TAC[REAL_LT_INTEGERS; FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC(REAL_ARITH `b < a ==> n + a <= c ==> n + b < c`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT; ARITH]);;
```

### Informal statement
For all natural numbers $n$, positive real numbers $r$, and real numbers $d < 2$:

$$2 \cdot \lfloor \frac{n}{r} \rfloor \leq \lfloor \frac{2n + d}{r} \rfloor \leq 2 \cdot \lfloor \frac{n}{r} \rfloor + 1$$

### Informal sketch
We need to prove the inequalities $2 \cdot \lfloor \frac{n}{r} \rfloor \leq \lfloor \frac{2n + d}{r} \rfloor \leq 2 \cdot \lfloor \frac{n}{r} \rfloor + 1$ given $d < 2$ and $0 < r$.

The key insight is proving that $\lfloor \frac{n}{r} \rfloor = \lfloor \frac{n + \frac{d}{2}}{r} \rfloor$ under these conditions. We establish this by showing that both real numbers belong to the same interval determined by the floor function.

From the properties of the floor function, we know that $\lfloor \frac{n}{r} \rfloor \leq \frac{n}{r} < \lfloor \frac{n}{r} \rfloor + 1$. To show that $\lfloor \frac{n + \frac{d}{2}}{r} \rfloor = \lfloor \frac{n}{r} \rfloor$, we need to verify:

1. $\lfloor \frac{n}{r} \rfloor \leq \frac{n + \frac{d}{2}}{r}$, which follows from combining $\lfloor \frac{n}{r} \rfloor \leq \frac{n}{r}$ with the fact that $\frac{n + \frac{d}{2}}{r} = \frac{n}{r} + \frac{d}{2r}$.

2. $\frac{n + \frac{d}{2}}{r} < \lfloor \frac{n}{r} \rfloor + 1$. Given that $\frac{n}{r} < \lfloor \frac{n}{r} \rfloor + 1$, we can multiply by $r$ to get $n < r \cdot (\lfloor \frac{n}{r} \rfloor + 1)$. Since $d < 2$, we have $\frac{d}{2} < 1$, so $n + \frac{d}{2} < r \cdot (\lfloor \frac{n}{r} \rfloor + 1) + 1$. Dividing by $r$, we get $\frac{n + \frac{d}{2}}{r} < \lfloor \frac{n}{r} \rfloor + 1 + \frac{1}{r}$. Since $\frac{1}{r} > 0$, we have $\frac{n + \frac{d}{2}}{r} < \lfloor \frac{n}{r} \rfloor + 1$.

With $\lfloor \frac{n}{r} \rfloor = \lfloor \frac{n + \frac{d}{2}}{r} \rfloor$ established, we can rewrite:
$\frac{2n + d}{r} = \frac{2(n + \frac{d}{2})}{r} = 2 \cdot \frac{n + \frac{d}{2}}{r}$

Therefore, the problem reduces to showing:
$2 \cdot \lfloor \frac{n + \frac{d}{2}}{r} \rfloor \leq \lfloor 2 \cdot \frac{n + \frac{d}{2}}{r} \rfloor \leq 2 \cdot \lfloor \frac{n + \frac{d}{2}}{r} \rfloor + 1$

This follows directly from the theorem FLOOR_DOUBLE, which states that for any real number $x$:
$2 \cdot \lfloor x \rfloor \leq \lfloor 2x \rfloor \leq 2 \cdot \lfloor x \rfloor + 1$

Applying this with $x = \frac{n + \frac{d}{2}}{r}$ and substituting $\lfloor \frac{n + \frac{d}{2}}{r} \rfloor = \lfloor \frac{n}{r} \rfloor$, we obtain the desired result.

### Mathematical insight
This theorem provides bounds on how the floor function behaves when scaling both numerator and denominator by the same factor, particularly when a small additive term is also included. It shows that doubling the numerator and adding a small value (less than 2) to it can at most increase the floor value by 1 compared to twice the floor of the original fraction.

This relationship is useful in various algorithms and mathematical analyses that involve discrete approximations of continuous values, particularly in computer science applications like digital signal processing, computer graphics, and numerical methods.

### Dependencies
- `FLOOR`: Fundamental properties of the floor function
- `FLOOR_UNIQUE`: Characterization of when a given integer equals the floor of a real number
- `FLOOR_DOUBLE`: Statement about the relationship between $\lfloor 2u \rfloor$ and $2\lfloor u \rfloor$
- `INTEGER_CLOSED`: Properties of the integer predicate, showing it's closed under various operations
- `REAL_LE_TRANS`: Transitivity of the less-than-or-equal relation on reals
- `REAL_LE_MUL`: Multiplication preserves non-negativity
- `REAL_POS`: All natural numbers are non-negative as reals
- `REAL_LT_INTEGERS`: Characterization of ordering between integers

### Porting notes
When porting this theorem to other systems:
- Ensure the floor function is properly defined with its fundamental properties
- Take care with the handling of real number arithmetic, particularly division and multiplication
- Note that the proof relies heavily on the structure of the floor function and its behavior under scaling and translation

---

## LN_FACT

### LN_FACT
- `LN_FACT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LN_FACT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. ln(&d))`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; sum; LN_1] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT; FACT_LT; LT_0] THEN
  ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[ADD_AC; REAL_ADD_AC]);;
```

### Informal statement
For any natural number $n$, the natural logarithm of $n!$ equals the sum of logarithms of integers from $1$ to $n$:

$$\ln(n!) = \sum_{d=1}^{n} \ln(d)$$

### Informal proof
The proof proceeds by induction on $n$:

**Base case**: For $n = 0$:
- We have $0! = 1$ and $\ln(1) = 0$ (by `LN_1`).
- The sum $\sum_{d=1}^{0} \ln(d)$ is an empty sum, which equals $0$.
- Therefore, $\ln(0!) = \ln(1) = 0 = \sum_{d=1}^{0} \ln(d)$.

**Inductive step**: Assume the statement holds for some $n$, i.e., $\ln(n!) = \sum_{d=1}^{n} \ln(d)$.
- For $n+1$, we have $(n+1)! = (n+1) \cdot n!$
- Taking the logarithm: $\ln((n+1)!) = \ln((n+1) \cdot n!)$
- Using the logarithm property for products (`LN_MUL`): $\ln((n+1) \cdot n!) = \ln(n+1) + \ln(n!)$
  - Note: `LN_MUL` requires both arguments to be positive, which is satisfied because $n+1 > 0$ and $n! > 0$ for all natural numbers.
- By the induction hypothesis: $\ln((n+1)!) = \ln(n+1) + \sum_{d=1}^{n} \ln(d)$
- This simplifies to: $\ln((n+1)!) = \sum_{d=1}^{n+1} \ln(d)$

The algebraic manipulations at the end (`REWRITE_TAC[ADD_AC; REAL_ADD_AC]`) handle the associativity and commutativity of addition to ensure that the resulting expression matches the required form.

### Mathematical insight
This theorem establishes a fundamental relationship between factorials and logarithms, showing that the logarithm of a factorial decomposes into a sum of logarithms. This result is useful in many mathematical contexts, particularly:

1. In asymptotic analysis, this leads to Stirling's approximation for factorials.
2. In probability theory and statistical mechanics, where log-factorials appear frequently.
3. In computational number theory, where calculating ln(n!) directly can be more efficiently done by summing logarithms.

The theorem highlights the logarithm's property of transforming products into sums, making many complex calculations more tractable.

### Dependencies
- Theorems:
  - `sum`: Recursive definition of finite summation
  - `LN_MUL`: Logarithm of a product equals sum of logarithms
  - `LN_1`: Logarithm of 1 equals 0
- Definitions:
  - `ln`: Natural logarithm defined as the inverse of the exponential function

### Porting notes
When porting this proof:
1. Ensure your target system has appropriate definitions of factorial, natural logarithm, and finite summation with similar properties.
2. The proof relies on induction over natural numbers, which should be straightforward in most systems.
3. Pay attention to how numerical values are represented (e.g., natural numbers vs. reals) and how type coercions are handled.
4. The use of `REWRITE_TAC[ADD_AC; REAL_ADD_AC]` indicates associativity and commutativity properties of addition might need explicit handling in some systems with less automatic reasoning.

---

## LN_FACT_BOUNDS

### Name of formal statement
LN_FACT_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_FACT_BOUNDS = prove
 (`!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)`,
  SUBGOAL_THEN
   `!n. ~(n = 0)
        ==> ?z. &n < z /\ z < &(n + 1) /\
                (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(z) + &1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`\x. x * ln(x)`; `\x. ln(x) + &1`; `&n`; `&(n + 1)`]
                 MVT_ALT) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(n + &1) - n = &1`] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real` (DIFF_CONV `\x. x * ln(x)`)) THEN
    SIMP_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num->real`) THEN
  SUBGOAL_THEN
   `!n. &(n + 1) * ln(&(n + 1)) = sum(1,n) (\i. ln(k i) + &1)`
  MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    REWRITE_TAC[sum; ADD_CLAUSES; LN_1; REAL_MUL_RZERO] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`;
                ARITH_RULE `SUC(n + 1) = n + 2`] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[REAL_ARITH `(a - b = c) <=> (a = b + c)`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_AC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD] THEN
  CONV_TAC(LAND_CONV(BINDER_CONV(RAND_CONV(RAND_CONV(LAND_CONV
    (LAND_CONV num_CONV)))))) THEN
  REWRITE_TAC[ADD1; SUM_REINDEX; SUM_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a = b + c * &1) <=> (b = a - c)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. abs(sum(1,n+1) (\i. ln(&i)) - (&(n + 1) * ln (&(n + 1)) - &(n + 1)))
        <= &1 + ln(&(n + 1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV)
     [GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x - (y - z)) <= a ==> abs(x - (y - (z + &1))) <= &1 + a`) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM th]) THEN
    SUBGOAL_THEN
     `sum(1,n + 1) (\i. ln (&i)) = sum(1,n) (\i. ln(&(i + 1)))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [SUM_DIFF] THEN
      REWRITE_TAC[SUM_1; ADD_CLAUSES; LN_1; REAL_SUB_RZERO] THEN
      GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM(NUM_REDUCE_CONV `0 + 1`)] THEN
      REWRITE_TAC[SUM_REINDEX] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\n. abs(ln(&(n + 1)) - ln(k n)))` THEN
    REWRITE_TAC[ABS_SUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\i. ln(&(i + 1)) - ln(&i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a < b /\ b < c ==> abs(c - b) <= c - a`) THEN
      SUBGOAL_THEN `&0 < &r /\ &r < k r /\ k r < &(r + 1)` MP_TAC THENL
       [ALL_TAC; MESON_TAC[LN_MONO_LT; REAL_LT_TRANS]] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < r <=> 1 <= r`;
                   ARITH_RULE `~(r = 0) <=> 1 <= r`];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SUB] THEN
    REWRITE_TAC[GSYM(SPECL [`f:num->real`; `m:num`; `1`] SUM_REINDEX)] THEN
    ONCE_REWRITE_TAC[SUM_DIFF] THEN
    REWRITE_TAC[ARITH; SUM_2; SUM_1; LN_1; REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 + n = SUC(1 + n)`] THEN
    REWRITE_TAC[sum; ADD_CLAUSES] THEN
    REWRITE_TAC[ADD_AC] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - c - (a - c) = b`; REAL_LE_REFL];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_REWRITE_TAC[ADD1; LN_FACT]);;
```

### Informal statement
For any non-zero natural number $n$, the approximation of $\ln(n!)$ by $n\ln(n) - n$ has a bounded error:

$$\forall n.\ n \neq 0 \implies |\ln(n!) - (n\ln(n) - n)| \leq 1 + \ln(n)$$

This provides bounds on how well Stirling's approximation (without the $\sqrt{2\pi n}$ term) approximates the logarithm of the factorial function.

### Informal proof
The proof establishes bounds on the approximation of $\ln(n!)$ by $n\ln(n) - n$ through several steps:

1. First, we prove a key intermediate result: for any non-zero $n$, there exists a real number $z$ such that $n < z < n+1$ and $(n+1)\ln(n+1) - n\ln(n) = \ln(z) + 1$. This is established by:
   * Applying the Mean Value Theorem to the function $f(x) = x\ln(x)$ on the interval $[n, n+1]$
   * Showing that the derivative of this function is $f'(x) = \ln(x) + 1$
   * Therefore, there exists $z$ with $n < z < n+1$ such that $f(n+1) - f(n) = (n+1 - n)f'(z) = \ln(z) + 1$

2. By induction, we prove that:
   $$(n+1)\ln(n+1) = \sum_{i=1}^n (\ln(k_i) + 1)$$
   where $k_i$ are the values from the first step with $n < k_i < n+1$ for each $i$.

3. Using the sum relationship and properties of logarithms:
   * We decompose the sum into $\sum_{i=1}^n \ln(k_i) + \sum_{i=1}^n 1$
   * The second sum is simply $n$
   * We then establish that $|\sum_{i=1}^n \ln(i+1) - \sum_{i=1}^n \ln(k_i)| \leq \sum_{i=1}^n |\ln(i+1) - \ln(k_i)|$
   * Since $i < k_i < i+1$ and $\ln$ is monotonic, $\ln(i) < \ln(k_i) < \ln(i+1)$
   * This gives $|\ln(i+1) - \ln(k_i)| \leq \ln(i+1) - \ln(i)$

4. The bound on the telescope sum $\sum_{i=1}^n (\ln(i+1) - \ln(i)) = \ln(n+1) - \ln(1) = \ln(n+1)$ yields our final result:
   $$|\ln((n+1)!) - ((n+1)\ln(n+1) - (n+1))| \leq 1 + \ln(n+1)$$

5. By shifting the index (replacing $n+1$ with $n$), we obtain the desired conclusion:
   $$|\ln(n!) - (n\ln(n) - n)| \leq 1 + \ln(n)$$

### Mathematical insight
This theorem provides a tight error bound on a simplified form of Stirling's approximation for the factorial function. Specifically, it bounds the error when approximating $\ln(n!)$ by $n\ln(n) - n$, showing that the error grows no faster than $1 + \ln(n)$.

The complete Stirling's approximation includes an additional $\frac{1}{2}\ln(2\pi n)$ term and gives an even closer approximation to $\ln(n!)$, but this theorem focuses on the primary terms.

This result is important in probability theory, statistical mechanics, and computational complexity, where accurate approximations of large factorials are needed. The bound is also tight enough for many asymptotic analyses.

The proof technique using the Mean Value Theorem to establish a relationship between consecutive terms is elegant and demonstrates how calculus can be applied to derive bounds on discrete functions.

### Dependencies
- Theorems:
  - `REAL_MUL_RID`: $\forall x.\ x \cdot 1 = x$
  - `REAL_MUL_RZERO`: $\forall x.\ x \cdot 0 = 0$
  - `REAL_LE_REFL`: $\forall x.\ x \leq x$
  - `REAL_LTE_TRANS`: $\forall x\ y\ z.\ x < y \land y \leq z \implies x < z$
  - `REAL_LE_TRANS`: $\forall x\ y\ z.\ x \leq y \land y \leq z \implies x \leq z$
  - `REAL_SUB_RZERO`: $\forall x.\ x - 0 = x$
  - `REAL_LT_IMP_NZ`: $\forall x.\ 0 < x \implies \lnot(x = 0)$
  - `sum`: Basic properties of finite summation
  - `SUM_DIFF`: $\forall f\ m\ n.\ \sum_{i=m}^{n+m-1} f(i) = \sum_{i=0}^{m+n-1} f(i) - \sum_{i=0}^{m-1} f(i)$
  - `ABS_SUM`: $\forall f\ m\ n.\ |\sum_{i=m}^{n+m-1} f(i)| \leq \sum_{i=m}^{n+m-1} |f(i)|$
  - `SUM_LE`: Sum monotonicity
  - `SUM_ADD`, `SUM_SUB`: Linearity of summation
  - `SUM_REINDEX`: Summation reindexing
  - `SUM_CONST`: Sum of constants
  - `MVT_ALT`: Mean Value Theorem (alternative form)
  - `LN_1`: $\ln(1) = 0$
  - `LN_MONO_LT`: Monotonicity of logarithm
  - `LN_FACT`: $\forall n.\ \ln(n!) = \sum_{d=1}^n \ln(d)$

- Definitions:
  - `ln`: Natural logarithm

### Porting notes
When porting this theorem:
1. Ensure that your system has a well-defined natural logarithm function with the appropriate properties.
2. The proof heavily relies on the Mean Value Theorem and properties of the logarithm function, so these should be available.
3. The handling of summations may vary between systems - ensure that your system's sum notation correctly handles the indexing as used here.
4. The argument uses a mixture of real and natural numbers, so attention should be paid to coercion between types (like `&n` in HOL Light for converting naturals to reals).
5. The final step of the proof uses induction on the natural number, which is standard in most systems but might require different tactics.

---

## primepow

### Name of formal statement
primepow

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let primepow = new_definition
  `primepow q <=> ?p k. 1 <= k /\ prime p /\ (q = p EXP k)`;;
```

### Informal statement
A positive integer $q$ is a prime power if and only if there exists a prime number $p$ and a positive integer $k \geq 1$ such that $q = p^k$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition captures the concept of a prime power, which is a fundamental concept in number theory. A prime power is simply a natural number that can be expressed as a prime raised to a positive integer power. This includes prime numbers themselves (when $k=1$).

Prime powers are important in many number-theoretic contexts:
- They are the building blocks in the prime factorization of integers
- They appear in various counting formulas and arithmetic functions
- They are relevant in group theory and related algebraic structures
- They play a role in many number-theoretic algorithms and proofs

This definition is useful for theorems that distinguish between general integers and those that are powers of a single prime.

### Dependencies
#### Definitions
- `primepow`: The definition itself
- `prime`: (implicit) The predicate indicating that a number is prime
- `EXP`: (implicit) The exponentiation operation

### Porting notes
When porting this definition to other proof assistants:
- Ensure that the system has appropriate definitions for prime numbers and exponentiation
- Consider whether the target system requires explicit type annotations
- Note that this definition allows any natural number type that supports the concepts of primality and exponentiation

---

## aprimedivisor

### Name of formal statement
aprimedivisor

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let aprimedivisor = new_definition
  `aprimedivisor q = @p. prime p /\ p divides q`;;
```

### Informal statement
For any natural number $q$, $\text{aprimedivisor}(q)$ is defined as a prime number $p$ such that $p$ divides $q$. More precisely, it is defined using the Hilbert choice operator as:

$$\text{aprimedivisor}(q) = \varepsilon p. \text{prime}(p) \land p \text{ divides } q$$

where $\varepsilon$ represents the choice operator that selects an arbitrary prime divisor of $q$.

### Informal proof
No proof is required as this is a definition.

### Mathematical insight
This definition introduces a function that selects a prime divisor for any natural number. For prime numbers, it will return the number itself. For composite numbers, it will return one of the prime factors. 

The definition uses the Hilbert choice operator (`@` in HOL Light), which means that for numbers with multiple prime divisors, the function will return a deterministic but not necessarily specified prime divisor. This is useful in number theory when we need to argue about the existence of prime divisors without specifying which one.

If $q = 1$ or $q = 0$, the choice is made over an empty set, as no prime divides 1, and technically the definition would not be well-behaved. In practical applications, this function would typically be used with appropriate preconditions to ensure it is applied only to numbers greater than 1.

### Dependencies
#### Definitions
- `aprimedivisor`

### Porting notes
When porting to other proof assistants:
1. Be aware that systems handle the choice operator differently:
   - In some systems like Isabelle/HOL, the definition would be similar
   - In constructive systems like Coq, a choice operator might not be available directly
   - In Lean, you would use `Classical.choose` or a similar construct

2. You might want to add explicit conditions on $q$ (such as $q > 1$) to ensure the choice is made over a non-empty set.

3. Consider whether you need this exact definition with the choice operator, or if an existential version would be more appropriate for your application.

---

## PRIMEPOW_GE_2

### Name of formal statement
PRIMEPOW_GE_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_GE_2 = prove
 (`!q. primepow q ==> 2 <= q`,
  REWRITE_TAC[primepow; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `p:num`; `k:num`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p:num` THEN
  ASM_SIMP_TAC[PRIME_GE_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);;
```

### Informal statement
For all natural numbers $q$, if $q$ is a prime power (i.e., $q = p^k$ for some prime $p$ and integer $k \geq 1$), then $q \geq 2$.

### Informal proof
We need to prove that if $q$ is a prime power, then $q \geq 2$.

- First, we unfold the definition of `primepow` and move the existential quantifiers outside the implication.
- Let $q$, $p$, and $k$ be natural numbers such that $k \geq 1$, $p$ is prime, and $q = p^k$.
- To prove $q \geq 2$, we use transitivity of $\leq$ with $p$ as the intermediate value:
  - We know $p \geq 2$ by `PRIME_GE_2` (which states that any prime number is at least 2).
  - We need to show $p \leq p^k$, which follows from the fact that $k \geq 1$.
  - Specifically, we rewrite $p$ as $p^1$ and use the property that $a^m \leq a^n$ when $1 \leq a$ and $m \leq n$.
  - Since $p \geq 2 > 1$ and $1 \leq k$ (from our assumptions), we have $p = p^1 \leq p^k = q$.
- By transitivity, we conclude $2 \leq p \leq q$, therefore $2 \leq q$.

### Mathematical insight
This theorem establishes a fundamental property of prime powers: they are always at least 2. This follows naturally from two basic facts: (1) primes are at least 2, and (2) taking a prime to a power $k \geq 1$ cannot decrease its value. 

This result is important for various number-theoretic applications where prime powers are considered, ensuring that we're always dealing with numbers greater than or equal to 2, which simplifies many arguments by excluding the edge cases of 0 and 1.

### Dependencies
#### Theorems
- `PRIME_GE_2`: For all primes $p$, $2 \leq p$

#### Definitions
- `primepow`: A natural number $q$ is a prime power if there exists a prime number $p$ and a natural number $k \geq 1$ such that $q = p^k$

### Porting notes
When porting this theorem:
- Ensure your system has the correct definition of prime powers that explicitly requires the exponent to be at least 1 (some systems might define prime powers differently).
- The proof is straightforward and should translate easily to most proof assistants with basic arithmetic reasoning.
- The transitivity argument and manipulation of exponents are standard techniques available in most theorem provers.

---

## PRIMEPOW_0

### Name of formal statement
PRIMEPOW_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_0 = prove
 (`~(primepow 0)`,
  MESON_TAC[NUM_REDUCE_CONV `2 <= 0`; PRIMEPOW_GE_2]);;
```

### Informal statement
Zero is not a prime power.

Formally: $\neg(\text{primepow}(0))$, where $\text{primepow}(q)$ means that $q$ is a prime power, i.e., $q = p^k$ for some prime number $p$ and integer $k \geq 1$.

### Informal proof
We prove this by contradiction using the theorem `PRIMEPOW_GE_2`.

If $0$ were a prime power, then by `PRIMEPOW_GE_2`, we would have $2 \leq 0$. However, this is false (as verified by the numerical computation `NUM_REDUCE_CONV `2 <= 0``). This contradiction shows that $0$ cannot be a prime power.

### Mathematical insight
This theorem establishes one of the basic properties of prime powers: zero is not a prime power. This is consistent with the definition of prime powers as $p^k$ where $p$ is prime and $k \geq 1$, since any prime $p$ satisfies $p \geq 2$ and therefore $p^k \geq 2$ for any $k \geq 1$.

The result is part of the foundational properties of prime powers used in number theory and helps establish the range of the primepow predicate.

### Dependencies
- Theorems:
  - `PRIMEPOW_GE_2`: If $q$ is a prime power, then $q \geq 2$.
- Definitions:
  - `primepow`: Defines what it means for a number to be a prime power ($q = p^k$ where $p$ is prime and $k \geq 1$).

### Porting notes
This theorem should be straightforward to port to other systems. The proof relies on a simple contradiction between the property that prime powers are at least 2 and the fact that 0 < 2.

---

## APRIMEDIVISOR_PRIMEPOW

### Name of formal statement
APRIMEDIVISOR_PRIMEPOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let APRIMEDIVISOR_PRIMEPOW = prove
 (`!p k. prime p /\ 1 <= k ==> (aprimedivisor(p EXP k) = p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `1 <= k ==> (k = SUC(k - 1))`)) THEN
  REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; PRIME_DIVEXP; PRIME_DIVPROD;
                prime; PRIME_1]);;
```

### Informal statement
For any prime number $p$ and any natural number $k \geq 1$, the function `aprimedivisor` applied to $p^k$ returns $p$ itself. 

That is, $\text{aprimedivisor}(p^k) = p$ for any prime $p$ and $k \geq 1$.

Here, `aprimedivisor` is a function that returns some prime divisor of its argument.

### Informal proof
We need to prove that for prime $p$ and $k \geq 1$, $\text{aprimedivisor}(p^k) = p$.

- First, we expand the definition of `aprimedivisor` which is defined as $\text{aprimedivisor}(q) = \varepsilon p. \text{prime}(p) \land p \text{ divides } q$, where $\varepsilon$ is the selection operator (Hilbert's epsilon) that selects a value satisfying the given predicate.

- To prove that $\text{aprimedivisor}(p^k) = p$, we need to show that $p$ is the unique prime divisor of $p^k$.

- Since $k \geq 1$, we can rewrite $k$ as $\text{SUC}(k-1)$.

- This gives us $p^k = p^{\text{SUC}(k-1)} = p \cdot p^{k-1}$

- Now, we know that:
  * $p$ is prime (given)
  * $p$ divides $p^k$ (by `DIVIDES_REFL` and `DIVIDES_RMUL`)
  
- If any other prime $q$ divides $p^k = p \cdot p^{k-1}$, then by `PRIME_DIVPROD`, either $q$ divides $p$ or $q$ divides $p^{k-1}$.

- If $q$ divides $p$ and both are prime, then $q = p$ (by the definition of prime numbers).

- If $q$ divides $p^{k-1}$, then by `PRIME_DIVEXP`, $q$ divides $p$, which again means $q = p$.

- Therefore, $p$ is the unique prime divisor of $p^k$, which means $\text{aprimedivisor}(p^k) = p$.

### Mathematical insight
This theorem establishes that for any prime power $p^k$ (with $k \geq 1$), the function `aprimedivisor` correctly identifies the prime factor $p$. This is intuitive since a prime power has only one prime divisor.

The result is important because it confirms that the `aprimedivisor` function behaves as expected on prime powers, which are fundamental building blocks in number theory. This function can be used as part of algorithms that need to find prime factors of composite numbers.

The proof relies on the uniqueness of prime factorization, a fundamental result in number theory.

### Dependencies
**Theorems:**
- `DIVIDES_REFL`: For any number $x$, $x$ divides itself.
- `DIVIDES_RMUL`: If $d$ divides $a$, then $d$ also divides $a \cdot x$ for any $x$.
- `PRIME_1`: 1 is not a prime number.
- `PRIME_DIVPROD`: If a prime $p$ divides a product $a \cdot b$, then either $p$ divides $a$ or $p$ divides $b$.
- `PRIME_DIVEXP`: If a prime $p$ divides $x^n$, then $p$ divides $x$.

**Definitions:**
- `aprimedivisor`: A function that returns some prime divisor of its argument, defined as $\text{aprimedivisor}(q) = \varepsilon p. \text{prime}(p) \land p \text{ divides } q$.

### Porting notes
When porting this theorem to other proof assistants:
1. The definition of `aprimedivisor` uses the epsilon operator (indefinite description), which may not be available in all proof assistants. In systems like Lean or Coq, you might need to use a different approach, such as defining it as a function that returns the smallest prime divisor.
2. The proof relies on the uniqueness of the selected prime divisor, which might require additional work in systems without direct support for the `SELECT_UNIQUE` theorem.
3. The arithmetic reasoning in HOL Light is handled by `ARITH_RULE`, which might need to be replaced with appropriate tactics in the target system.

---

## APRIMEDIVISOR

### Name of formal statement
APRIMEDIVISOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let APRIMEDIVISOR = prove
 (`!n. ~(n = 1) ==> prime(aprimedivisor n) /\ (aprimedivisor n) divides n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  CONV_TAC SELECT_CONV THEN ASM_SIMP_TAC[PRIME_FACTOR]);;
```

### Informal statement
For any natural number $n$ where $n \neq 1$, the function $\text{aprimedivisor}(n)$ returns a prime number that divides $n$. More precisely:

$$\forall n. n \neq 1 \implies \text{prime}(\text{aprimedivisor}(n)) \land \text{aprimedivisor}(n) \mid n$$

where $\text{aprimedivisor}(n)$ is defined as $\text{aprimedivisor}(n) = \epsilon p.\, \text{prime}(p) \land p \mid n$, with $\epsilon$ being the choice operator that selects a prime divisor of $n$.

### Informal proof
We need to prove that for any $n \neq 1$, the function $\text{aprimedivisor}(n)$ returns a prime number that divides $n$.

1. Start with an arbitrary natural number $n$ where $n \neq 1$.
2. The function $\text{aprimedivisor}(n)$ is defined using the choice operator as $\text{aprimedivisor}(n) = \epsilon p.\, \text{prime}(p) \land p \mid n$.
3. To show that this choice operator returns a valid result, we need to establish that there exists at least one prime $p$ that divides $n$.
4. This existence is provided by the theorem `PRIME_FACTOR`, which states that every natural number greater than 1 has a prime factor.
5. Since we know $n \neq 1$, `PRIME_FACTOR` guarantees that there exists a prime $p$ such that $p \mid n$.
6. Therefore, $\text{aprimedivisor}(n)$ selects a prime number that divides $n$, completing the proof.

### Mathematical insight
This theorem establishes a function that deterministically selects a prime divisor for any number greater than 1. The choice is made using Hilbert's epsilon operator, which provides a way to select a representative element satisfying a given property when such elements exist.

The function $\text{aprimedivisor}$ is particularly useful for algorithms and proofs that need to work with prime factors. Rather than just knowing that prime factors exist (as established by the `PRIME_FACTOR` theorem), this function provides a specific prime factor that can be used in further computations or proofs.

The theorem essentially moves from an existential statement "there exists a prime divisor" to a constructive one "here is a specific prime divisor", which is often necessary in formal mathematics.

### Dependencies
#### Theorems
- `PRIME_FACTOR`: For any natural number $n \neq 1$, there exists a prime number $p$ such that $p$ divides $n$.

#### Definitions
- `aprimedivisor`: Defined as $\text{aprimedivisor}(q) = \epsilon p.\, \text{prime}(p) \land p \mid q$, where $\epsilon$ is Hilbert's choice operator.

### Porting notes
When porting this to other proof assistants, note that:

1. The theorem relies on Hilbert's choice operator (the $\epsilon$ operator), which may be handled differently in other systems. In systems without built-in choice operators, you might need to use axioms of choice or define an explicit function that returns a prime divisor.

2. The proof is straightforward once you have established the `PRIME_FACTOR` theorem, which shows the existence of prime divisors for any number greater than 1.

3. In constructive systems, you would need to actually compute a prime divisor rather than abstractly selecting one with a choice operator.

---

## BIG_POWER_LEMMA

### Name of formal statement
BIG_POWER_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIG_POWER_LEMMA = prove
 (`!m n. 2 <= m ==> ?k. n <= m EXP k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP (SUC n)` THEN
  ASM_REWRITE_TAC[EXP_MONO_LE; NOT_SUC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; ARITH] THEN
  UNDISCH_TAC `n <= 2 EXP SUC n` THEN REWRITE_TAC[EXP] THEN
  MP_TAC(SPECL [`2:num`; `n:num`] EXP_EQ_0) THEN
  REWRITE_TAC[ARITH] THEN SPEC_TAC(`2 EXP n`,`m:num`) THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $m$ and $n$, if $m \geq 2$, then there exists a natural number $k$ such that $n \leq m^k$.

### Informal proof
The proof demonstrates that for any $m \geq 2$ and any $n$, there exists a power of $m$ that is greater than or equal to $n$.

- We start by fixing arbitrary $m$ and $n$ with the assumption that $m \geq 2$.
- We claim that $k = n+1$ gives us the desired power.
- We need to show that $n \leq m^{n+1}$.
- To prove this, we use transitivity of $\leq$ by showing that $n \leq 2^{n+1} \leq m^{n+1}$.
  - For the second inequality: Since $m \geq 2$, we have $2^{n+1} \leq m^{n+1}$ by monotonicity of exponentiation.
  - For the first inequality: We prove $n \leq 2^{n+1}$ by induction on $n$.
    - Base case ($n = 0$): We need to show $0 \leq 2^1 = 2$, which is trivial.
    - Induction step: Assume $n \leq 2^{n+1}$. We need to show $(n+1) \leq 2^{(n+1)+1} = 2^{n+2} = 2 \cdot 2^{n+1}$.
      - From the induction hypothesis, we have $n \leq 2^{n+1}$.
      - Since $2^{n+1} \geq 1$ (as $2^a > 0$ for any $a$), we have $2 \cdot 2^{n+1} \geq 2 \cdot 1 = 2 > 1$.
      - Therefore, $2 \cdot 2^{n+1} \geq n + 1$.
- This completes the proof that $n \leq m^{n+1}$.

### Mathematical insight
This lemma establishes a fundamental property of exponential growth: powers of any number greater than or equal to 2 will eventually exceed any given number. This is a basic observation used in complexity theory, number theory, and other areas of mathematics when discussing the asymptotic behavior of functions.

The proof uses the fact that exponential growth outpaces linear growth, specifically showing that $2^{n+1} \geq n$ for all $n$, and that larger bases grow even faster.

### Dependencies
- `EXP_MONO_LE`: If $a \leq b$ and $c \geq 1$, then $c^a \leq c^b$
- `NOT_SUC`: Negation property related to successor function
- `EXP`: Definition or basic properties of exponentiation
- `EXP_EQ_0`: Characterizes when $a^b = 0$
- `ARITH_TAC`: Tactical for solving basic arithmetic goals
- `LE_TRANS`: Transitivity of less than or equal to relation

### Porting notes
When porting this theorem:
- Make sure the exponentiation operation is defined in the target system
- Most of the proof relies on basic properties of natural numbers and exponentiation
- The basic structure of proving a bound on $2^{n+1}$ and then using transitivity should transfer to most systems
- The final arithmetic reasoning may need to be reconstructed with the target system's arithmetic automation

---

## PRIME_PRIMEPOW

### PRIME_PRIMEPOW
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PRIME_PRIMEPOW = prove
 (`!p. prime p ==> primepow p`,
  MESON_TAC[prime; primepow; LE_REFL; EXP_1]);;
```

### Informal statement
For any number $p$, if $p$ is a prime number, then $p$ is a prime power.

### Informal proof
This theorem follows immediately from the definitions of prime and prime power.

Let $p$ be a prime number. By definition, a prime power is a number $q$ such that $q = p^k$ where $p$ is prime and $k \geq 1$ is a natural number.

We can express $p$ as $p^1$. Since $p$ is prime and $1 \geq 1$ (by reflexivity of the $\leq$ relation), $p$ satisfies the definition of a prime power.

The proof uses:
- The definition of `prime`
- The definition of `primepow`
- The reflexivity of the $\leq$ relation (`LE_REFL`)
- The fact that $p^1 = p$ (`EXP_1`)

### Mathematical insight
This theorem establishes the basic fact that prime numbers are a special case of prime powers (specifically, they are prime powers with exponent 1). This connection is important for many number-theoretic results where properties of primes are extended to prime powers.

The result follows directly from the definitions and provides a foundation for working with prime powers in more complex contexts.

### Dependencies
- **Definitions**: `prime`, `primepow`
- **Theorems**: `LE_REFL`, `EXP_1`

---

## rec

### bezout

### Type of the formal statement
- Definition

### Formal Content
```ocaml
let rec bezout (m,n) =
  if m =/ num 0 then (num 0,num 1) else if n =/ num 0 then (num 1,num 0)
  else if m <=/ n then
    let q = quo_num n m and r = mod_num n m in
    let (x,y) = bezout(m,r) in
    (x -/ q */ y,y)
  else let (x,y) = bezout(n,m) in (y,x);;
```

### Informal statement
The `bezout` function computes Bézout coefficients for two natural numbers $m$ and $n$. It returns a pair of integers $(x, y)$ such that $xm + yn = \gcd(m, n)$, where $\gcd(m, n)$ is the greatest common divisor of $m$ and $n$.

The function is defined recursively as follows:
- If $m = 0$, then $(x, y) = (0, 1)$ 
- If $n = 0$, then $(x, y) = (1, 0)$
- If $m \leq n$, let $q = \lfloor n/m \rfloor$ (integer quotient) and $r = n \bmod m$ (remainder), then compute $(x', y') = \text{bezout}(m, r)$ and return $(x' - qy', y')$
- Otherwise (if $m > n$), compute $(x', y') = \text{bezout}(n, m)$ and return $(y', x')$

### Informal proof
This is a definition, not a theorem, so there is no proof to present. However, the correctness of this definition can be established by showing that if $x'm + y'r = \gcd(m, r)$ and $r = n - qm$, then $(x' - qy')m + y'n = \gcd(m, n)$.

### Mathematical insight
The Bézout identity states that if $m$ and $n$ are integers, not both zero, then there exist integers $x$ and $y$ such that $xm + yn = \gcd(m, n)$. This function computes these Bézout coefficients using the extended Euclidean algorithm.

The algorithm works by recursive application of the division algorithm. When we have $n = qm + r$ with $r < m$, we know that $\gcd(m, n) = \gcd(m, r)$. If we find coefficients $x'$ and $y'$ such that $x'm + y'r = \gcd(m, r)$, we can substitute $r = n - qm$ to get $x'm + y'(n - qm) = \gcd(m, n)$, which simplifies to $(x' - qy')m + y'n = \gcd(m, n)$. This gives us our Bézout coefficients $(x, y) = (x' - qy', y')$.

The base cases handle scenarios when either input is zero: if $m = 0$, then $\gcd(0, n) = n$, and $0 \cdot 0 + 1 \cdot n = n$; if $n = 0$, then $\gcd(m, 0) = m$, and $1 \cdot m + 0 \cdot 0 = m$.

This algorithm is an essential tool in number theory and has applications in solving Diophantine equations, computing modular inverses, and constructing continued fractions.

### Dependencies
None explicitly mentioned, but the implementation uses:
- `num` type and operations
- `quo_num` (quotient function for numbers)
- `mod_num` (modulus function for numbers)
- Arithmetic operations (`=/, <=/, -/, */`)

### Porting notes
When porting this function:
1. Be aware of the representation of natural numbers in the target system
2. Ensure the quotient (`quo_num`) and modulus (`mod_num`) operations behave as expected
3. Note that this implementation assumes non-negative integer inputs and may need adjustment for handling signed integers
4. The recursive algorithm terminates because the second argument decreases at each step until reaching zero

---

## PRIMEPOW_CONV

### Name of formal statement
PRIMEPOW_CONV

### Type of the formal statement
A conversion function (ML function that produces theorems)

### Formal Content
```ocaml
let PRIMEPOW_CONV =
  let pth0 = prove
   (`primepow 0 <=> F`,
    REWRITE_TAC[primepow] THEN MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`primepow 1 <=> F`,
    REWRITE_TAC[primepow] THEN
    MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (primepow q <=> T)`,
    MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (primepow q <=> F)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and primepow_tm = `primepow` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> primepow_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then pth0
    else if q =/ num 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in PRIMEPOW_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ num 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;
```

### Informal statement
`PRIMEPOW_CONV` is a conversion function that determines whether a natural number is a prime power. Specifically, it evaluates expressions of the form `primepow n` where `n` is a numeral (concrete natural number), returning either `primepow n <=> T` or `primepow n <=> F` depending on whether `n` is a prime power or not.

A natural number is a prime power if it can be represented as $p^k$ where $p$ is a prime number and $k \geq 1$ is a natural number.

### Informal proof
The conversion uses four key theorems as building blocks:

1. **For zero**: $\text{primepow}(0) \Leftrightarrow \text{False}$
   - Proof: By the definition of `primepow`, we need a prime $p$ and $k \geq 1$ such that $0 = p^k$.
   - This is impossible because $p^k > 0$ for any prime $p$ and positive $k$.
   - Uses facts that $0$ is not prime and $p^k = 0$ implies $p = 0$.

2. **For one**: $\text{primepow}(1) \Leftrightarrow \text{False}$
   - Proof: By definition of `primepow`, we need a prime $p$ and $k \geq 1$ such that $1 = p^k$.
   - This is impossible because $p^k = 1$ implies either $p = 1$ (which is not prime) or $k = 0$ (which contradicts $k \geq 1$).

3. **For actual prime powers**: $\text{prime}(p) \Rightarrow 1 \leq k \land q = p^k \Rightarrow (\text{primepow}(q) \Leftrightarrow \text{True})$
   - Proof: This follows directly from the definition of `primepow`.

4. **For composite numbers**: If $(p \cdot x = r \cdot y + 1) \land (p \neq 1) \land (r \neq 1) \land (q = p \cdot r \cdot d) \Rightarrow (\text{primepow}(q) \Leftrightarrow \text{False})$
   - Proof:
     - Assume $q$ is a prime power, i.e., $q = P^k$ for some prime $P$ and $k \geq 1$
     - Since $p \neq 1$, there exists a prime $P_p$ dividing $p$
     - Since $r \neq 1$, there exists a prime $P_r$ dividing $r$
     - Since $P^k = q = p \cdot r \cdot d$, both $P_p$ and $P_r$ divide $P^k$
     - By the theorem `PRIME_DIVEXP`, both $P_p$ and $P_r$ must divide $P$
     - Since $P$ is prime, this means $P_p = P_r = P$
     - But $p \cdot x = r \cdot y + 1$ implies $\gcd(p, r) = 1$, which means $P_p$ and $P_r$ cannot be the same prime
     - This contradiction shows $q$ cannot be a prime power

The implementation handles different cases when evaluating `primepow n`:
- If n = 0 or n = 1, returns the corresponding theorem directly
- If n can be factored as $p^k$ for a single prime p, applies the third theorem
- If n has at least two distinct prime factors, applies the fourth theorem (using Bézout's identity to find coefficients x and y)

### Mathematical insight
This conversion effectively decides whether a given number is a prime power by examining its prime factorization. The key insight is that:

1. A natural number is a prime power if and only if its prime factorization contains exactly one distinct prime (raised to some power ≥ 1)
2. Numbers like 0 and 1 are special cases that are not prime powers
3. For composite numbers with multiple prime factors, the proof exploits Bézout's identity to show they cannot be prime powers

This conversion is useful for number theory calculations and is particularly efficient because it works directly on concrete numerals rather than using general reasoning.

### Dependencies
- **Definitions**:
  - `primepow`: Defines a predicate that identifies prime powers as numbers of the form $p^k$ where $p$ is prime and $k \geq 1$
  
- **Theorems**:
  - `PRIME_0`: Proves that 0 is not a prime number
  - `PRIME_1`: Proves that 1 is not a prime number
  - `PRIME_FACTOR`: Shows that any number greater than 1 has a prime factor
  - `PRIME_DIVEXP`: States that if a prime $p$ divides $x^n$, then $p$ divides $x$

### Porting notes
When porting this conversion:
1. Ensure the target system has an equivalent concept of "conversions" (functions that transform terms to theorems)
2. Factor in differences in how prime factorization is computed in different systems
3. Make sure Bézout's identity computation is available in the target system
4. Be aware that the implementation uses pattern matching on the factorization result, which may need to be adapted
5. The implementation relies on the existence of conversions like `NUM_REDUCE_CONV` and `PRIME_CONV`, which would need equivalents in the target system

---

## APRIMEDIVISOR_CONV

### APRIMEDIVISOR_CONV
- `APRIMEDIVISOR_CONV`

### Type of the formal statement
- Conversion function (HOL Light implementation)

### Formal Content
```ocaml
let APRIMEDIVISOR_CONV =
  let pth = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)`,
    MESON_TAC[APRIMEDIVISOR_PRIMEPOW])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and aprimedivisor_tm = `aprimedivisor` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> aprimedivisor_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then failwith "APRIMEDIVISOR_CONV: not a prime power" else
    match factor q with
      [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | _ -> failwith "APRIMEDIVISOR_CONV: not a prime power";;
```

### Informal statement
`APRIMEDIVISOR_CONV` is a conversion function that computes `aprimedivisor q` when `q` is a prime power. It applies the theorem that for a prime power $q = p^k$ where $p$ is prime and $k \geq 1$, we have $\text{aprimedivisor}(q) = p$.

The function takes a term of the form `aprimedivisor n` where `n` is a numeral, factors `n` to determine if it's a prime power (of the form $p^k$ for prime $p$ and $k \geq 1$), and if so, returns the theorem `|- aprimedivisor n = p`.

### Informal proof
The conversion works as follows:

1. It first proves the auxiliary theorem `prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)` using `APRIMEDIVISOR_PRIMEPOW`.

2. When given a term `aprimedivisor n`:
   - It extracts the numeral `n`
   - It checks that `n` is not 0
   - It factors `n` using the `factor` function
   - If `n` factors as `[p,k]` (a single prime `p` raised to power `k`), it:
     - Instantiates the auxiliary theorem with the specific values of `p`, `k`, and `q`
     - Proves that `p` is prime using `PRIME_CONV`
     - Proves that `1 <= k` using numerical reduction
     - Applies these facts to derive `|- aprimedivisor n = p`
   - If `n` is not a prime power, it raises an error

### Mathematical insight
This conversion implements an efficient way to compute a prime divisor of a number when that number is a prime power. The mathematical insight is that for a prime power $p^k$, the smallest (and only) prime divisor is $p$ itself.

The conversion is part of a larger library for working with prime numbers and factorizations. It provides computational capabilities for symbolic reasoning about prime divisors of specific numbers.

### Dependencies
- Definitions:
  - `aprimedivisor`: Selects a prime divisor of a number using the choice operator
  - `primepow`: Defines a prime power as a number of the form $p^k$ where $p$ is prime and $k \geq 1$

- Theorems:
  - `APRIMEDIVISOR_PRIMEPOW`: Proves that `aprimedivisor(p EXP k) = p` when `p` is prime and `k ≥ 1`

### Porting notes
When porting this conversion:
1. Ensure your target system has a prime factorization algorithm equivalent to HOL Light's `factor`
2. The conversion relies on HOL Light's ability to work with and manipulate terms at runtime—adapt accordingly for systems with different meta-programming capabilities
3. The error handling should be adapted to match the target system's conventions
4. In systems with stronger typing, explicit type annotations may be needed

---

## mangoldt

### Name of formal statement
mangoldt

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let mangoldt = new_definition
  `mangoldt d = if primepow d then ln(&(aprimedivisor d)) else &0`;;
```

### Informal statement
The Mangoldt function $\Lambda(d)$ is defined as:

$$\Lambda(d) = \begin{cases}
\ln(p) & \text{if } d \text{ is a prime power} \\
0 & \text{otherwise}
\end{cases}$$

where $p$ is a prime divisor of $d$ when $d$ is a prime power.

More specifically, $d$ is a prime power when there exists a prime $p$ and an integer $k \geq 1$ such that $d = p^k$. In this case, $p$ is the unique prime divisor of $d$, and is obtained using the function `aprimedivisor`.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The Mangoldt function $\Lambda(d)$ is a fundamental arithmetic function in number theory. It plays a crucial role in the study of the distribution of prime numbers. Some key insights:

- It equals $\ln(p)$ when $d = p^k$ for some prime $p$ and integer $k \geq 1$, and zero otherwise.
- The von Mangoldt function appears in the explicit formula for counting prime numbers, connecting to the Riemann zeta function.
- It is used in the formulation of the logarithmic derivative of the Riemann zeta function.
- The summatory Mangoldt function, $\psi(x) = \sum_{n \leq x} \Lambda(n)$, is known as the Chebyshev function, which is closely related to the prime counting function.

This function was named after Hans von Mangoldt, who used it in his work on the explicit formula for the prime counting function.

### Dependencies
- Definitions:
  - `primepow`: Defines when a number is a prime power (exists p, k where k ≥ 1, p is prime, and q = p^k)
  - `aprimedivisor`: Returns a prime divisor of a number using the Hilbert epsilon operator
  - `ln`: The natural logarithm function

### Porting notes
When porting this definition:
- Ensure that the prime power concept is properly defined beforehand
- The definition uses the Hilbert epsilon operator via `aprimedivisor` to select a prime divisor. In systems without this operator, you might need to define a specific function that returns the unique prime divisor of a prime power
- For prime powers p^k, there is only one prime divisor p, so `aprimedivisor` is well-defined in this context

---

## MANGOLDT_POS

### MANGOLDT_POS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let MANGOLDT_POS = prove
 (`!d. &0 <= mangoldt d`,
  GEN_TAC THEN REWRITE_TAC[mangoldt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `2 <= a ==> 1 <= a`;
                PRIME_GE_2; LN_POS; REAL_OF_NUM_LE; primepow]);;
```

### Informal statement
The Mangoldt function $\Lambda(d)$ is non-negative for all natural numbers $d$, i.e.,
$$\forall d \in \mathbb{N}, \Lambda(d) \geq 0$$

Where the Mangoldt function is defined as:
$$\Lambda(d) = \begin{cases}
\ln(p) & \text{if } d = p^k \text{ where } p \text{ is prime and } k \geq 1 \\
0 & \text{otherwise}
\end{cases}$$

### Informal proof
To prove that the Mangoldt function is non-negative, we consider two cases based on its definition:

1. If $d$ is a prime power, i.e., $d = p^k$ where $p$ is prime and $k \geq 1$, then:
   - $\Lambda(d) = \ln(p)$
   - From `APRIMEDIVISOR_PRIMEPOW`, we know that for any prime $p$ and $k \geq 1$, the smallest prime divisor of $p^k$ is $p$
   - From `PRIME_GE_2`, we know that any prime number $p$ satisfies $p \geq 2$
   - Since $p \geq 2 > 1$, we can apply `LN_POS` which states that $\forall x, x \geq 1 \implies \ln(x) \geq 0$
   - Therefore, $\Lambda(d) = \ln(p) \geq 0$

2. If $d$ is not a prime power, then:
   - By definition, $\Lambda(d) = 0$
   - And trivially, $0 \geq 0$ by reflexivity of $\leq$ (used `REAL_LE_REFL`)

Thus, in both cases, $\Lambda(d) \geq 0$ for all natural numbers $d$.

### Mathematical insight
The Mangoldt function $\Lambda(d)$ plays a crucial role in analytic number theory, particularly in the study of the distribution of prime numbers. This theorem establishes the basic property that the function is non-negative, which is important for various applications involving sums of the Mangoldt function.

The non-negativity is essentially built into the definition, as the function either equals zero or the logarithm of a prime number. Since any prime number is at least 2, its logarithm is positive. This simple property is fundamental when working with the function in more complex contexts, such as in the explicit formulas relating the Mangoldt function to the zeros of the Riemann zeta function.

### Dependencies
- **Theorems**:
  - `PRIME_GE_2`: Every prime number is at least 2
  - `REAL_LE_REFL`: Reflexivity of less-than-or-equal relation for reals
  - `LN_POS`: For any real number $x \geq 1$, we have $\ln(x) \geq 0$
  - `APRIMEDIVISOR_PRIMEPOW`: For any prime $p$ and $k \geq 1$, the smallest prime divisor of $p^k$ is $p$

- **Definitions**:
  - `mangoldt`: The Mangoldt function defined as $\Lambda(d) = \ln(p)$ if $d = p^k$ for some prime $p$ and $k \geq 1$, and 0 otherwise
  - `primepow`: A number $q$ is a prime power if there exist $p$ and $k$ such that $q = p^k$ where $p$ is prime and $k \geq 1$

---

## LN_PRIMEFACT

### Name of formal statement
LN_PRIMEFACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_PRIMEFACT = prove
 (`!n. ~(n = 0)
       ==> (ln(&n) =
            sum(1,n) (\d. if primepow d /\ d divides n
                          then ln(&(aprimedivisor d)) else &0))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1,n) (\d. &0)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_0; LN_1]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIMEPOW_GE_2; DIVIDES_LE; NUM_REDUCE_CONV `2 <= 1`;
                  LE_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
    SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 < p <=> 2 <= p`] THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `?k. 1 <= k /\ (p EXP k) divides (p * m)` MP_TAC THENL
   [EXISTS_TAC `1` THEN SIMP_TAC[EXP_1; DIVIDES_RMUL; DIVIDES_REFL; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. !j. 1 <= j /\ (p EXP j) divides (p * m) ==> j <= k`
  MP_TAC THENL
   [MP_TAC(SPECL [`p:num`; `p * m:num`] BIG_POWER_LEMMA) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP k` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_MAX] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `sum (1,m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0) =
    sum (1,p * m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SUM_DIFF] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `1 + p * m = (1 + m) + (p * m - m)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
        `1 * y <= x ==> (1 + x = (1 + y) + (x - y))`) THEN
      SIMP_TAC[LE_MULT_RCANCEL] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUM_TWO] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    SUBGOAL_THEN
     `!d. d >= 1 + m
          ==> ((if primepow d /\ d divides m then ln (&(aprimedivisor d))
                else &0) = &0)`
    MP_TAC THENL
     [X_GEN_TAC `d:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 + m <= d /\ d <= m)`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_ZERO) THEN DISCH_THEN MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[PRIMEPOW_0; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `1 + p * m = p EXP k + 1 + (p * m - p EXP k)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `k <= p ==> (1 + p = k + 1 + (p - k))`) THEN
    ASM_MESON_TAC[DIVIDES_LE; MULT_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = a') /\ (l + b = c) ==> (l + a + b = a' + c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
    ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d divides (p * m) <=> d divides m`
     (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC `q = p:num` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> (a <=> b)`) THEN
      REWRITE_TAC[DIVIDES_LMUL] THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `p EXP (k - 1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[divides] THEN EXISTS_TAC `p EXP ((k - 1) - j)` THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `p EXP j < p EXP k` THEN ASM_REWRITE_TAC[LT_EXP] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `p EXP k divides (p * m)` THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV)
                  [th]) o MATCH_MP
          (ARITH_RULE `1 <= k ==> (k = SUC(k - 1))`)) THEN
      REWRITE_TAC[divides; EXP] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(AP_TERM `(divides) p` th)) THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `p divides q` MP_TAC THENL
       [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
      ASM_MESON_TAC[prime; PRIME_1];
      ALL_TAC] THEN
    UNDISCH_TAC `p * m = q EXP j * r` THEN
    UNDISCH_TAC `p divides r` THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
    SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN BINOP_TAC THENL
   [SUBGOAL_THEN `primepow (p EXP k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[primepow]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p EXP k) divides m)` ASSUME_TAC THENL
     [REWRITE_TAC[divides] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      MP_TAC(ARITH_RULE `~(k + 1 <= k)`) THEN REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
      MESON_TAC[MULT_ASSOC; DIVIDES_REFL; DIVIDES_RMUL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d divides (p * m) <=> d divides m`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `q = p:num` THENL
   [UNDISCH_THEN `q = p:num` SUBST_ALL_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ ~a ==> (a <=> b)`) THEN
    REWRITE_TAC[DIVIDES_LMUL] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= b ==> a < b`)) THEN
    REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2; NOT_LT];
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(AP_TERM `(divides) p` th)) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `p divides q` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
    ASM_MESON_TAC[prime; PRIME_1];
    ALL_TAC] THEN
  UNDISCH_TAC `p * m = q EXP j * r` THEN
  UNDISCH_TAC `p divides r` THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
  SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[]);;
```

### Informal statement
Let $n$ be a positive integer. Then the natural logarithm of $n$ can be expressed as:

$$\ln(n) = \sum_{d=1}^{n} \begin{cases}
\ln(\text{aprimedivisor}(d)) & \text{if } d \text{ is a prime power and } d \text{ divides } n \\
0 & \text{otherwise}
\end{cases}$$

Where:
- $\text{primepow}(d)$ means that $d$ is a prime power, i.e., $d = p^k$ for some prime $p$ and integer $k \geq 1$
- $\text{aprimedivisor}(d)$ is a function that selects a prime divisor of $d$. When $d$ is a prime power $p^k$, this function returns $p$.

### Informal proof
We prove this theorem by induction on $n$, using the well-founded induction principle on natural numbers.

First, consider the base case where $n = 1$:
- We have $\ln(1) = 0$ (by `LN_1`).
- For the sum, we need to show that all terms are zero.
- If $d$ is a prime power and $d$ divides $1$, then we must have $d = 1$. 
- But $1$ is not a prime power since $\text{primepow}(q) \Rightarrow 2 \leq q$ (by `PRIMEPOW_GE_2`).
- So all terms in the sum are zero, making the sum equal to $0 = \ln(1)$.

For the inductive step, let $n > 1$. By the prime factorization theorem (`PRIME_FACTOR`), there exists a prime $p$ that divides $n$, so $n = p \cdot m$ for some $m$.

Since $p$ is prime and $p \geq 2$, we have $m < n$. By the induction hypothesis:
$$\ln(m) = \sum_{d=1}^{m} \begin{cases}
\ln(\text{aprimedivisor}(d)) & \text{if } \text{primepow}(d) \text{ and } d \text{ divides } m \\
0 & \text{otherwise}
\end{cases}$$

Now we use the property of logarithms: $\ln(p \cdot m) = \ln(p) + \ln(m)$ since both $p$ and $m$ are positive.

Let's compute the maximum power $k$ such that $p^k$ divides $n = p \cdot m$. Such a $k$ exists by `BIG_POWER_LEMMA`.

We now split the sum for $n = p \cdot m$ into three parts:
1. Terms for $d = 1$
2. Terms for $d = p^k$ 
3. All other terms

For part 1, the term is zero since $1$ is not a prime power.

For part 2, the term contributes $\ln(p)$ since $p^k$ is a prime power that divides $n$, and $\text{aprimedivisor}(p^k) = p$ by `APRIMEDIVISOR_PRIMEPOW`.

For part 3, we need to show that for any other prime power $d$ dividing $n$:
- If $d = p^j$ for some $j < k$, then we already counted this in the sum for $m$
- If $d = q^j$ where $q \neq p$ is another prime, then $d$ divides $m$ if and only if $d$ divides $n$.

Putting these parts together, we get:
$$\ln(n) = \ln(p) + \ln(m) = \ln(p) + \sum_{d=1}^{m} [...] = \sum_{d=1}^{n} [...]$$

Which completes the proof.

### Mathematical insight
This theorem expresses the natural logarithm of a positive integer as a sum of logarithms of primes, with each prime appearing with a multiplicity equal to its exponent in the prime factorization. 

This is a remarkable connection between prime factorization and logarithms. The formula essentially says that:

$$\ln(n) = \sum_{\text{prime powers }p^k\text{ dividing }n} \ln(p)$$

So if $n = 2^3 \cdot 5^2 \cdot 11$, then $\ln(n) = \ln(2) + \ln(2) + \ln(2) + \ln(5) + \ln(5) + \ln(11)$.

This result is foundational in analytic number theory and relates to the study of the distribution of prime numbers. It provides a direct link between multiplicative number theory and the additive properties of logarithms.

### Dependencies
- **Theorems**:
  - `DIVIDES_REFL`: For all $x$, $x$ divides $x$
  - `DIVIDES_TRANS`: If $a$ divides $b$ and $b$ divides $c$, then $a$ divides $c$
  - `DIVIDES_RMUL`: For all $d$, $a$, $x$, if $d$ divides $a$ then $d$ divides $a \cdot x$
  - `PRIME_1`: $1$ is not prime
  - `PRIME_DIVPROD`: If $p$ is prime and $p$ divides $a \cdot b$, then $p$ divides $a$ or $p$ divides $b$
  - `PRIME_GE_2`: If $p$ is prime, then $2 \leq p$
  - `PRIME_FACTOR`: If $n > 1$, then there exists a prime $p$ such that $p$ divides $n$
  - `PRIME_DIVEXP`: If $p$ is prime and $p$ divides $x^n$, then $p$ divides $x$
  - `LN_MUL`: For positive $x$ and $y$, $\ln(x \cdot y) = \ln(x) + \ln(y)$
  - `LN_1`: $\ln(1) = 0$
  - `PRIMEPOW_GE_2`: If $q$ is a prime power, then $2 \leq q$
  - `APRIMEDIVISOR_PRIMEPOW`: If $p$ is prime and $k \geq 1$, then $\text{aprimedivisor}(p^k) = p$
  - `BIG_POWER_LEMMA`: For all $m$, $n$ with $2 \leq m$, there exists $k$ such that $n \leq m^k$

- **Definitions**:
  - `ln`: Natural logarithm
  - `primepow`: Prime power predicate
  - `aprimedivisor`: Function that selects a prime divisor

### Porting notes
When porting this theorem:
1. The definition of `aprimedivisor` uses Hilbert's epsilon operator (the `@` symbol in HOL Light) which may not have direct equivalents in other systems. It can be replaced with a function that provably returns a prime divisor.
2. The proof uses well-founded induction on natural numbers, which might be structured differently in other systems.
3. The handling of summation notation might differ between systems - ensure your summation bounds are correctly translated.
4. The proof structure involves breaking down a complex sum into several parts and requires careful tracking of divisibility conditions.

---

## MANGOLDT

### Name of formal statement
MANGOLDT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. mangoldt(d) * floor(&n / &d))`,
  GEN_TAC THEN REWRITE_TAC[LN_FACT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\m. sum(1,n) (\d. if primepow d /\ d divides m
                                then ln (&(aprimedivisor d))
                                else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LN_PRIMEFACT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `d < n + 1 ==> (n = d + (n - d))`)) THEN
    DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1 + d,n - d) (\k. &0)` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE
     `1 <= d /\ 1 + d <= r /\ (r <= d \/ (d = 0)) ==> F`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_SWAP] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[mangoldt] THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[SUM_0; REAL_MUL_LZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 <= d ==> ~(d = 0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV d`; `r = n MOD d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `floor (&(q * d + r) / &d) = &q` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
                 REAL_OF_NUM_LT; ARITH_RULE `0 < d <=> 1 <= d`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `r < d:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ (a = c) ==> (a + b = c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + q * d,r) (\x. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `d divides s` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `1 + x <= y * z ==> x < z * y`)) THEN
    ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    REWRITE_TAC[LT_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `d * (q + SUC e) < r + 1 + q * d` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `d * q + x < y + 1 + q * d <=> x <= y`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `a + b <= c ==> a <= c:num`)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  SIMP_TAC[SUM_1; DIVIDES_0; DIVIDES_LMUL; DIVIDES_REFL] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - b = a`] THEN
  REWRITE_TAC[GSYM SUM_GROUP] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0,q) (\x. ln (&(aprimedivisor d)))` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST; REAL_MUL_AC]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `1 <= d ==> (d = 1 + (d - 1))`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (funpow 2 LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a + b = a)`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(m * d + 1,d - 1) (\x. &0)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(d divides (t + 1))` MP_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `t + m * d + 1 < d - 1 + m * d + 1` THEN
    REWRITE_TAC[LT_ADD_RCANCEL] THEN
    UNDISCH_TAC `d divides (t + m * d + 1)` THEN
    ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
     [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVR;
                    DIVIDES_ONE; PRIMEPOW_GE_2; NUM_REDUCE_CONV `2 <= 1`];
      DISCH_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `d divides (t + m * d + 1)` THEN
  ONCE_REWRITE_TAC[ARITH_RULE `t + m * d + 1 = (t + 1) + m * d`] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVL]);;
```

### Informal statement
For any natural number $n$, the natural logarithm of the factorial of $n$ equals the sum over $d$ from $1$ to $n$ of the product of the Mangoldt function $\Lambda(d)$ and the floor of $\frac{n}{d}$:

$$\ln(n!) = \sum_{d=1}^{n} \Lambda(d) \cdot \left\lfloor\frac{n}{d}\right\rfloor$$

where the Mangoldt function $\Lambda(d)$ is defined as:
$$\Lambda(d) = \begin{cases}
\ln(p) & \text{if } d = p^k \text{ for some prime } p \text{ and integer } k \geq 1\\
0 & \text{otherwise}
\end{cases}$$

### Informal proof
We start by using the known result `LN_FACT`, which states that the logarithm of $n!$ equals the sum of logarithms of integers from $1$ to $n$:
$$\ln(n!) = \sum_{d=1}^{n} \ln(d)$$

The proof proceeds in several steps:

1. First, we transform each $\ln(d)$ using the `LN_PRIMEFACT` theorem, which expresses the logarithm of any positive integer in terms of its prime power divisors:
   $$\ln(d) = \sum_{k=1}^{d} \begin{cases} \ln(p) & \text{if } k \text{ is a prime power } p^j \text{ and } k \text{ divides } d \\ 0 & \text{otherwise} \end{cases}$$

2. This allows us to rewrite $\ln(n!)$ as a double sum:
   $$\ln(n!) = \sum_{m=1}^{n} \sum_{d=1}^{n} \begin{cases} \ln(p) & \text{if } d \text{ is a prime power } p^j \text{ and } d \text{ divides } m \\ 0 & \text{otherwise} \end{cases}$$

3. We then swap the order of summation using `SUM_SWAP` to get:
   $$\ln(n!) = \sum_{d=1}^{n} \sum_{m=1}^{n} \begin{cases} \ln(p) & \text{if } d \text{ is a prime power } p^j \text{ and } d \text{ divides } m \\ 0 & \text{otherwise} \end{cases}$$

4. For a fixed $d$, we consider the inner sum. If $d$ is not a prime power, all terms in the inner sum are zero.

5. If $d$ is a prime power, we note that the inner sum counts how many numbers $m$ from $1$ to $n$ are divisible by $d$. This count equals $\lfloor\frac{n}{d}\rfloor$.

6. Using the division theorem, we write $n = qd + r$ where $0 \leq r < d$, so $q = \lfloor\frac{n}{d}\rfloor$.

7. The inner sum then simplifies to $\ln(p) \cdot \lfloor\frac{n}{d}\rfloor$, which by definition is $\Lambda(d) \cdot \lfloor\frac{n}{d}\rfloor$.

8. Substituting this result into the outer sum gives:
   $$\ln(n!) = \sum_{d=1}^{n} \Lambda(d) \cdot \lfloor\frac{n}{d}\rfloor$$

which completes the proof.

### Mathematical insight
The Mangoldt function theorem provides a deep connection between factorials and prime powers. This result is fundamental in analytic number theory, particularly in understanding the distribution of prime numbers.

The theorem establishes that the logarithm of a factorial can be expressed as a weighted sum of the Mangoldt function values. This transformation is crucial because:

1. It connects factorials to prime numbers, showing how the growth of factorials is intimately related to the distribution of primes.

2. It is a key step in the proof of the Prime Number Theorem, as it relates $\ln(n!)$ to prime powers.

3. The Mangoldt function effectively counts prime powers with appropriate weights (the natural logarithm of the corresponding prime), making it an essential tool in the study of the zeta function and the distribution of primes.

This formula represents one of the fundamental identities in analytic number theory that bridges combinatorial structures (factorials) with prime number distributions.

### Dependencies
- Definitions:
  - `mangoldt`: Defines the Mangoldt function
  - `primepow`: Defines prime powers
  - `aprimedivisor`: Returns a prime divisor of a number
  - `ln`: Natural logarithm

- Theorems:
  - `LN_FACT`: Formula for logarithm of factorial
  - `LN_PRIMEFACT`: Expresses logarithm of an integer in terms of its prime factors
  - `PRIMEPOW_GE_2`: Prime powers are at least 2
  - `FLOOR_UNIQUE`: Characterization of the floor function
  - `SUM_SWAP`: Swapping the order of summation
  - `SUM_GROUP`: Grouping terms in a sum
  - `SUM_EQ`: Equality of sums with equal corresponding terms
  - `SUM_SPLIT`: Splitting a sum into two parts
  - `SUM_CONST`: Sum of constant terms

### Porting notes
When porting this theorem:
1. Ensure that the Mangoldt function is properly defined first.
2. The proof relies heavily on manipulating sums, so libraries for sum operations should be established before attempting this proof.
3. The floor function and divisibility relations are crucial for this theorem, so ensure these concepts are well-defined.
4. The proof makes extensive use of natural number arithmetic, especially divisibility and modular arithmetic.
5. Handling the quantification and the sum's index ranges might require special attention in different proof assistants.

---

## psi

### Name of formal statement
psi

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let psi = new_definition
  `psi(n) = sum(1,n) (\d. mangoldt(d))`;;
```

### Informal statement
The Chebyshev psi function $\psi(n)$ is defined as the sum of the von Mangoldt function $\Lambda(d)$ for all integers $d$ from $1$ to $n$:

$$\psi(n) = \sum_{d=1}^{n} \Lambda(d)$$

where $\Lambda(d)$ (denoted as `mangoldt d` in HOL Light) is the von Mangoldt function defined as:
$$\Lambda(d) = \begin{cases}
\ln(p) & \text{if } d = p^k \text{ for some prime } p \text{ and integer } k \geq 1 \\
0 & \text{otherwise}
\end{cases}$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The Chebyshev psi function $\psi(n)$ (also called the second Chebyshev function) plays a fundamental role in analytic number theory, particularly in the study of the distribution of prime numbers. 

This function has a close relationship with the prime number theorem. In fact, the asymptotic behavior of $\psi(n)$ is equivalent to the prime number theorem, as $\psi(n) \sim n$ as $n \to \infty$. More precisely, the prime number theorem is equivalent to $\psi(n) = n + o(n)$.

The function counts prime powers with a logarithmic weight. Each prime power $p^k$ contributes $\ln(p)$ to the sum, which means that $\psi(n)$ approximately measures the "logarithmic density" of prime powers up to $n$.

The Chebyshev psi function is often used in proofs related to the distribution of primes because it has nice analytic properties, especially in connection with the Riemann zeta function.

### Dependencies
- **Definitions**:
  - `mangoldt`: The von Mangoldt function
  - `sum`: The summation function

### Porting notes
When porting this definition to other proof assistants, ensure that:
1. The summation function has the same indexing convention (starting from 1 up to n inclusive)
2. The von Mangoldt function is defined correctly, especially the `primepow` predicate and the `aprimedivisor` function
3. Pay attention to how the natural number to real conversion is handled (the `&` operator in HOL Light)

---

## PSI_BOUNDS_LN_FACT

### PSI_BOUNDS_LN_FACT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_BOUNDS_LN_FACT = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) <= psi(n) /\
       psi(n) - psi(n DIV 2) <= ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))`,
  X_GEN_TAC `k:num` THEN MP_TAC(SPECL [`k:num`; `2`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`n = k DIV 2`; `d = k MOD 2`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[psi; MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n) (\d. mangoldt d * floor (&n / &d)) =
    sum (1,2 * n + d) (\d. mangoldt d * floor (&n / &d))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + n,n + d) (\k. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC[FLOOR_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 + n <= r ==> 0 < r`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `1 + n <= r` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `m * f - &2 * m * f' = m * (f - &2 * f')`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&2 * a <= b /\ b <= &2 * a + &1
      ==> b - &2 * a <= &1`) THEN
    ASM_SIMP_TAC[FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1,2 * n + d) (\d. mangoldt d) - sum(1,n) (\d. mangoldt d) =
    sum(1,2 * n + d) (\d. if d <= n then &0 else mangoldt d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(c = &0) /\ (b = d) ==> ((a + b) - a = c + d)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1,n) (\k. &0)` THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
      MATCH_MP_TAC SUM_EQ THEN
      SIMP_TAC[ARITH_RULE `r < n + 1 <=> r <= n`];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[ARITH_RULE `1 + n <= r ==> ~(r <= n)`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `m * a - &2 * m * b = m * (a - &2 * b)`] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `a = a * &1`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ &1 <= a ==> &1 <= a - &2 * b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < r <=> 1 <= r`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_REWRITE_TAC[GSYM NOT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = &1) ==> &1 <= a`) THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < r <=> 1 <= r`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_MUL;
              REAL_OF_NUM_ADD] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the following inequalities hold:
$$\ln(n!) - 2 \ln((n \div 2)!) \leq \psi(n)$$
$$\psi(n) - \psi(n \div 2) \leq \ln(n!) - 2 \ln((n \div 2)!)$$

where:
- $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ is the second Chebyshev function
- $\Lambda(d)$ is the Mangoldt function defined as $\ln(p)$ if $d = p^k$ for some prime $p$ and integer $k \geq 1$, and $0$ otherwise
- $n \div 2$ is the integer division of $n$ by $2$

### Informal proof
The proof establishes bounds on the Chebyshev $\psi$ function in terms of factorial expressions.

Let's begin by writing $n = 2m + r$ where $m = n \div 2$ and $r \in \{0, 1\}$ is the remainder when dividing $n$ by $2$.

First, we use the Mangoldt identity for factorials: $\ln(n!) = \sum_{d=1}^n \Lambda(d) \lfloor \frac{n}{d} \rfloor$

We can equivalently write:
$$\sum_{d=1}^{n} \Lambda(d) \lfloor \frac{m}{d} \rfloor = \sum_{d=1}^{2m+r} \Lambda(d) \lfloor \frac{m}{d} \rfloor$$

This equality holds because for $d > m$, we have $\lfloor \frac{m}{d} \rfloor = 0$.

For the first inequality:
- We need to show $\ln(n!) - 2\ln(m!) \leq \psi(n)$
- Using the Mangoldt identity: $\ln(n!) = \sum_{d=1}^n \Lambda(d) \lfloor \frac{n}{d} \rfloor$ and $\ln(m!) = \sum_{d=1}^m \Lambda(d) \lfloor \frac{m}{d} \rfloor$
- We can rewrite the left side as $\sum_{d=1}^n \Lambda(d)(\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor)$
- For each $d$ from $1$ to $n$, we have $2\lfloor \frac{m}{d} \rfloor \leq \lfloor \frac{2m+r}{d} \rfloor \leq 2\lfloor \frac{m}{d} \rfloor + 1$ (using `FLOOR_DOUBLE_NUM`)
- Therefore, $\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor \leq 1$
- This implies $\sum_{d=1}^n \Lambda(d)(\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor) \leq \sum_{d=1}^n \Lambda(d) = \psi(n)$

For the second inequality:
- We need to show $\psi(n) - \psi(m) \leq \ln(n!) - 2\ln(m!)$
- We can write $\psi(n) - \psi(m) = \sum_{d=m+1}^n \Lambda(d)$
- Similarly, we can express $\ln(n!) - 2\ln(m!)$ as $\sum_{d=1}^n \Lambda(d)(\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor)$
- For $d \leq m$, we have $\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor \geq 0$ (using `FLOOR_DOUBLE_NUM`)
- For $d > m$, we have $\lfloor \frac{m}{d} \rfloor = 0$ and $\lfloor \frac{n}{d} \rfloor = 1$ (for $d \leq n$)
- Therefore, $\sum_{d=m+1}^n \Lambda(d) \leq \sum_{d=1}^n \Lambda(d)(\lfloor \frac{n}{d} \rfloor - 2\lfloor \frac{m}{d} \rfloor)$

Thus, we have established both inequalities.

### Mathematical insight
This theorem provides important bounds on the Chebyshev $\psi$ function, which plays a crucial role in number theory, especially in the study of prime numbers. The result establishes a relationship between the $\psi$ function and factorial expressions.

The bounds are particularly useful in proving results like Bertrand's postulate (that there is always a prime between $n$ and $2n$ for $n \geq 1$) and other theorems about the distribution of prime numbers. The proof uses the Mangoldt identity for factorials, which connects the factorial function to the Mangoldt function.

The key insight is exploiting the relationship between values of $\psi$ at $n$ and $n/2$, showing they differ by approximately $\ln(n!) - 2\ln((n/2)!)$. This provides a way to analyze the growth rate of $\psi$ and, consequently, the distribution of primes.

### Dependencies
- **Theorems**:
  - `INTEGER_CLOSED`: Properties of integers under various operations
  - `FLOOR_UNIQUE`: Characterization of the floor function
  - `FLOOR_EQ_0`: Conditions for when the floor of a real number equals zero
  - `REAL_MUL_RID`: Right identity of multiplication by 1
  - `REAL_MUL_LZERO`: Left zero of multiplication
  - `REAL_LE_MUL`: Conditions for non-negative product
  - `REAL_SUB_LE`: Subtraction and inequality relation
  - `REAL_POS`: Non-negativity of real numbers
  - `SUM_LE`: Monotonicity of summation
  - `SUM_EQ`: Equality of sums with equal terms
  - `SUM_CMUL`: Constant multiplication in summation
  - `SUM_SUB`: Subtraction of sums
  - `SUM_0`: Sum of zero terms
  - `SUM_SPLIT`: Splitting summation ranges
  - `MANGOLDT`: The Mangoldt identity for factorials
  - `FLOOR_DOUBLE_NUM`: Properties of floor function with doubling
  - `MANGOLDT_POS`: Non-negativity of the Mangoldt function

- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: The Mangoldt function
  - `psi`: The second Chebyshev function

### Porting notes
When porting this theorem:
1. Ensure the Mangoldt function and Chebyshev psi function are defined consistently
2. The proof relies heavily on properties of the floor function and summation operations
3. Be careful with integer division (`DIV`) which behaves differently in some systems
4. The Mangoldt identity for factorials is a key component and should be verified
5. Pay attention to the handling of inequality chains in the target system

---

## LN_FACT_DIFF_BOUNDS

### LN_FACT_DIFF_BOUNDS
- `LN_FACT_DIFF_BOUNDS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LN_FACT_DIFF_BOUNDS = prove
 (`!n. abs((ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))) - &n * ln(&2))
       <= &4 * ln(if n = 0 then &1 else &n) + &3`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[FACT; MULT_CLAUSES; LN_1; DIV_0; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `q = 0` THENL
   [UNDISCH_TAC `~(q * 2 + r = 0)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < 2 ==> ((r = 0) <=> ~(r = 1))`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[num_CONV `1`; FACT; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LN_1] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_SUB_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> x <= &3`) THEN
    SUBST1_TAC(REAL_ARITH `&2 = &1 + &1`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(x) <= &1 + &1`) THEN
    ASM_SIMP_TAC[LN_POS; LN_LE; REAL_OF_NUM_LE; ARITH; REAL_LE_ADDL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a'. abs((a' - b) - c) <= d - abs(a' - a) ==> abs((a - b) - c) <= d`) THEN
  EXISTS_TAC `ln(&(FACT(q * 2)))` THEN
  MP_TAC(SPEC `q:num` LN_FACT_BOUNDS) THEN
  MP_TAC(SPEC `q * 2` LN_FACT_BOUNDS) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a - (a2 - &2 * a1)) <= b - &2 * b1 - b2
    ==> abs(l2 - a2) <= b2
        ==> abs(l1 - a1) <= b1
            ==> abs((l2 - &2 * l1) - a) <= b`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  REWRITE_TAC[REAL_ARITH
   `(q * &2 + r) * l2 - ((q * &2) * (lq + l2) - q * &2 - &2 * (q * lq - q)) =
    r * l2`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x <= a - b - c - d <=> x + b <= a - c - d`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ln(&2) + ln(&q * &2 + &r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 * y ==> abs(x) <= y`) THEN
      SIMP_TAC[LN_POS_LT; REAL_LT_IMP_LE; REAL_LE_RMUL_EQ;
               REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `r < 2` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
     `r < 2 ==> (r = 0) \/ (r = 1)`))
    THENL
     [REWRITE_TAC[ADD_CLAUSES; REAL_SUB_REFL; REAL_ADD_RID; REAL_ABS_NUM] THEN
      MATCH_MP_TAC LN_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; FACT] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT;
             FACT_LT; LT_0] THEN
    REWRITE_TAC[REAL_ARITH `abs(b - (a + b)) = abs a`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(x) <= x`) THEN
    MATCH_MP_TAC LN_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `l2 + lnn <= (&4 * lnn + &3) - a - b
    <=> a + b + l2 <= &3 * lnn + &3`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 * ln(&q * &2) + &3` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_LE_RADD; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[LN_MONO_LE; REAL_POS; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < q <=> ~(q = 0)`;
                 REAL_ARITH `&0 < q /\ &0 <= r ==> &0 < q * &2 + r`;
                 REAL_ARITH `&0 < q ==> &0 < q * &2`] THEN
    REWRITE_TAC[REAL_LE_ADDR; REAL_POS]] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  SUBGOAL_THEN `&0 <= ln(&2)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE; ARITH]);;
```

### Informal statement
For all natural numbers $n$, the following inequality holds:
$$\left|\left(\ln\left(\text{FACT}(n)\right) - 2 \cdot \ln\left(\text{FACT}\left(\lfloor\frac{n}{2}\rfloor\right)\right)\right) - n \cdot \ln(2)\right| \leq 4 \cdot \ln(\max(1,n)) + 3$$

where:
- $\text{FACT}(n)$ represents the factorial function $n!$
- $\ln$ is the natural logarithm
- $n \text{ DIV } 2$ is integer division (floor division)

### Informal proof
The proof establishes bounds on the difference between $\ln(n!) - 2\ln((n/2)!)$ and $n\ln(2)$.

* First, we handle the base case when $n = 0$:
  - In this case, $0! = 1$, $\ln(1) = 0$, $0 \div 2 = 0$, and $0 \cdot \ln(2) = 0$
  - The inequality simplifies to $|0| \leq 4 \cdot \ln(1) + 3 = 3$, which is true

* For the general case where $n > 0$, we use the division theorem to write $n = 2q + r$ where $q = \lfloor n/2 \rfloor$ and $r \in \{0, 1\}$

* If $q = 0$, then $n$ must be 1 (since we already handled $n = 0$)
  - We evaluate the expression directly using $1! = 1$ and $0! = 1$
  - The result simplifies to $|0 - \ln(2)| = \ln(2) \leq 3$, which is true since $\ln(2) < 1$

* For $q > 0$, we use a bound on $|\ln(n!) - (n\ln(n) - n)|$ provided by `LN_FACT_BOUNDS`
  - We apply this bound to both $\ln(n!)$ and $\ln((n/2)!)$
  - We manipulate the expression using properties of logarithms, particularly $\ln(a \cdot b) = \ln(a) + \ln(b)$
  - For the case where $r = 0$, the error term simplifies
  - For the case where $r = 1$, we account for the additional factorial term

* Throughout the proof, we use properties of logarithms and basic inequalities:
  - $\ln$ is monotonically increasing
  - $\ln(1) = 0$
  - $\ln(ab) = \ln(a) + \ln(b)$ for positive $a, b$
  - $\ln(n) \geq 0$ for $n \geq 1$

* After algebraic manipulations and applying the appropriate bounds, we arrive at the desired inequality.

### Mathematical insight
This theorem provides tight bounds for the difference between $\ln(n!) - 2\ln((n/2)!)$ and $n\ln(2)$. The result is significant in combinatorics and number theory, particularly for analyzing:

1. The growth rate of factorials
2. Behavior of central binomial coefficients
3. Entropy estimates in information theory

The result shows that $\ln(n!) - 2\ln((n/2)!)$ approximates $n\ln(2)$ with an error bounded by logarithmic terms. This approximation is useful for asymptotic analysis of combinatorial quantities and is related to Stirling's approximation for factorials.

The proof demonstrates how to handle different ranges of values carefully and combine bounds on logarithms of factorials to obtain tight composite bounds.

### Dependencies
- **Theorems**:
  - `LN_FACT_BOUNDS`: Bound on $|\ln(n!) - (n\ln(n) - n)|$
  - `LN_MUL`: Logarithm of product property
  - `LN_1`: Natural logarithm of 1 is 0
  - `LN_POS`: Positivity of logarithm for values ≥ 1
  - `LN_POS_LT`: Strict positivity of logarithm for values > 1
  - `LN_MONO_LE`: Monotonicity of logarithm
  - `LN_LE`: Upper bound on logarithm of 1+x
  - `REAL_LE_TRANS`: Transitivity of ≤ for reals
  - `REAL_LE_RADD`, `REAL_LE_LMUL_EQ`, `REAL_LE_RMUL_EQ`: Manipulation of inequalities
  - `REAL_MUL_LZERO`, `REAL_MUL_RZERO`: Multiplication by zero
  - Various other real number arithmetic properties

- **Definitions**:
  - `ln`: Natural logarithm function

### Porting notes
When porting this theorem:
1. Ensure that the factorial definition matches HOL Light's (with 0! = 1)
2. Be careful with integer division (DIV) operation - ensure it implements floor division
3. The proof relies heavily on bounds for logarithms of factorials, so `LN_FACT_BOUNDS` should be ported first
4. Some proof assistants may have more powerful automation for real arithmetic, which could simplify portions of this proof
5. The conditional expression `if n = 0 then &1 else &n` may need to be handled differently in type systems with stricter typing

---

## PSI_BOUNDS_INDUCT

### PSI_BOUNDS_INDUCT
- `PSI_BOUNDS_INDUCT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_BOUNDS_INDUCT = prove
 (`!n. &n * ln(&2) - (&4 * ln (if n = 0 then &1 else &n) + &3) <= psi(n) /\
       psi(n) - psi(n DIV 2)
       <= &n * ln(&2) + (&4 * ln (if n = 0 then &1 else &n) + &3)`,
  MESON_TAC[PSI_BOUNDS_LN_FACT; LN_FACT_DIFF_BOUNDS; REAL_ARITH
             `m <= a /\ b <= m /\ abs(m - n) <= k
              ==> n - k <= a /\ b <= n + k`]);;
```

### Informal statement
For all natural numbers $n$, the following inequalities hold:
$$n \cdot \ln(2) - (4 \cdot \ln(\text{if}\ n = 0\ \text{then}\ 1\ \text{else}\ n) + 3) \leq \psi(n)$$
and
$$\psi(n) - \psi(n \div 2) \leq n \cdot \ln(2) + (4 \cdot \ln(\text{if}\ n = 0\ \text{then}\ 1\ \text{else}\ n) + 3)$$

where $\psi(n)$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, with $\Lambda$ being the von Mangoldt function, and $\div$ represents integer division.

### Informal proof
The proof uses the theorems `PSI_BOUNDS_LN_FACT` and `LN_FACT_DIFF_BOUNDS` along with arithmetic manipulation.

From `PSI_BOUNDS_LN_FACT`, we have:
$$\ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(n \div 2)) \leq \psi(n)$$
and
$$\psi(n) - \psi(n \div 2) \leq \ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(n \div 2))$$

From `LN_FACT_DIFF_BOUNDS`, we have:
$$|\ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(n \div 2)) - n \cdot \ln(2)| \leq 4 \cdot \ln(\text{if}\ n = 0\ \text{then}\ 1\ \text{else}\ n) + 3$$

By a general arithmetic principle, if $m \leq a$ and $b \leq m$ and $|m - n| \leq k$, then $n - k \leq a$ and $b \leq n + k$.

Applying this principle with:
- $m = \ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(n \div 2))$
- $a = \psi(n)$
- $b = \psi(n) - \psi(n \div 2)$
- $n = n \cdot \ln(2)$
- $k = 4 \cdot \ln(\text{if}\ n = 0\ \text{then}\ 1\ \text{else}\ n) + 3$

We obtain the desired inequalities.

### Mathematical insight
This theorem establishes upper and lower bounds for the Chebyshev function $\psi(n)$ and the difference $\psi(n) - \psi(n \div 2)$ in terms of $n \cdot \ln(2)$ plus correction terms. The Chebyshev function $\psi(n)$ plays a crucial role in number theory, particularly in the study of the distribution of prime numbers.

The bounds here show that $\psi(n)$ grows approximately like $n \cdot \ln(2)$, with an error term involving $\ln(n)$. This is a step toward proving stronger asymptotic results about the distribution of primes, such as the Prime Number Theorem.

The difference $\psi(n) - \psi(n \div 2)$ represents the contribution to the Chebyshev function from the interval $(n \div 2, n]$, which is approximately $n \cdot \ln(2)/2$.

### Dependencies
- `PSI_BOUNDS_LN_FACT`: Relates the Chebyshev function to factorial values
- `LN_FACT_DIFF_BOUNDS`: Bounds on the difference between factorial logarithm terms
- `psi`: Definition of the Chebyshev function
- `ln`: Definition of the natural logarithm

### Porting notes
When implementing this in other proof assistants:
- Ensure the Chebyshev function and von Mangoldt function are correctly defined
- Handle the case distinction for n=0 carefully
- The proof relies on arithmetic manipulation of inequalities, which should be relatively straightforward to port
- The integer division operation (DIV) needs to be properly implemented

---

## MANGOLDT_CONV

### Name of formal statement
MANGOLDT_CONV

### Type of the formal statement
Conversion function (let-binding)

### Formal Content
```ocaml
let MANGOLDT_CONV =
  GEN_REWRITE_CONV I [mangoldt] THENC
  RATOR_CONV(LAND_CONV PRIMEPOW_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  TRY_CONV(funpow 2 RAND_CONV APRIMEDIVISOR_CONV);;
```

### Informal statement
`MANGOLDT_CONV` is a conversion function in HOL Light that evaluates the von Mangoldt function $\Lambda(d)$ on numeric literals. The von Mangoldt function is defined as:

$$\Lambda(d) = \begin{cases}
\ln(p) & \text{if } d = p^k \text{ for some prime } p \text{ and integer } k \geq 1 \\
0 & \text{otherwise}
\end{cases}$$

This conversion automatically computes the value of the von Mangoldt function for a given numeral input.

### Informal proof
This is a conversion function that combines several other conversions to compute the von Mangoldt function value:

1. First, it unfolds the definition of the von Mangoldt function (`mangoldt`) using `GEN_REWRITE_CONV`.
2. Then it evaluates whether the input is a prime power by applying `PRIMEPOW_CONV` to the condition part of the if-then-else expression.
3. Next, it applies the standard conditional simplification rules (`COND_CLAUSES`) to reduce the if-then-else expression based on the result of the prime power test.
4. Finally, if the number is a prime power, it applies `APRIMEDIVISOR_CONV` twice (once to reach the term and once to evaluate it) to compute the prime that divides the number.

The computation follows directly from combining these conversion functions in the appropriate sequence.

### Mathematical insight
The von Mangoldt function $\Lambda(d)$ is an important arithmetic function in analytic number theory. It equals $\ln(p)$ when $d$ is a power of a prime $p$, and zero otherwise. This function plays a crucial role in the proof of the Prime Number Theorem and in studying the distribution of prime numbers.

This conversion automates the evaluation of the von Mangoldt function for explicit numerals, which is useful in formal calculations involving this function. The implementation leverages factorization and primality testing to determine if a number is a prime power and, if so, to identify the relevant prime.

### Dependencies
- **Definitions:**
  - `mangoldt`: Defines the von Mangoldt function
  
- **Theorems and Conversions:**
  - `PRIMEPOW_CONV`: Conversion that determines if a number is a prime power
  - `APRIMEDIVISOR_CONV`: Conversion that finds a prime divisor of a prime power
  - `COND_CLAUSES`: Standard theorems for simplifying conditional expressions

### Porting notes
When porting this to another proof assistant:
1. You'll need to have a factorization algorithm available to check if a number is a prime power
2. You'll need to implement the von Mangoldt function definition
3. The approach of chaining conversions is common in HOL Light but may look different in other systems:
   - In Lean, this might be implemented as a computable function using match expressions
   - In Isabelle, you might use the simplifier with conditional rewrite rules
   - In Coq, you might use a Fixpoint function with pattern matching

---

## MANGOLDT_CONV

### MANGOLDT_CONV

### Type of the formal statement
Conversion function (used to compute values of the Mangoldt function)

### Formal Content
```ocaml
let MANGOLDT_CONV =
  let pth0 = prove
   (`mangoldt 0 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`mangoldt 1 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (mangoldt q = ln(&p))`,
    SIMP_TAC[mangoldt; APRIMEDIVISOR_PRIMEPOW] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (mangoldt q = ln(&1))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(primepow q)`
     (fun th -> REWRITE_TAC[LN_1; th; mangoldt]) THEN
    REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and mangoldt_tm = `mangoldt` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> mangoldt_tm then failwith "expected mangoldt(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then pth0
    else if q =/ num 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in MANGOLDT_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ num 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;
```

### Informal statement
This is a conversion function that computes the value of the von Mangoldt function $\Lambda(n)$ for numeric arguments. The function establishes that:

1. $\Lambda(0) = \ln(1) = 0$
2. $\Lambda(1) = \ln(1) = 0$
3. For prime powers $q = p^k$ where $p$ is prime and $k \geq 1$, $\Lambda(q) = \ln(p)$
4. For all other natural numbers, $\Lambda(q) = 0$

The function uses efficient computation methods to avoid repeated primality testing.

### Informal proof
This conversion function is constructed by proving several key theorems and then combining them into an efficient computation procedure:

1. First, it proves that $\Lambda(0) = \ln(1) = 0$ by:
   - Using the definition of the Mangoldt function
   - Showing that 0 is not a prime power (using `EXP_EQ_0` and `PRIME_0`)
   - Therefore the function returns $\ln(1)$ which equals 0

2. Next, it proves that $\Lambda(1) = \ln(1) = 0$ by:
   - Using the definition of the Mangoldt function
   - Showing that 1 is not a prime power (since $1 = p^0$ for any prime $p$, but the definition requires $k \geq 1$)

3. For prime powers $q = p^k$ with $k \geq 1$ and $p$ prime, it proves that $\Lambda(q) = \ln(p)$ by:
   - Using `APRIMEDIVISOR_PRIMEPOW` to establish that for a prime power $p^k$, the "a prime divisor" function returns $p$
   - Applying the definition of the Mangoldt function

4. For composite numbers that aren't prime powers, it proves that $\Lambda(q) = \ln(1) = 0$ by:
   - Using a condition where $q = p \cdot r \cdot d$ and $p$ and $r$ are coprime (indicated by $p \cdot x = r \cdot y + 1$)
   - Proving by contradiction that such numbers cannot be prime powers

Finally, the implementation combines these theorems into an efficient algorithm that:
- Handles 0 and 1 as special cases
- Factors the input number $q$
- If $q$ is a prime power (has only one prime factor with some exponent), computes $\Lambda(q) = \ln(p)$
- Otherwise returns 0

### Mathematical insight
The von Mangoldt function $\Lambda(n)$ is defined as:
- $\ln(p)$ if $n = p^k$ for some prime $p$ and integer $k \geq 1$
- 0 otherwise

It plays a crucial role in analytic number theory, especially in the study of the distribution of prime numbers. The function appears in the explicit formula for the prime counting function and is related to the Riemann zeta function through the identity:
$$-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^{\infty} \frac{\Lambda(n)}{n^s}$$

This conversion implementation provides an efficient way to compute the Mangoldt function for specific numeric values, avoiding repeated primality testing by using number factorization and clever case handling.

### Dependencies
- **Theorems**:
  - `PRIME_0`: 0 is not prime
  - `PRIME_1`: 1 is not prime
  - `PRIME_FACTOR`: Every number greater than 1 has a prime factor
  - `PRIME_DIVEXP`: If a prime divides a power, it divides the base
  - `LN_1`: $\ln(1) = 0$
  - `APRIMEDIVISOR_PRIMEPOW`: For a prime power $p^k$ with $k \geq 1$, the function `aprimedivisor` returns $p$

- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: Von Mangoldt function defined as $\Lambda(d) = \ln(\text{aprimedivisor}(d))$ if $d$ is a prime power, otherwise 0
  - `primepow`: Predicate that identifies prime powers ($q = p^k$ where $p$ is prime and $k \geq 1$)

### Porting notes
When porting this to other systems:
1. You'll need to define the von Mangoldt function and the concept of "prime power"
2. The implementation relies on efficient factorization (`factor q`), which should be available in the target system
3. The Bézout identity computation (`bezout(p,r)`) is used to establish coprimality
4. Consider whether the target system needs explicit numeric conversion or whether it can handle the computation more directly
5. The conversion is optimized to avoid redundant primality tests - maintain this efficiency in the port if possible

---

## PSI_LIST

### PSI_LIST

### Type of the formal statement
- function

### Formal Content
```ocaml
let PSI_LIST =
  let PSI_0 = prove
   (`psi(0) = ln(&1)`,
    REWRITE_TAC[psi; sum; LN_1])
  and PSI_SUC = prove
   (`psi(SUC n) = psi(n) + mangoldt(SUC n)`,
    REWRITE_TAC[psi; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    SIMP_CONV [REAL_ADD_RID; GSYM LN_MUL; REAL_OF_NUM_MUL;
               REAL_OF_NUM_LT; ARITH] in
  let rec PSI_LIST n =
    if n = 0 then [PSI_0] else
    let ths = PSI_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PSI_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    let th3 = CONV_RULE(COMB_CONV (funpow 2 RAND_CONV NUM_SUC_CONV)) th2 in
    let th4 = CONV_RULE (funpow 2 RAND_CONV MANGOLDT_CONV) th3 in
    (CONV_RULE(RAND_CONV SIMPER_CONV) th4)::ths in
  PSI_LIST;;
```

### Informal statement
The function `PSI_LIST` computes a list of theorems stating the values of the Chebyshev function $\psi(n)$ for all natural numbers up to a given bound. 

Specifically, it recursively builds a list where:
- For $n = 0$, it returns the theorem $\psi(0) = \ln(1)$
- For each subsequent value, it applies the recurrence relation $\psi(n+1) = \psi(n) + \Lambda(n+1)$

Where $\psi$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ and $\Lambda$ is the von Mangoldt function.

### Informal proof
The implementation consists of two key theorems and a recursive function:

1. First, it establishes base cases:
   - `PSI_0`: Proves that $\psi(0) = \ln(1)$ by using the definitions of $\psi$, sum, and the fact that $\ln(1) = 0$
   - `PSI_SUC`: Proves the recurrence relation $\psi(\text{SUC}(n)) = \psi(n) + \Lambda(\text{SUC}(n))$ using the definition of $\psi$ and properties of summation

2. The recursive function `PSI_LIST` then:
   - For $n = 0$, returns `[PSI_0]`
   - For $n > 0$:
     - Recursively computes `PSI_LIST(n-1)`
     - Applies the recurrence relation using the theorem `PSI_SUC`
     - Performs a sequence of rule and conversion applications to compute the exact value of $\psi(n)$ by:
       - Substituting the known value of $\psi(n-1)$
       - Converting the successor to the numeral representation
       - Computing the value of the Mangoldt function at $n$ using `MANGOLDT_CONV`
       - Simplifying the resulting expression using properties of logarithms

### Mathematical insight
The Chebyshev function $\psi(n)$ is an important function in number theory, particularly in the study of the distribution of prime numbers. It's defined as the sum of the von Mangoldt function $\Lambda(d)$ for $1 \leq d \leq n$.

This implementation provides an efficient way to compute the exact values of $\psi(n)$ for all values up to a given bound, which is useful for verifying asymptotic properties of this function. The recursive approach leverages the natural recurrence relation and previously computed values to build up the complete list.

The function is particularly valuable in the context of results like Bertrand's postulate and other theorems about prime number distribution, as it provides concrete values that can be used to verify theorems and explore patterns.

### Dependencies
- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: The von Mangoldt function
  - `psi`: The second Chebyshev function

- **Theorems**:
  - `sum`: Properties of finite summation
  - `LN_MUL`: Logarithm of a product
  - `LN_1`: Theorem stating that $\ln(1) = 0$
  - `MANGOLDT_CONV`: Conversion for calculating values of the Mangoldt function

### Porting notes
When porting this implementation:
1. Ensure that the von Mangoldt function and Chebyshev function are correctly defined first
2. Implement the conversion function for computing Mangoldt values efficiently
3. The implementation relies on HOL Light's conversion system - in other systems, you may need to use a different approach for the iterative theorem building
4. Consider whether your target system can efficiently handle the recursive accumulation of theorems, or if you need an alternative approach to compute the sequence of values

---

## PSI_LIST_300

### Name of formal statement
PSI_LIST_300

### Type of the formal statement
theorem/definition

### Formal Content
```ocaml
let PSI_LIST_300 = PSI_LIST 300;;
```

### Informal statement
`PSI_LIST_300` is the list of theorems that explicitly compute the values of the Chebyshev psi function $\psi(n)$ for all integers $n$ from $0$ to $300$.

The list contains theorems of the form:
- $\psi(0) = \ln(1)$
- $\psi(1) = \ln(1) + \Lambda(1)$
- $\psi(2) = \ln(1) + \Lambda(1) + \Lambda(2)$
- ...
- $\psi(300) = \ln(1) + \Lambda(1) + \Lambda(2) + ... + \Lambda(300)$

where $\Lambda(n)$ is the von Mangoldt function.

### Informal proof
This is a computational definition that calls the function `PSI_LIST` with argument 300. The `PSI_LIST` function recursively constructs a list of theorems about the values of the Chebyshev psi function.

The construction relies on two base theorems:
- `PSI_0`: states that $\psi(0) = \ln(1)$
- `PSI_SUC`: states that $\psi(n+1) = \psi(n) + \Lambda(n+1)$ for any natural number $n$

For each $n$ from 1 to 300, the function:
1. Applies the successor theorem `PSI_SUC` with the appropriate instantiation
2. Rewrites using the theorem for $\psi(n-1)$ 
3. Simplifies the successor expression for the natural number
4. Computes the value of $\Lambda(n)$ using `MANGOLDT_CONV`
5. Performs additional simplifications

The result is a list of 301 theorems, with the theorem for $\psi(300)$ at the head of the list.

### Mathematical insight
The Chebyshev psi function $\psi(n)$ is defined as $\psi(n) = \sum_{k=1}^{n} \Lambda(k)$ where $\Lambda$ is the von Mangoldt function. This function plays a crucial role in number theory and particularly in the study of the distribution of prime numbers.

Computing explicit values of $\psi(n)$ up to 300 provides concrete data that can be useful for:
1. Testing conjectures related to the prime number theorem
2. Analyzing the growth rate of the function
3. Studying the error terms in asymptotic approximations

This computation demonstrates how formal theorem proving systems can be used to precisely compute mathematical functions with complex definitions, ensuring that every step is rigorously verified.

### Dependencies
- **Theorems**:
  - `PSI_LIST`: Recursive function that generates theorems about $\psi(n)$ values
  - `PSI_0`: Theorem stating $\psi(0) = \ln(1)$
  - `PSI_SUC`: Theorem stating $\psi(n+1) = \psi(n) + \Lambda(n+1)$

- **Definitions**:
  - `psi`: The Chebyshev psi function
  - `mangoldt`: The von Mangoldt function

### Porting notes
When porting this computation to another proof assistant:
1. First implement the von Mangoldt function $\Lambda(n)$ and the Chebyshev psi function $\psi(n)$
2. Prove the base cases: $\psi(0) = \ln(1)$ and $\psi(n+1) = \psi(n) + \Lambda(n+1)$
3. Develop a conversion/tactic for computing $\Lambda(n)$ values efficiently
4. Create a recursive function to build the list of theorems
5. Consider performance optimizations if computing for large ranges of values, as the recursive approach may be computationally expensive in some systems

---

## PSI_UBOUND_128

### Name of formal statement
PSI_UBOUND_128

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_128 = prove
 (`!n. n <= 128 ==> psi(n) <= &133 / &128 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 128 <=> n < 129`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;
```

### Informal statement
For all natural numbers $n$, if $n \leq 128$, then $\psi(n) \leq \frac{133}{128} \cdot n$.

Here, $\psi(n)$ is the Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda(d)$ is the von Mangoldt function.

### Informal proof
The proof establishes a specific upper bound for the Chebyshev psi function for small values.

- First, the inequality $n \leq 128$ is rewritten as $n < 129$ using arithmetic rules.
- The proof then expands the cases for all natural numbers less than 129.
- It uses `PSI_LIST_300`, which contains pre-computed values of $\psi(n)$ for $n$ up to 300.
- The proof applies $\ln(1) = 0$ and performs rational number reductions.
- The main proof technique repeatedly applies a lemma that states: if $a \leq b$, $l \leq a$, and some other condition holds, then $l \leq a$, $l \leq b$, and that other condition holds.
- For each value of $n$, the proof verifies that $\psi(n) \leq \frac{133}{128} \cdot n$ by:
  - Computing rational values
  - Using `LN_N2_CONV` to convert logarithmic expressions
  - Performing real number calculations to check the inequality

The proof systematically verifies the bound for each value of $n$ from 1 to 128, ultimately showing that the inequality holds for all such values.

### Mathematical insight
This theorem establishes a tight linear upper bound on the Chebyshev psi function $\psi(n)$ for values up to 128. The Chebyshev function is important in number theory and relates to the distribution of prime numbers.

The bound $\psi(n) \leq \frac{133}{128} \cdot n \approx 1.0391 \cdot n$ is fairly tight and serves as a computational verification for this range of values. This type of bound is useful in analytic number theory, particularly in relation to the Prime Number Theorem.

The approach used here is computational - verifying the bound directly for each value rather than providing a general analytic proof. This is a common technique for obtaining concrete bounds over finite ranges.

### Dependencies
- **Theorems:**
  - `REAL_LE_TRANS`: Transitivity of less-than-or-equal relation on real numbers
  - `LN_1`: The natural logarithm of 1 equals 0
  - `LN_N2_CONV`: Conversion for natural logarithm expressions
- **Definitions:**
  - `psi`: The Chebyshev psi function defined as the sum of the Mangoldt function

### Porting notes
When porting this theorem to another system:
1. You'll need a pre-computed table of values for the Chebyshev psi function (referenced as `PSI_LIST_300`).
2. The proof relies heavily on computational verification using specific conversion tactics like `LN_N2_CONV` and `REALCALC_REL_CONV`. You may need to implement similar numerical computation capabilities.
3. Consider developing a more direct approach than case-by-case verification if your system has better support for numerical reasoning.

---

## PSI_UBOUND_128_LOG

### Name of formal statement
PSI_UBOUND_128_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_128_LOG = prove
 (`!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PSI_UBOUND_128) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV));;
```

### Informal statement
For all natural numbers $n$ such that $n \leq 128$, the Chebyshev function $\psi(n)$ is bounded above by:
$$\psi(n) \leq \left(\frac{3}{2} \cdot \ln(2)\right) \cdot n$$

### Informal proof
The proof establishes the desired upper bound for $\psi(n)$ by translating from a previously proven bound.

* Begin with the theorem `PSI_UBOUND_128`, which states that $\psi(n) \leq \frac{133}{128} \cdot n$ for $n \leq 128$.
* Show that $\frac{133}{128} \leq \frac{3}{2} \cdot \ln(2)$ using numerical calculation (performed by `REALCALC_REL_CONV`).
* Use transitivity of $\leq$ to conclude that $\psi(n) \leq \left(\frac{3}{2} \cdot \ln(2)\right) \cdot n$.

The proof relies on:
1. The previous upper bound from `PSI_UBOUND_128`
2. The fact that $n$ is non-negative (from `REAL_POS`)
3. Numerical verification that $\frac{133}{128} \leq \frac{3}{2} \cdot \ln(2)$

### Mathematical insight
This theorem provides a cleaner, more mathematical upper bound for Chebyshev's $\psi$ function in terms of the natural logarithm. The Chebyshev function $\psi(n)$ is defined as the sum of the von Mangoldt function $\Lambda(d)$ from 1 to $n$:

$$\psi(n) = \sum_{d=1}^n \Lambda(d)$$

While the previous bound $\psi(n) \leq \frac{133}{128} \cdot n$ is useful computationally, expressing the bound in terms of $\ln(2)$ connects it more directly to the Prime Number Theorem. The comment "As a multiple of log(2) is often more useful" suggests this reformulation provides a more natural mathematical expression that may simplify subsequent proofs or estimates.

For the Prime Number Theorem, the asymptotic behavior of $\psi(n)$ is $n$, so this theorem establishes that for $n \leq 128$, $\psi(n)$ is bounded by approximately $1.04 \cdot n$ (since $\frac{3}{2} \cdot \ln(2) \approx 1.04$).

### Dependencies
- Theorems:
  - `PSI_UBOUND_128`: Upper bound for $\psi(n)$ as $\frac{133}{128} \cdot n$ for $n \leq 128$
  - `REAL_POS`: For every natural number $n$, $0 \leq n$
  - `LN_N2_CONV`: Conversion for natural logarithm calculations

- Definitions:
  - `psi`: Chebyshev's second function defined as $\psi(n) = \sum_{d=1}^n \Lambda(d)$
  - `ln`: Natural logarithm defined as $\ln(x) = u$ such that $\exp(u) = x$

### Porting notes
When porting this theorem:
1. Ensure your system has a precise numerical calculation capability equivalent to `REALCALC_REL_CONV` to verify that $\frac{133}{128} \leq \frac{3}{2} \cdot \ln(2)$.
2. The theorem relies on previously established results about the Chebyshev function up to 128, so you'll need to port those results first.
3. The von Mangoldt function ($\Lambda$) and Chebyshev's $\psi$ function should be defined consistently with their mathematical definitions.

---

## OVERPOWER_LEMMA

### OVERPOWER_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OVERPOWER_LEMMA = prove
 (`!f g d a.
        f(a) <= g(a) /\
        (!x. a <= x ==> ((\x. g(x) - f(x)) diffl (d(x)))(x)) /\
        (!x. a <= x ==> &0 <= d(x))
        ==> !x. a <= x ==> f(x) <= g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. g(x) - f(x)`; `d:real->real`; `a:real`; `x:real`]
               MVT_ALT) THEN
  UNDISCH_TAC `a <= x` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `fa <= ga /\ &0 <= d ==> (gx - fx - (ga - fa) = d) ==> fx <= gx`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]);;
```

### Informal statement
For functions $f$, $g$, and $d$, and a real number $a$, if:
1. $f(a) \leq g(a)$,
2. For all $x \geq a$, the function $g(x) - f(x)$ is differentiable at $x$ with derivative $d(x)$, and
3. For all $x \geq a$, $d(x) \geq 0$,

Then for all $x \geq a$, $f(x) \leq g(x)$.

### Informal proof
The proof uses the Mean Value Theorem to establish that if the difference $g-f$ has a non-negative derivative, then the function $g-f$ is non-decreasing.

- Assume the premises and let $x \geq a$.
- Consider two cases:
  * If $x = a$, then $f(x) = f(a) \leq g(a) = g(x)$ by the first premise.
  * If $x > a$, apply the Mean Value Theorem (MVT_ALT) to the function $g-f$ on the interval $[a,x]$.
  
- By MVT_ALT, there exists $z \in (a,x)$ such that:
  $$(g(x) - f(x)) - (g(a) - f(a)) = (x-a) \cdot d(z)$$

- Since $x > a$, we have $x - a > 0$.
- By premise (3), $d(z) \geq 0$ since $z > a$.
- Therefore, $(x-a) \cdot d(z) \geq 0$ by the non-negativity of products of non-negative numbers.
- This implies $(g(x) - f(x)) - (g(a) - f(a)) \geq 0$
- Rearranging, $g(x) - f(x) \geq g(a) - f(a) \geq 0$ (since $f(a) \leq g(a)$)
- Therefore, $f(x) \leq g(x)$ for all $x \geq a$.

### Mathematical insight
This theorem is a formalization of an important principle in analysis: if a function's derivative is non-negative on an interval, then the function is non-decreasing on that interval. Here, we apply this principle to the difference $g-f$ to show that if $g-f$ has a non-negative derivative and $g-f$ is non-negative at a point, then $g-f$ remains non-negative for all greater points.

This result is particularly useful in proving inequalities between functions. It allows us to "overpower" one function with another by checking conditions at a single point and then using information about derivatives to extend the inequality to an entire interval. This technique is common in calculus and analysis when comparing functions.

### Dependencies
- Theorems:
  - `REAL_LE_LT`: For all real numbers $x$ and $y$, $x \leq y$ if and only if $x < y$ or $x = y$.
  - `REAL_LT_IMP_LE`: For all real numbers $x$ and $y$, if $x < y$ then $x \leq y$.
  - `REAL_LE_MUL`: For all real numbers $x$ and $y$, if $0 \leq x$ and $0 \leq y$, then $0 \leq x \cdot y$.
  - `REAL_SUB_LE`: For all real numbers $x$ and $y$, $0 \leq (x - y)$ if and only if $y \leq x$.
  - `MVT_ALT`: Mean Value Theorem (alternative formulation)

- Definitions:
  - `diffl`: Defines the derivative of a function at a point

### Porting notes
When implementing this theorem in other proof assistants:
1. The handling of differentiability might differ - some systems use a more structured approach to derivatives.
2. The formal statement relies on HOL Light's `diffl` predicate, which defines differentiability in terms of limits. Other systems may have different ways to express this concept.
3. The proof relies heavily on the Mean Value Theorem, so a similar formulation should be available in the target system.

---

## DOUBLE_CASES_RULE

### DOUBLE_CASES_RULE

### Type of the formal statement
- Rule (function)

### Formal Content
```ocaml
let DOUBLE_CASES_RULE th =
  let bod = snd(dest_forall(concl th)) in
  let ant,cons = dest_imp bod in
  let m = dest_numeral (rand ant)
  and c = rat_of_term (lhand(lhand(rand cons))) in
  let x = float_of_num(m +/ num 1) in
  let d = (4.0 *. log x +. 3.0) /. (x *. log 2.0) in
  let c' = c // num 2 +/ num 1 +/
           (floor_num(num_of_float(1024.0 *. d)) +/ num 2) // num 1024 in
  let c'' = max_num c c' in
  let tm = mk_forall
   (`n:num`,
    subst [mk_numeral(num 2 */ m),rand ant;
          term_of_rat c'',lhand(lhand(rand cons))] bod) in
  prove(tm,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (mk_comb(`(<=) (n:num)`,mk_numeral m)) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
    SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `pn2 <= ((a - &1) * l2) * n - logtm
      ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
    MP_TAC(SPEC `n DIV 2` th) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
      FIRST_ASSUM(UNDISCH_TAC o check ((not) o is_neg) o concl) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    W(fun (asl,w) ->
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `logtm <= ((c - a * b) * l2) * n
      ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `a <= n ==> a - &1 <= n - &1`)) THEN
    ABBREV_TAC `x = &n - &1` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    W(fun (asl,w) ->
        let th = DIFF_CONV
         (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
        MP_TAC th) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
      REAL_MUL_RID; REAL_MUL_LID] THEN
    W(fun (asl,w) ->
        let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
        DISCH_TAC THEN EXISTS_TAC tm) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
      CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
                 inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV);;
```

### Informal statement
`DOUBLE_CASES_RULE` is a specialized rule for extending the range of a theorem of a particular form. Given a theorem `th` of the form:

$$\forall n. n \leq m \Rightarrow P(n) \leq c \cdot \ln(2) \cdot n$$

it produces a new theorem of the form:

$$\forall n. n \leq 2m \Rightarrow P(n) \leq c' \cdot \ln(2) \cdot n$$

where $c'$ is a carefully calculated constant based on $c$, potentially larger than $c$, to accommodate the extended range.

### Informal proof
The proof works by using a case-based approach to extend the range of validity:

1. For the case where $n \leq m$, we directly apply the original theorem and use monotonicity properties to establish the result with the potentially larger constant $c'$.

2. For the case where $n > m$, we:
   - Apply the `PSI_BOUNDS_INDUCT` theorem to get bounds on $\psi(n)$ and $\psi(n) - \psi(n \div 2)$.
   - Apply the original theorem to $n \div 2$ (which is guaranteed to be $\leq m$).
   - Use real number inequalities to relate the recurrence relation between $\psi(n)$ and $\psi(n \div 2)$.
   - Apply the `OVERPOWER_LEMMA` to handle the difference between logarithmic functions.
   - Perform algebraic manipulations and calculus to establish the needed bounds.
   - Use differential calculus to analyze rate of growth.
   - Combine all these steps to show that the inductive bound holds for all $n \leq 2m$.

The proof combines recurrence relations, differential calculus, and careful numerical bounds to establish that the property extends to a larger range.

### Mathematical insight
This rule implements a bootstrapping approach to extending theorems about upper bounds. By using a recurrence relation and careful analysis of the growth rate, it allows doubling the range of applicability of certain inequalities.

This technique is particularly useful in analytic number theory when working with functions that have recurrence relations, such as the Chebyshev psi function $\psi(n)$. The rule carefully adjusts the constant factors to maintain the upper bound across the extended range.

The approach is a constructive implementation of induction with explicit constants, allowing concrete numerical bounds to be established for larger ranges without starting from scratch. It likely plays a role in Bertrand's postulate or other results about the distribution of prime numbers.

### Dependencies
- **Theorems**:
  - `REAL_MUL_RID`: $\forall x. x \cdot 1 = x$
  - `REAL_MUL_LZERO`: $\forall x. 0 \cdot x = 0$
  - `REAL_LE_TRANS`: $\forall x\,y\,z. x \leq y \land y \leq z \Rightarrow x \leq z$
  - `REAL_LE_MUL`: $\forall x\,y. 0 \leq x \land 0 \leq y \Rightarrow 0 \leq x \cdot y$
  - `REAL_SUB_LE`: $\forall x\,y. 0 \leq x - y \iff y \leq x$
  - `REAL_POS`: $\forall n. 0 \leq n$
  - `LN_POS`: $\forall x. 1 \leq x \Rightarrow 0 \leq \ln(x)$
  - `LN_N2_CONV`: A conversion for logarithm expressions
  - `PSI_BOUNDS_INDUCT`: A theorem providing bounds on the $\psi$ function
  - `OVERPOWER_LEMMA`: A lemma about functions with non-decreasing difference

### Porting notes
This rule is highly specialized for working with bounds on the Chebyshev psi function in analytic number theory. When porting:

1. The numerical calculation approach using floating-point arithmetic to determine constants may need adaptation, as different proof assistants handle computational aspects differently.

2. The proof uses several specialized conversions like `REAL_RAT_REDUCE_CONV`, `LN_N2_CONV`, and `REALCALC_REL_CONV` that perform symbolic and numerical calculations - equivalent tools would need to be found or implemented.

3. The proof heavily relies on manipulating terms using HOL Light's term structure. This aspect would need careful adaptation to other systems' term representation.

4. The core mathematical reasoning combines induction, recurrence relations, and calculus - these mathematical concepts should be available in most mature proof assistants, but the tactics to apply them will differ.

---

## PSI_UBOUND_1024_LOG

### PSI_UBOUND_1024_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_1024_LOG = funpow 3 DOUBLE_CASES_RULE PSI_UBOUND_128_LOG;;
```

### Informal statement
For all natural numbers $n \leq 1024$, the Chebyshev function $\psi(n)$ is bounded above by:

$$\psi(n) \leq \frac{3}{2} \cdot \ln(2) \cdot n$$

This provides an explicit upper bound on the Chebyshev function $\psi(n)$ for values of $n$ up to 1024.

### Informal proof
The theorem is proved by repeated application of the `DOUBLE_CASES_RULE` to the theorem `PSI_UBOUND_128_LOG`.

The `funpow 3 DOUBLE_CASES_RULE` applies the `DOUBLE_CASES_RULE` three times to the theorem `PSI_UBOUND_128_LOG`.

Each application of `DOUBLE_CASES_RULE` doubles the range of validity of the bound:
- `PSI_UBOUND_128_LOG` gives the bound for $n \leq 128$
- First application extends it to $n \leq 256$
- Second application extends it to $n \leq 512$
- Third application extends it to $n \leq 1024$

The theorem can be seen as a repeated doubling of the upper limit for which the bound on $\psi(n)$ holds, without changing the actual bound $\frac{3}{2} \cdot \ln(2) \cdot n$.

### Mathematical insight
This theorem is part of a series of results leading to Chebyshev's bounds on the prime counting function and ultimately to the Prime Number Theorem. The Chebyshev function $\psi(n) = \sum_{p^k \leq n} \ln(p)$ (where the sum is over all prime powers not exceeding $n$) is closely related to the distribution of primes.

The bound $\psi(n) \leq \frac{3}{2} \cdot \ln(2) \cdot n$ for $n \leq 1024$ is an explicit numerical result that helps establish asymptotic properties of $\psi(n)$. This specific bound of $\frac{3}{2} \cdot \ln(2) \approx 1.04$ is not optimal but is sufficient for proving Bertrand's postulate and similar results.

The theorem extends the bound from $n \leq 128$ to $n \leq 1024$ through repeated application of a doubling rule, which is a common technique for extending bounds in number theory.

### Dependencies
- `PSI_UBOUND_128_LOG`: Establishes that for all $n \leq 128$, $\psi(n) \leq \frac{3}{2} \cdot \ln(2) \cdot n$
- `DOUBLE_CASES_RULE`: A rule that doubles the range of validity for certain bounds
- `funpow`: Function that applies a given function a specified number of times

### Porting notes
When porting this theorem:
1. Ensure that the target system has a definition for the Chebyshev function $\psi(n)$
2. First port the dependency `PSI_UBOUND_128_LOG`
3. Implement or port a version of `DOUBLE_CASES_RULE` that can extend bounds
4. Either implement the functional `funpow` or manually apply the doubling rule three times
5. Most proof assistants would likely require a more explicit proof showing how the bound extends from 128 to 256, 512, and then 1024

---

## PSI_BOUNDS_SUSTAINED_INDUCT

### PSI_BOUNDS_SUSTAINED_INDUCT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_BOUNDS_SUSTAINED_INDUCT = prove
 (`&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j) /\
   &4 / (&1 + &2 pow j) <= d * ln(&2) /\ &0 <= c /\ c / &2 + d + &1 <= c
   ==> !k. j <= k /\
           (!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
           ==> !n. n <= 2 EXP (SUC k) ==> psi(n) <= (c * ln(&2)) * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n <= 2 EXP k` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
  SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `!a. ~(a = 0) /\ ~(n <= a) ==> ~(n = 0)`) THEN
    EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `pn2 <= ((a - &1) * l2) * n - logtm
    ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `n <= 2 * k ==> n < 2 * (k + 1)`) THEN
    ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  W(fun (asl,w) ->
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `logtm <= ((c - a * b) * l2) * n
    ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(d * ln (&2)) * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_REWRITE_TAC[REAL_ARITH `d <= c - &1 - c2 <=> c2 + d + &1 <= c`]] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  SUBGOAL_THEN `&2 pow j <= &n - &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow k` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = &n - &1` THEN SPEC_TAC(`x:real`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= x ==> &0 < &1 + x`) THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; REAL_ARITH
     `&0 < x ==> &0 < &1 + x`];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;
```

### Informal statement

For fixed constants $j$, $c$, and $d$, if the following conditions hold:
1. $4 \cdot \ln(1 + 2^j) + 3 \leq (d \cdot \ln(2)) \cdot (1 + 2^j)$
2. $\frac{4}{1 + 2^j} \leq d \cdot \ln(2)$
3. $0 \leq c$
4. $\frac{c}{2} + d + 1 \leq c$

Then, for all $k$ such that $j \leq k$, if $\psi(n) \leq (c \cdot \ln(2)) \cdot n$ for all $n \leq 2^k$, then $\psi(n) \leq (c \cdot \ln(2)) \cdot n$ for all $n \leq 2^{k+1}$.

Here $\psi(n)$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the von Mangoldt function.

### Informal proof

We need to prove that if $\psi(n) \leq (c \cdot \ln(2)) \cdot n$ holds for all $n \leq 2^k$, then it also holds for all $n \leq 2^{k+1}$.

For $n \leq 2^k$, the result holds directly by our assumption. Let's focus on the case where $2^k < n \leq 2^{k+1}$.

First, we observe that $n \neq 0$ since $n > 2^k \geq 2^j > 0$.

From `PSI_BOUNDS_INDUCT`, we have:
$$\psi(n) - \psi(n \text{ DIV } 2) \leq n \cdot \ln(2) + (4 \cdot \ln(n) + 3)$$

Let's call the term $(4 \cdot \ln(n) + 3)$ as $\text{logtm}$. Then we want to prove:
$$\psi(n) \leq (c \cdot \ln(2)) \cdot n$$

This can be rewritten as:
$$\psi(n) \leq \psi(n \text{ DIV } 2) + (n \cdot \ln(2) + \text{logtm}) \leq (c \cdot \ln(2)) \cdot n$$

Since $n \text{ DIV } 2 \leq 2^k$, we can apply our induction hypothesis:
$$\psi(n \text{ DIV } 2) \leq (c \cdot \ln(2)) \cdot (n \text{ DIV } 2) \leq (c \cdot \ln(2)) \cdot \frac{n}{2}$$

So, we need to show:
$$(c \cdot \ln(2)) \cdot \frac{n}{2} + (n \cdot \ln(2) + \text{logtm}) \leq (c \cdot \ln(2)) \cdot n$$

Which simplifies to:
$$\text{logtm} \leq ((c - \frac{c}{2} - 1) \cdot \ln(2)) \cdot n = ((c - \frac{c}{2} - 1) \cdot \ln(2)) \cdot n$$

We want to show $\text{logtm} \leq (d \cdot \ln(2)) \cdot n$, because we know from our assumptions that $d \leq c - \frac{c}{2} - 1$.

Let's rewrite $n = 1 + (n - 1)$. Since $n > 2^k \geq 2^j$, we have $n - 1 \geq 2^j$, so we can substitute $x = n - 1$ and show:
$$\text{logtm} \leq (d \cdot \ln(2)) \cdot (1 + x)$$

For $x \geq 2^j$, we know that $4 \cdot \ln(1 + 2^j) + 3 \leq (d \cdot \ln(2)) \cdot (1 + 2^j)$.

Using `OVERPOWER_LEMMA`, we can show that if:
- $f(a) \leq g(a)$
- $\frac{d}{dx}(g(x) - f(x)) \geq 0$ for all $x \geq a$

Then $f(x) \leq g(x)$ for all $x \geq a$.

In our case:
- $f(x) = 4 \cdot \ln(1 + x) + 3$
- $g(x) = (d \cdot \ln(2)) \cdot (1 + x)$
- $a = 2^j$

We calculate $\frac{d}{dx}(g(x) - f(x))$ and verify it's non-negative for $x \geq 2^j$:
$$\frac{d}{dx}(g(x) - f(x)) = d \cdot \ln(2) - \frac{4}{1 + x}$$

Since $x \geq 2^j$, we have $\frac{4}{1 + x} \leq \frac{4}{1 + 2^j} \leq d \cdot \ln(2)$ by our assumption.

Therefore, $\text{logtm} \leq (d \cdot \ln(2)) \cdot n$, which completes the proof.

### Mathematical insight

This theorem establishes a crucial inductive step in studying the growth of the Chebyshev $\psi$ function. The key insight is showing that if we have an upper bound for $\psi(n)$ up to a certain power of 2, then we can extend that bound to the next power of 2 under certain conditions on the constants involved.

The proof technique applies differential calculus to compare the growth rates of functions. It uses the properties of logarithmic functions and the fact that the $\psi$ function satisfies certain bounds related to the summatory von Mangoldt function.

This result is part of the machinery used in proving results like Bertrand's postulate and ultimately connects to the Prime Number Theorem. The careful choice of constants $c$ and $d$ establishes a self-sustaining inductive bound, which is crucial for controlling the growth of prime-counting functions.

### Dependencies

**Theorems:**
- `REAL_MUL_RID`: $\forall x. x \times 1 = x$
- `REAL_MUL_LZERO`: $\forall x. 0 \times x = 0$
- `REAL_LE_TRANS`: $\forall x~y~z. x \leq y \land y \leq z \Rightarrow x \leq z$
- `REAL_LE_MUL`: $\forall x~y. 0 \leq x \land 0 \leq y \Rightarrow 0 \leq (x \times y)$
- `REAL_LE_LADD`: $\forall x~y~z. (x + y) \leq (x + z) \iff y \leq z$
- `REAL_SUB_LE`: $\forall x~y. 0 \leq (x - y) \iff y \leq x$
- `REAL_POS`: $\forall n. 0 \leq n$
- `LN_POS`: $\forall x. 1 \leq x \Rightarrow 0 \leq \ln(x)$
- `PSI_BOUNDS_INDUCT`: Bounds on $\psi(n)$ and $\psi(n) - \psi(n \text{ DIV } 2)$
- `OVERPOWER_LEMMA`: A calculus-based comparison principle for functions

**Definitions:**
- `ln`: The natural logarithm function
- `psi`: The second Chebyshev function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Porting notes

When porting this theorem:
1. Ensure your system has a good library for real analysis, including properties of logarithms.
2. The proof relies heavily on calculus techniques (derivatives and function comparison), so equivalent tools should be available.
3. The Chebyshev $\psi$ function should be properly defined using the von Mangoldt function.
4. The theorem involves several algebraic manipulations and inequalities, which may require additional lemmas in some proof assistants.
5. The use of `OVERPOWER_LEMMA` is crucial - make sure an equivalent result is available or can be proved in your target system.

---

## PSI_BOUNDS_SUSTAINED

### Name of formal statement
PSI_BOUNDS_SUSTAINED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_BOUNDS_SUSTAINED = prove
 (`(!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
   ==> &4 * ln(&1 + &2 pow k) + &3
         <= ((c / &2 - &1) * ln(&2)) * (&1 + &2 pow k) /\
       &4 / (&1 + &2 pow k) <= (c / &2 - &1) * ln(&2) /\ &0 <= c
           ==> !n. psi(n) <= (c * ln(&2)) * &n`,
  let lemma = prove
   (`c / &2 + (c / &2 - &1) + &1 <= c`,
    REWRITE_TAC[REAL_ARITH `c2 + (c2 - &1) + &1 = &2 * c2`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LE_REFL]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ lemma) THEN
  ABBREV_TAC `d = c / &2 - &1` THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED_INDUCT) THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `?j. m <= 2 EXP j` MP_TAC THENL
   [EXISTS_TAC `m:num` THEN SPEC_TAC(`m:num`,`m:num`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[EXP] THEN MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ m <= a ==> SUC m <= 2 * a`) THEN
    ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`m:num`,`m:num`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `k <= j:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (SUC j) <= 2 EXP k`
   (fun th -> ASM_MESON_TAC[th; LE_TRANS]) THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH] THEN
  UNDISCH_TAC `~(k <= j:num)` THEN ARITH_TAC);;
```

### Informal statement
The theorem states that if for all numbers $n \leq 2^k$, we have $\psi(n) \leq (c \cdot \ln(2)) \cdot n$, and if the following conditions are satisfied:
- $4 \cdot \ln(1 + 2^k) + 3 \leq ((c/2 - 1) \cdot \ln(2)) \cdot (1 + 2^k)$
- $4 / (1 + 2^k) \leq (c/2 - 1) \cdot \ln(2)$
- $0 \leq c$

Then for all natural numbers $n$, we have $\psi(n) \leq (c \cdot \ln(2)) \cdot n$.

Here, $\psi(n)$ is the Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the von Mangoldt function.

### Informal proof
The proof proceeds as follows:

- First, a lemma is established: $c/2 + (c/2 - 1) + 1 \leq c$. This is proven by simplifying the left side to $2 \cdot c/2 = c$, resulting in $c \leq c$, which is true by reflexivity.

- We then define $d = c/2 - 1$ and apply the induction theorem `PSI_BOUNDS_SUSTAINED_INDUCT` using our conditions and the lemma.

- For any arbitrary number $m$, we prove that there exists some $j$ such that $m \leq 2^j$. This is shown by taking $j = m$ and using induction:
  * Base case: For $m = 0$, we have $0 \leq 2^0 = 1$.
  * Inductive step: If $m \leq 2^m$, then $m+1 \leq 2 \cdot 2^m = 2^{m+1}$, since $2^m \neq 0$.

- The proof then proceeds by induction on $j$:
  * Base case ($j = 0$): If $m \leq 2^0 = 1$, we use our original assumption to conclude $\psi(m) \leq (c \cdot \ln(2)) \cdot m$.
  * Inductive step: If $k \leq j$, we can use the induction hypothesis directly. Otherwise, we have $j < k$, which implies $2^{j+1} \leq 2^k$. This allows us to use the original assumption through transitivity to conclude $\psi(m) \leq (c \cdot \ln(2)) \cdot m$.

### Mathematical insight
This theorem extends a bound on the Chebyshev function $\psi(n)$ from numbers up to $2^k$ to all natural numbers, given certain conditions on the constant $c$. The Chebyshev function $\psi(n)$ sums the von Mangoldt function up to $n$ and is related to the distribution of prime numbers.

The key insight is that if we have a bound for $\psi(n)$ up to a certain power of 2, and if certain conditions involving logarithmic bounds are satisfied, then the bound can be extended to all natural numbers. This is a form of a "sustained" bound, meaning it holds indefinitely once established up to a certain threshold.

This result is part of the machinery used in proving results about the asymptotic distribution of prime numbers, such as Bertrand's postulate or the Prime Number Theorem.

### Dependencies
- **Theorems**:
  - `REAL_LE_REFL`: For all real numbers $x$, $x \leq x$.
  - `PSI_BOUNDS_SUSTAINED_INDUCT`: An induction principle for extending bounds on the Chebyshev function.

- **Definitions**:
  - `ln`: The natural logarithm function.
  - `psi`: The Chebyshev function defined as the sum of the von Mangoldt function.

### Porting notes
- The proof relies on properties of real numbers and the natural logarithm, which should have equivalents in most proof assistants.
- The definition of the Chebyshev function $\psi(n)$ and the von Mangoldt function need to be ported first.
- The induction principle `PSI_BOUNDS_SUSTAINED_INDUCT` is a key component and must be ported or proven in the target system.

---

## PSI_UBOUND_LOG

### Name of formal statement
PSI_UBOUND_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_LOG = prove
 (`!n. psi(n) <= (&4407 / &2048 * ln (&2)) * &n`,
  MP_TAC PSI_UBOUND_1024_LOG THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 10`)) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV);;
```

### Informal statement
For all natural numbers $n$, the function $\psi(n)$ (the second Chebyshev function) satisfies the following upper bound:
$$\psi(n) \leq \left(\frac{4407}{2048} \cdot \ln(2)\right) \cdot n$$

Here, $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ where $\Lambda$ is the von Mangoldt function.

### Informal proof
The proof establishes an explicit numerical upper bound on the second Chebyshev function $\psi(n)$.

* We start with the theorem `PSI_UBOUND_1024_LOG`, which provides a bound for $\psi(n)$ when $n \leq 2^{10} = 1024$.

* We substitute $2^{10}$ for its numerical value 1024 using `SYM(NUM_REDUCE_CONV `2 EXP 10`)`.

* Next, we apply `PSI_BOUNDS_SUSTAINED`, which extends bounds from $\psi(n)$ for $n \leq 2^k$ to bounds valid for all $n$. This theorem requires verifying certain inequalities involving the constant $c$ where $\psi(n) \leq (c \cdot \ln(2)) \cdot n$.

* The rational constant $\frac{4407}{2048}$ is reduced to its simplified form.

* The logarithm term is simplified using `LN_N2_CONV`, which handles logarithms of numbers conveniently.

* Finally, we verify that the numerical inequalities required by `PSI_BOUNDS_SUSTAINED` are satisfied using real number calculation conversions.

### Mathematical insight
This theorem provides an explicit upper bound on the second Chebyshev function $\psi(n)$, which is crucial in analytic number theory, especially in the study of the distribution of prime numbers. The bound $\psi(n) \leq \frac{4407}{2048} \cdot \ln(2) \cdot n$ (approximately $1.5 \cdot n$) is sharper than many classical bounds and is particularly useful in concrete applications.

The second Chebyshev function $\psi(n)$ counts primes with weights according to their powers, and its asymptotic behavior is closely related to the Prime Number Theorem. Having explicit numerical bounds (rather than just asymptotic ones) is valuable for computational applications and explicit estimates in number theory.

### Dependencies
- **Theorems:**
  - `PSI_UBOUND_1024_LOG`: Provides an upper bound for $\psi(n)$ when $n \leq 2^{10}$
  - `PSI_BOUNDS_SUSTAINED`: Extends bounds from $\psi(n)$ for $n \leq 2^k$ to bounds valid for all $n$
  - `LN_N2_CONV`: Conversion for handling logarithms of numbers

- **Definitions:**
  - `psi`: The second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$
  - `ln`: The natural logarithm function

### Porting notes
When porting this theorem, special attention should be paid to:

1. The representation of real constants like $\frac{4407}{2048}$
2. The automation for verifying numerical inequalities (equivalent to `REALCALC_REL_CONV`)
3. Implementation of the Chebyshev function $\psi$ and von Mangoldt function $\Lambda$

In systems with strong automation for real arithmetic, the verification of the numerical inequalities may be more straightforward than in HOL Light.

---

## PSI_UBOUND_3_2

### PSI_UBOUND_3_2
- `PSI_UBOUND_3_2`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_UBOUND_3_2 = prove
 (`!n. psi(n) <= &3 / &2 * &n`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4407 / &2048 * ln (&2)) * &n` THEN
  REWRITE_TAC[PSI_UBOUND_LOG] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONV_TAC REALCALC_REL_CONV);;
```

### Informal statement
For all natural numbers $n$, the Chebyshev psi function satisfies the upper bound:
$$\psi(n) \leq \frac{3}{2} \cdot n$$

Where $\psi(n) = \sum_{d=1}^n \Lambda(d)$ and $\Lambda(d)$ is the von Mangoldt function.

### Informal proof
The proof establishes the bound $\psi(n) \leq \frac{3}{2} \cdot n$ by the following steps:

* Apply transitivity of the real ordering relation (using `REAL_LE_TRANS`).
* Show $\psi(n) \leq \frac{4407}{2048} \cdot \ln(2) \cdot n$ using the theorem `PSI_UBOUND_LOG`.
* Show that $\frac{4407}{2048} \cdot \ln(2) \cdot n \leq \frac{3}{2} \cdot n$ by:
  * Using `REAL_LE_RMUL` to factor out $n$, which is non-negative by `REAL_POS`
  * Converting the logarithm expression using `LN_N2_CONV`
  * Using numerical calculation (`REALCALC_REL_CONV`) to verify that $\frac{4407}{2048} \cdot \ln(2) \leq \frac{3}{2}$

### Mathematical insight
This theorem provides a simple upper bound for the Chebyshev psi function, which is the sum of the von Mangoldt function over all positive integers up to $n$. The von Mangoldt function $\Lambda(d)$ equals $\log(p)$ when $d = p^k$ for some prime $p$ and positive integer $k$, and equals 0 otherwise.

The bound $\psi(n) \leq \frac{3}{2} \cdot n$ is significant in analytic number theory, particularly in the study of the distribution of prime numbers. It's a refinement of previously established bounds and is useful in prime number theorems and related results.

The theorem represents a stronger and cleaner bound compared to the more complex expression $\frac{4407}{2048} \cdot \ln(2) \cdot n$ used in the intermediate result `PSI_UBOUND_LOG`.

### Dependencies
- **Theorems**:
  - `REAL_LE_TRANS`: Transitivity of the real less-than-or-equal relation
  - `REAL_POS`: Non-negativity of natural numbers embedded in reals
  - `PSI_UBOUND_LOG`: Upper bound on $\psi(n)$ involving logarithm
  - `REAL_LE_RMUL`: Monotonicity of multiplication for the real less-than-or-equal relation

- **Definitions**:
  - `psi`: The Chebyshev psi function defined as the sum of the von Mangoldt function
  - `ln`: The natural logarithm function

- **Conversions**:
  - `LN_N2_CONV`: Conversion for logarithmic expressions
  - `REALCALC_REL_CONV`: Calculator for real number relation checking

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the Chebyshev psi function and von Mangoldt function are correctly defined
2. The numerical verification that $\frac{4407}{2048} \cdot \ln(2) \leq \frac{3}{2}$ may require different approaches depending on the numerical calculation capabilities of the target system
3. The intermediate bound from `PSI_UBOUND_LOG` might need to be proven separately if not already available

---

## PSI_LBOUND_3_5

### PSI_LBOUND_3_5
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_LBOUND_3_5 = prove
 (`!n. 4 <= n ==> &3 / &5 * &n <= psi(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  GEN_TAC THEN ASM_CASES_TAC `n < 300` THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC(PSI_LIST_300) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(CONJUNCT1 (SPEC `n:num` PSI_BOUNDS_INDUCT)) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < 300) ==> ~(n = 0)`] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= n * (b - a) ==> a * n <= n * b - c`) THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &11 * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[real_sub] THEN CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV] THEN
  ABBREV_TAC `x = &n - &1` THEN
  SUBGOAL_THEN `&n = &1 + x` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&299 <= x` MP_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; ARITH] THEN
    UNDISCH_TAC `~(n < 300)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&1 + &299)` THEN CONJ_TAC THENL
   [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n \geq 4$, we have:
$$\frac{3}{5} \cdot n \leq \psi(n)$$

where $\psi(n)$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, with $\Lambda$ being the von Mangoldt function.

### Informal proof
The proof proceeds by considering two cases: $n < 300$ and $n \geq 300$.

For $n < 300$:
- The proof uses a computational approach, applying `PSI_LIST_300` to obtain exact values of $\psi(n)$ for $n < 300$.
- Each value is checked against the bound $\frac{3}{5} \cdot n$ using numerical calculations.

For $n \geq 300$:
- We use the lower bound for $\psi(n)$ from `PSI_BOUNDS_INDUCT`:
  $$n \cdot \ln(2) - (4 \cdot \ln(n) + 3) \leq \psi(n)$$
  
- The goal is to show this lower bound exceeds $\frac{3}{5} \cdot n$, which reduces to proving:
  $$\frac{1}{11} \cdot n \leq n \cdot (\ln(2) - \frac{3}{5})$$
  
- Let $x = n - 1$, so that $n = 1 + x$ with $x \geq 299$ (since $n \geq 300$).
  
- The proof applies `OVERPOWER_LEMMA`, which is a calculus result about preserving inequalities when a derivative is non-negative.
  
- It's shown that $\frac{1}{1+x} \leq \frac{1}{11}$ for $x \geq 299$, which completes the proof.

### Mathematical insight
This theorem establishes an important lower bound on the second Chebyshev function $\psi(n)$. The bound $\frac{3}{5} \cdot n \leq \psi(n)$ for $n \geq 4$ is significant in analytic number theory, particularly in the study of the distribution of prime numbers.

The proof technique is interesting as it combines:
1. Direct computation for small values ($n < 300$)
2. Analytical techniques for larger values, using properties of the logarithm function and calculus

This result is part of a family of bounds on the Chebyshev functions that lead toward proving the Prime Number Theorem and related results such as Bertrand's postulate.

### Dependencies
- Definitions:
  - `psi`: The second Chebyshev function defined as the sum of von Mangoldt function values
  
- Theorems:
  - `PSI_BOUNDS_INDUCT`: Provides bounds relating $\psi(n)$ to $n \cdot \ln(2)$ and logarithmic terms
  - `OVERPOWER_LEMMA`: A calculus result about preserving inequalities when a derivative is non-negative
  - `LN_N2_CONV`: Conversion for logarithm expressions
  - `PSI_LIST_300`: List of exact values of $\psi(n)$ for $n < 300$ (implied in the proof)
  - Basic real number theorems: `REAL_MUL_RID`, `REAL_MUL_LZERO`, `REAL_LE_TRANS`, etc.

### Porting notes
- This proof relies heavily on computation for the case $n < 300$. When porting to another system, you'll need to:
  1. Implement or import the Chebyshev function $\psi$ 
  2. Pre-compute values for small $n$ or find an efficient way to calculate them
  3. Implement appropriate numerical calculation tactics for the analytical part of the proof
- The analytical part uses calculus and real analysis, so a system with good support for these areas would make the port easier.

---

## theta

### theta
- `theta`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let theta = new_definition
  `theta(n) = sum(1,n) (\p. if prime p then ln(&p) else &0)`;;
```

### Informal statement
The function $\theta(n)$ is defined as the sum of natural logarithms of all prime numbers $p$ from $1$ to $n$:

$$\theta(n) = \sum_{i=1}^{n} \begin{cases} \ln(p) & \text{if $i$ is prime} \\ 0 & \text{otherwise} \end{cases}$$

where $\ln(p)$ denotes the natural logarithm of $p$.

### Informal proof
This is a definition, so no proof is needed.

### Mathematical insight
The function $\theta(n)$ is the Chebyshev theta function, a key function in analytic number theory. It represents the logarithmic weight of prime numbers up to $n$ and plays a crucial role in the study of the distribution of prime numbers.

The Chebyshev theta function is closely related to the Prime Number Theorem. In fact, proving that $\theta(n) \sim n$ (meaning $\theta(n)/n \to 1$ as $n \to \infty$) is equivalent to the Prime Number Theorem.

The definition sums the logarithm of primes up to $n$, which effectively gives us a measure of how many primes there are up to $n$, with each prime weighted by its logarithm. This weighting turns out to be natural in many number-theoretic contexts.

### Dependencies
- Definitions:
  - `ln`: The natural logarithm function defined as `ln x = @u. exp(u) = x`
  - `sum`: The summation function for real-valued sequences
- Theorems:
  - `sum`: Basic properties of the summation function

### Porting notes
When porting to other systems:
1. Ensure that the natural logarithm function (`ln`) is properly defined
2. Make sure the summation operator has similar recursive behavior
3. The definition uses an if-then-else construction to filter prime numbers - validate that your target system handles this idiom correctly
4. Note that in HOL Light, `&p` represents the injection from natural numbers to real numbers, so ensure this conversion is handled appropriately in the target system

---

## THETA_LIST

### THETA_LIST

### Type of the formal statement
Function definition with auxiliary theorems

### Formal Content
```ocaml
let THETA_LIST =
  let THETA_0 = prove
   (`theta(0) = ln(&1)`,
    REWRITE_TAC[theta; sum; LN_1])
  and THETA_SUC = prove
   (`theta(SUC n) = theta(n) + (if prime(SUC n) then ln(&(SUC n)) else &0)`,
    REWRITE_TAC[theta; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [COND_CLAUSES; REAL_ADD_LID; REAL_ADD_RID] THENC
    SIMP_CONV [GSYM LN_MUL; REAL_OF_NUM_MUL; REAL_OF_NUM_LT; ARITH] in
  let rec THETA_LIST n =
    if n = 0 then [THETA_0] else
    let ths = THETA_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] THETA_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  THETA_LIST;;
```

### Informal statement
`THETA_LIST` is a recursive function that computes a list of theorems about the function $\theta(n)$ for natural numbers $n$. The function $\theta(n)$ is defined as:

$$\theta(n) = \sum_{p=1}^{n} \begin{cases} \ln(p) & \text{if } p \text{ is prime} \\ 0 & \text{otherwise} \end{cases}$$

The function uses two key theorems:
1. $\theta(0) = \ln(1)$
2. $\theta(n+1) = \theta(n) + \begin{cases} \ln(n+1) & \text{if } (n+1) \text{ is prime} \\ 0 & \text{otherwise} \end{cases}$

When `THETA_LIST n` is called with a natural number $n$, it returns a list of theorems corresponding to $\theta(0)$ through $\theta(n)$, with $\theta(n)$ at the head of the list.

### Informal proof
The implementation uses two auxiliary theorems that are proved first:

1. `THETA_0`: Shows $\theta(0) = \ln(1)$
   - Proved by expanding the definitions of $\theta$ and sum, and applying `LN_1` (which states $\ln(1) = 0$)

2. `THETA_SUC`: Shows $\theta(n+1) = \theta(n) + \begin{cases} \ln(n+1) & \text{if } (n+1) \text{ is prime} \\ 0 & \text{otherwise} \end{cases}$
   - Proved by expanding the definitions of $\theta$ and sum, using `ADD1` and associativity/commutativity properties of addition

The main `THETA_LIST` function works recursively:
- Base case: For $n = 0$, it returns `[THETA_0]`
- Recursive case: For $n > 0$
  1. Recursively obtain theorems for $n-1$
  2. Instantiate `THETA_SUC` with $n-1$
  3. Use the theorem for $\theta(n-1)$ to rewrite the left side of the equation
  4. Apply a conversion (`SIMPER_CONV`) to simplify the result, which:
     - Reduces numeric expressions
     - Evaluates primality 
     - Simplifies conditional expressions
     - Applies logarithm properties to combine terms
  5. Add the new theorem to the head of the list

This recursive approach builds a list of theorems about $\theta$ values efficiently.

### Mathematical insight
This implementation provides an optimized way to generate theorems about $\theta(n)$ for all values up to some bound. The function $\theta(n)$ is important in number theory, especially in the study of prime distribution. It represents the sum of logarithms of primes less than or equal to $n$.

The recursive structure is carefully designed for efficiency:
- It reuses previously computed theorems in the construction of new ones
- The `SIMPER_CONV` conversion simplifies expressions at each step
- The resulting theorems are stored in a list, making them easily accessible

This approach is more efficient than proving each $\theta(n)$ independently, as it builds upon previous results.

### Dependencies
- **Definitions**:
  - `theta`: Definition of the function summing logarithms of primes
  - `ln`: Natural logarithm definition
  
- **Theorems**:
  - `sum`: Properties of summation
  - `LN_MUL`: Logarithm of product property
  - `LN_1`: Theorem stating ln(1) = 0
  - Support theorems: `ADD1`, `ADD_AC`, `COND_CLAUSES`, `REAL_ADD_LID`, `REAL_ADD_RID`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_LT`, `ARITH`

### Porting notes
When porting this to another system:
1. Ensure the target system has a good representation of the theta function summing logarithms of primes
2. The conversion `SIMPER_CONV` combines multiple simplification steps that may need to be replicated differently in another system
3. The recursive theorem generation approach relies on HOL Light's ability to manipulate theorems as first-class objects, which might need adaptation in systems with different metaprogramming capabilities
4. The primality check (`PRIME_CONV`) would need an equivalent implementation in the target system

---

## PRIMEPOW_ODD_EVEN

### Name of formal statement
PRIMEPOW_ODD_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_ODD_EVEN = prove
 (`!p q j k.
     ~(prime(p) /\ prime(q) /\ 1 <= j /\ (p EXP (2 * j) = q EXP (2 * k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * j` THEN
    UNDISCH_TAC `p EXP (2 * j) = q EXP (2 * k + 1)` THEN
    REWRITE_TAC[EXP_ADD; EXP_1] THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `p EXP (2 * j) = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p = 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[LE_ANTISYM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]);;
```

### Informal statement
For all prime numbers $p$ and $q$, and for all integers $j$ and $k$ where $j \geq 1$, it is impossible to have $p^{2j} = q^{2k+1}$.

### Informal proof
The proof establishes that an even power of a prime cannot equal an odd power of another prime through the following steps:

* Assume we have primes $p$ and $q$, integers $j \geq 1$ and $k$ such that $p^{2j} = q^{2k+1}$.
* First, we show that $q$ divides $p$:
  * From $p^{2j} = q^{2k+1}$, we have $q^{2k+1}$ divides $p^{2j}$
  * Using `PRIME_DIVEXP`, if a prime divides a power, it must divide the base
  * Therefore, $q$ divides $p$

* Since $q$ divides $p$ and both are prime, we must have $q = p$
* The equation becomes $p^{2j} = p^{2k+1}$
* Taking logarithms (implicitly), this means $2j = 2k+1$
* But this is impossible because:
  * The left side ($2j$) is even
  * The right side ($2k+1$) is odd
  * An even number cannot equal an odd number

Therefore, no such $p$, $q$, $j$, and $k$ can exist, proving the theorem.

### Mathematical insight
This theorem demonstrates the fundamental number-theoretic principle that the parity of exponents carries important information when dealing with prime powers. Specifically, it shows that a number cannot be simultaneously an even power of one prime and an odd power of another prime.

The result is a special case of the unique prime factorization theorem. If we had $p^{2j} = q^{2k+1}$, then comparing the prime factorizations of both sides would lead to a contradiction, as the exponent of each prime in a prime factorization is unique.

This theorem might be used in number theory proofs involving perfect powers, Diophantine equations, or when analyzing properties of numbers expressible as powers in different ways.

### Dependencies
- Theorems:
  - `PRIME_0`: Prime numbers are not zero
  - `PRIME_1`: One is not a prime number
  - `PRIME_DIVEXP`: If a prime $p$ divides $x^n$, then $p$ divides $x$

### Porting notes
When porting this theorem:
- The proof relies heavily on the fact that even and odd numbers are different, which is represented differently in various proof assistants
- The proof uses several number theory theorems about primes and divisibility, so ensure these are available in the target system
- The reasoning about the parity of exponents (even vs. odd) may require different tactics in other systems

---

## PSI_SPLIT

### Name of formal statement
PSI_SPLIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_SPLIT = prove
 (`psi(n) = theta(n) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                          then ln(&(aprimedivisor d)) else &0) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                          then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi; theta; GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))) /\
                  ~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k + 1))) /\
                  ~(prime r)`
     (fun th -> REWRITE_TAC[th; REAL_ADD_LID]) THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`;
                  EXP_1; LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `m:num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`k = m DIV 2`; `d = m MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `d < 2 ==> (d = 0) \/ (d = 1)`)) THEN
  ASM_REWRITE_TAC[PRIME_EXP; ADD_EQ_0; MULT_EQ_0; ARITH_EQ] THENL
   [UNDISCH_TAC `1 <= k * 2 + 0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k * 2 = 1)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
    ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM;
                  ARITH_RULE `~(k = 0) ==> 1 <= k`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [MATCH_MP_TAC(REAL_ARITH
     `(a = a') /\ (b = &0) /\ (c = &0) ==> (a = a' + b + c)`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH; EXP_1]; ALL_TAC] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
     [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k * 2 + 1` THEN
      UNDISCH_TAC `p EXP (k * 2 + 1) = q EXP (2 * j + 1)` THEN
      REWRITE_TAC[EXP_ADD; EXP_1] THEN
      ASM_MESON_TAC[divides; MULT_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    UNDISCH_TAC `p EXP (k * 2 + 1) = p EXP (2 * j + 1)` THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[LE_ANTISYM] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(1 = 2 * j + 1)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k * 2 + 1 = 1) <=> (k = 0)`; ARITH_EQ] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
  ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM; ARITH_RULE
   `~(k = 0) ==> 1 <= k`]);;
```

### Informal statement
The theorem decomposes the Chebyshev $\psi$ function into three components:

$$\psi(n) = \theta(n) + \sum_{d=1}^n \left[ \begin{cases} \ln(p) & \text{if } d = p^{2k} \text{ for some prime } p \text{ and } k \geq 1 \\ 0 & \text{otherwise} \end{cases}\right] + \sum_{d=1}^n \left[ \begin{cases} \ln(p) & \text{if } d = p^{2k+1} \text{ for some prime } p \text{ and } k \geq 1 \\ 0 & \text{otherwise} \end{cases}\right]$$

where:
- $\psi(n) = \sum_{d=1}^n \Lambda(d)$ is the Chebyshev psi function with $\Lambda(d)$ being the von Mangoldt function
- $\theta(n) = \sum_{p \leq n, p \text{ prime}} \ln(p)$ is the Chebyshev theta function
- The second term counts prime powers with even exponents $\geq 2$
- The third term counts prime powers with odd exponents $\geq 3$

### Informal proof
We prove the identity by showing that the terms on both sides are equal.

First, we rewrite the definitions of $\psi(n)$ and $\theta(n)$, and apply the sum of sums property:
$$\psi(n) = \sum_{d=1}^n \Lambda(d)$$
$$\theta(n) = \sum_{p=1}^n [\text{if } p \text{ is prime then } \ln(p) \text{ else } 0]$$

We need to show that for each $r$ such that $1 \leq r \leq n$, the summands on both sides are equal. So we consider an arbitrary $r$ in this range, and analyze the von Mangoldt function $\Lambda(r)$.

By definition, $\Lambda(r) = \ln(p)$ if $r$ is a prime power $p^k$ with $k \geq 1$, and $0$ otherwise.

We have two main cases:
1. When $r$ is not a prime power: In this case $\Lambda(r) = 0$, and the three terms on the right side also sum to 0, as $r$ is neither a prime, nor a prime power with even exponent, nor a prime power with odd exponent.

2. When $r$ is a prime power, i.e., $r = p^m$ for some prime $p$ and $m \geq 1$:
   * If $m = 1$, then $r = p$ is a prime. In this case:
     - $\Lambda(r) = \ln(p)$
     - $\theta(r)$ contributes $\ln(p)$
     - The other sums contribute 0 as $r$ is not of the form $p^{2k}$ or $p^{2k+1}$ with $k \geq 1$
   * If $m > 1$, we can write $m = 2k + d$ where $d \in \{0,1\}$ (division with remainder).
     - If $d = 0$, so $m = 2k$ for $k \geq 1$, then $r = p^{2k}$ contributes to the second sum.
     - If $d = 1$, so $m = 2k + 1$ for $k \geq 1$, then $r = p^{2k+1}$ contributes to the third sum.

The proof carefully handles special cases and uses properties like `APRIMEDIVISOR_PRIMEPOW` which states that for prime powers $p^k$ with $k \geq 1$, the function $\text{aprimedivisor}(p^k) = p$.

The theorem `PRIMEPOW_ODD_EVEN` is also used to show that a number cannot simultaneously be both a prime power with an even exponent and a prime power with an odd exponent.

### Mathematical insight
This theorem expresses the Chebyshev psi function $\psi(n)$ in terms of its constituent parts based on the structure of the von Mangoldt function $\Lambda(n)$. The decomposition separates:

1. Primes (through the $\theta$ function)
2. Prime powers with even exponents ≥ 2
3. Prime powers with odd exponents ≥ 3

This decomposition is useful in number theory, particularly in the study of the distribution of prime numbers. The Chebyshev functions $\psi$ and $\theta$ are important in proving results related to the Prime Number Theorem, which describes the asymptotic distribution of prime numbers.

By separating the contributions from different types of prime powers, this theorem provides a more detailed structural understanding of the psi function, which can be leveraged in asymptotic analyses. The decomposition also clarifies how the Mangoldt function accounts for each prime power exactly once, with the corresponding prime as its logarithmic weight.

### Dependencies
- **Theorems**:
  - `PRIME_0`: States that 0 is not prime
  - `PRIME_1`: States that 1 is not prime
  - `PRIME_DIVEXP`: If a prime divides a power, then it divides the base
  - `PRIME_EXP`: A power is prime if and only if the base is prime and the exponent is 1
  - `SUM_EQ`: Two sums are equal if their summands are equal
  - `SUM_ADD`: Sum of sum of functions equals sum of their sum
  - `APRIMEDIVISOR_PRIMEPOW`: The prime divisor of a prime power is the prime itself
  - `PRIMEPOW_ODD_EVEN`: No number can be both a prime power with even exponent and a prime power with odd exponent
  - `sum`: Basic properties of finite sums

- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: The von Mangoldt function
  - `primepow`: Prime power property
  - `aprimedivisor`: A prime divisor of a number
  - `psi`: The Chebyshev psi function
  - `theta`: The Chebyshev theta function

### Porting notes
When porting this theorem:
1. Ensure your system has appropriate definitions for the Chebyshev functions $\psi$ and $\theta$, as well as the von Mangoldt function.
2. The proof relies on case analysis of whether numbers are prime powers, with careful handling of the exponents. Ensure your system has good support for such case analysis.
3. The theorem `PRIMEPOW_ODD_EVEN` may be challenging to port as it involves proving that a number cannot simultaneously be a prime power with both even and odd exponents.
4. Properties of the logarithm function will be needed, especially in relation to the von Mangoldt function.

---

## SUM_SURJECT

### Name of formal statement
SUM_SURJECT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_SURJECT = prove
 (`!f i m n p q.
        (!r. m <= r /\ r < m + n ==> &0 <= f(i r)) /\
        (!s. p <= s /\ s < p + q /\ ~(f(s) = &0)
             ==> ?r. m <= r /\ r < m + n /\ (i r = s))
        ==> sum(p,q) f <= sum(m,n) (\r. f(i r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m,n) (\r. if p:num <= i(r) /\ i(r) < p + q
                            then f(i(r)) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_LE_REFL; ADD_AC]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`q:num`,`q:num`) THEN INDUCT_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[ARITH_RULE `~(p <= q /\ q < p + 0)`] THEN
    REWRITE_TAC[SUM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `s < p + q ==> s < p + SUC q`];
    ALL_TAC] THEN
  REWRITE_TAC[sum] THEN
  SUBGOAL_THEN
   `sum(m,n) (\r. if p <= i r /\ i r < p + SUC q then f (i r) else &0) =
    sum(m,n) (\r. if p <= i r /\ i r < p + q then f (i r) else &0) +
    sum(m,n) (\r. if i r = p + q then f(i r) else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num->num) r = p + q` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[LE_ADD; LT_REFL; ARITH_RULE `p + q < p + SUC q`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE
       `r < p + SUC q <=> (r = p + q) \/ r < p + q`] THEN
    REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `f <= s'' ==> s <= s' ==> s + f <= s' + s''`) THEN
  UNDISCH_TAC
   `!s. p <= s /\ s < p + SUC q /\ ~(f s = &0)
           ==> (?r:num. m <= r /\ r < m + n /\ (i r = s))` THEN
  DISCH_THEN(MP_TAC o SPEC `p + q:num`) THEN
  ASM_CASES_TAC `f(p + q:num) = &0` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,n) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[ADD_SYM];
    ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n = (s - m) + 1 + ((m + n) - (s + 1))` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m <= s:num`; `s < m + n:num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_SIMP_TAC[SUM_1; ARITH_RULE `m <= s ==> (m + (s - m) = s:num)`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> a <= x + a + y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,s - m) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`m <= r:num`; `r < s - m + m:num`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(s + 1,(m + n) - (s + 1)) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`r < (m + n) - (s + 1) + s + 1:num`;
       `s + 1 <= r`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC]);;
```

### Informal statement
For any function $f$ from natural numbers to reals and any function $i$ between natural numbers, if:
1. For all $r$ such that $m \leq r < m+n$, we have $0 \leq f(i(r))$.
2. For all $s$ such that $p \leq s < p+q$ where $f(s) \neq 0$, there exists some $r$ with $m \leq r < m+n$ such that $i(r) = s$.

Then: $\sum_{s=p}^{p+q-1} f(s) \leq \sum_{r=m}^{m+n-1} f(i(r))$.

### Informal proof
We prove this by induction on $q$.

First, we show that:
$\sum_{s=p}^{p+q-1} f(s) \leq \sum_{r=m}^{m+n-1} g(r)$, where $g(r) = f(i(r))$ if $p \leq i(r) < p+q$, and $g(r) = 0$ otherwise.

We then compare $\sum_{r=m}^{m+n-1} g(r)$ with $\sum_{r=m}^{m+n-1} f(i(r))$.

**Base case**: When $q = 0$:
- The sum $\sum_{s=p}^{p+0-1} f(s)$ is empty, thus equal to $0$.
- Since $0 \leq \sum_{r=m}^{m+n-1} g(r)$, the inequality holds.

**Inductive case**: Assume the result holds for $q$, and we prove it for $q+1$.

Let's split the function $g$ for $q+1$ into:
$g_{q+1}(r) = g_q(r) + h(r)$ where $h(r) = f(i(r))$ if $i(r) = p+q$, otherwise $h(r) = 0$.

So $\sum_{r=m}^{m+n-1} g_{q+1}(r) = \sum_{r=m}^{m+n-1} g_q(r) + \sum_{r=m}^{m+n-1} h(r)$

Now, we need to show:
$\sum_{s=p}^{p+(q+1)-1} f(s) \leq \sum_{r=m}^{m+n-1} g_{q+1}(r)$

This can be rewritten as:
$\sum_{s=p}^{p+q-1} f(s) + f(p+q) \leq \sum_{r=m}^{m+n-1} g_q(r) + \sum_{r=m}^{m+n-1} h(r)$

By the inductive hypothesis, we have:
$\sum_{s=p}^{p+q-1} f(s) \leq \sum_{r=m}^{m+n-1} g_q(r)$

So we need to show:
$f(p+q) \leq \sum_{r=m}^{m+n-1} h(r)$

If $f(p+q) = 0$, this is trivial since the sum is non-negative.

If $f(p+q) \neq 0$, by assumption 2, there exists $s$ such that $m \leq s < m+n$ and $i(s) = p+q$.

We can rearrange:
$\sum_{r=m}^{m+n-1} h(r) = \sum_{r=m}^{s-1} h(r) + h(s) + \sum_{r=s+1}^{m+n-1} h(r)$

Since $h(r) = 0$ for $r \neq s$ (where $i(r) \neq p+q$) and $h(s) = f(p+q)$:
$\sum_{r=m}^{m+n-1} h(r) = f(p+q)$

Finally, the original inequality holds by combining these results:
$\sum_{r=m}^{m+n-1} g(r) \leq \sum_{r=m}^{m+n-1} f(i(r))$ because $g(r) \leq f(i(r))$ for all $r$ in the range.

Therefore, $\sum_{s=p}^{p+q-1} f(s) \leq \sum_{r=m}^{m+n-1} f(i(r))$.

### Mathematical insight
This theorem establishes an inequality for sums under the action of a function $i$ on indices. It essentially shows that when $i$ is "surjective" on the support of $f$ (where $f$ is non-zero), then the sum over the codomain is less than or equal to the sum over the domain after applying $i$.

The key insight is that the function $i$ might map multiple elements from the domain to the same element in the codomain, potentially "overcounting" the values, which explains why we get an inequality rather than an equality.

This result is important for dealing with rearrangements and transformations of sums, particularly when working with functions that map between different index sets.

### Dependencies
- `REAL_LE_REFL` - Reflexivity of real number inequality: $\forall x. x \leq x$
- `REAL_LE_TRANS` - Transitivity of real number inequality: $\forall x,y,z. x \leq y \land y \leq z \Rightarrow x \leq z$
- `sum` - Definition of finite sum: $\sum_{i=n}^{n+0-1} f(i) = 0$ and $\sum_{i=n}^{n+\text{SUC}(m)-1} f(i) = \sum_{i=n}^{n+m-1} f(i) + f(n+m)$
- `SUM_LE` - Monotonicity of sums: $\forall f,g,m,n. (\forall r. m \leq r < n+m \Rightarrow f(r) \leq g(r)) \Rightarrow \sum_{i=m}^{m+n-1} f(i) \leq \sum_{i=m}^{m+n-1} g(i)$
- `SUM_EQ` - Equality of sums with equal terms: $\forall f,g,m,n. (\forall r. m \leq r < n+m \Rightarrow f(r) = g(r)) \Rightarrow \sum_{i=m}^{m+n-1} f(i) = \sum_{i=m}^{m+n-1} g(i)$
- `SUM_ADD` - Sum of sum: $\forall f,g,m,n. \sum_{i=m}^{m+n-1} (f(i) + g(i)) = \sum_{i=m}^{m+n-1} f(i) + \sum_{i=m}^{m+n-1} g(i)$
- `SUM_0` - Sum of zeros: $\forall m,n. \sum_{i=m}^{m+n-1} 0 = 0$
- `SUM_SPLIT` - Splitting sums: $\forall f,n,p. \sum_{i=m}^{m+n-1} f(i) + \sum_{i=m+n}^{m+n+p-1} f(i) = \sum_{i=m}^{m+n+p-1} f(i)$

### Porting notes
- This proof relies significantly on induction and case analysis, which should translate well to other systems.
- The handling of finite sums may differ between systems - ensure that the sum notation is properly translated and that the indexing conventions match.
- The proof uses some arithmetic reasoning about indices that may require more explicit justification in other proof assistants.
- The conditional function definition (`if p <= i(r) /\ i(r) < p + q then f(i(r)) else 0`) is a key component of the proof and should be carefully managed when porting.

---

## PSI_RESIDUES_COMPARE_2

I'll revise the documentation to fix the summation upper bound issue in the informal statement and ensure it matches the formal content.

### PSI_RESIDUES_COMPARE_2
- PSI_RESIDUES_COMPARE_2

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_RESIDUES_COMPARE_2 = prove
 (`sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                 then ln(&(aprimedivisor d)) else &0)
   <= sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                    then ln(&(aprimedivisor d)) else &0)`,
  MP_TAC(SPECL
   [`\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                    then ln(&(aprimedivisor d)) else &0`;
    `\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP k)
                  then d * (aprimedivisor d) else d`;
    `2`; `n:num`; `2`; `n:num`] SUM_SURJECT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`]] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `p EXP k * p = p EXP (k + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `1 <= k + 1`] THEN
      ASM_MESON_TAC[LN_POS; REAL_OF_NUM_LE; PRIME_GE_2; REAL_LE_REFL;
                    ARITH_RULE `2 <= n ==> 1 <= n`];
      ALL_TAC] THEN
    X_GEN_TAC `s:num` THEN
    ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (s = p EXP (2 * k + 1))` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    EXISTS_TAC `p EXP (2 * k)` THEN
    COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k`]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_ADD; EXP_1;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`;
                  EXP_EQ_0; EXP_EQ_1] THEN
      ASM_MESON_TAC[PRIME_1; PRIME_0;
                    ARITH_RULE `1 <= k ==> ~(2 * k = 0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP (2 * k + 1)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`]] THEN
  FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC)) THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    SUBGOAL_THEN `p EXP (2 * k) * p = p EXP (2 * k + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; REAL_LE_REFL;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> b ==> c`) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` APRIMEDIVISOR) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
  ABBREV_TAC `q = aprimedivisor r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * k + 1` THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `r * p = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[EXP_ADD; EXP_1; EQ_MULT_RCANCEL] THEN
  ASM_MESON_TAC[PRIME_0]);;
```

### Informal statement
This theorem states that 
$$\sum_{d=2}^{n} \left(\ln(\text{aprimedivisor}(d)) \text{ if } d = p^{2k+1} \text{ for some prime } p \text{ and } k \geq 1, \text{ else } 0\right) \leq \sum_{d=2}^{n} \left(\ln(\text{aprimedivisor}(d)) \text{ if } d = p^{2k} \text{ for some prime } p \text{ and } k \geq 1, \text{ else } 0\right)$$

where $\ln(\text{aprimedivisor}(d))$ represents the natural logarithm of a prime divisor of $d$.

### Informal proof
The proof compares two sums involving prime powers. We need to show that the sum of logarithms for odd-powered prime terms is bounded by the sum for even-powered terms.

The key steps of the proof are:

* We apply the `SUM_SURJECT` theorem to establish a connection between the two sums via a surjective mapping.

* We define a mapping function $i(d) = d \cdot \text{aprimedivisor}(d)$ if $d = p^k$ for some prime $p$ and $k \geq 1$, and $i(d) = d$ otherwise.

* We show that this mapping satisfies the conditions for `SUM_SURJECT`:
  - For any $r$ in the domain, the term $f(i(r))$ is non-negative.
  - For any $s$ with non-zero $f(s)$ in the target sum, there exists an $r$ in the domain with $i(r) = s$.

* For the first condition, we prove that if $r = p^k$ for some prime $p$ and $k \geq 1$, then:
  - $\text{aprimedivisor}(p^k) = p$ (using `APRIMEDIVISOR_PRIMEPOW`)
  - $r \cdot \text{aprimedivisor}(r) = p^k \cdot p = p^{k+1}$
  - If $r = p^{2k}$, then $i(r) = p^{2k+1}$
  - The logarithm of a prime is non-negative since all primes are ≥ 2.

* For the second condition, we prove that for any $s = p^{2k+1}$ where $p$ is prime and $k \geq 1$:
  - The preimage of $s$ under $i$ is $p^{2k}$
  - We verify that $p^{2k} \geq 2$ (using properties of prime powers)
  - We show that $i(p^{2k}) = p^{2k+1} = s$

* We then complete the proof by showing for each $r$ in the summation range:
  - If $r$ is not a prime power, both sums contribute 0
  - If $r = p^{2k}$ for some prime $p$ and $k \geq 1$, we have $i(r) = p^{2k+1}$ and the corresponding logarithm values are equal
  - Otherwise, the odd-powered term is 0, making the inequality hold

The crux of the proof is establishing that each odd-powered prime term in the first sum has a corresponding even-powered prime term in the second sum with the same logarithm value.

### Mathematical insight
This theorem compares two sums related to the von Mangoldt function and the Chebyshev psi function. The result shows that the sum of logarithms of primes for odd-powered terms is bounded by the sum for even-powered terms.

The key insight is that we can establish a surjective mapping from even-powered prime terms to odd-powered ones in a way that preserves the logarithm values. This mapping multiplies each even power by its prime base to obtain the corresponding odd power.

This result is likely used as a step in proving asymptotic bounds related to the distribution of prime numbers, particularly in the context of Bertrand's postulate or Chebyshev's theorems on prime number density.

### Dependencies
- Prime number theorems:
  - `PRIME_0`: Not prime(0)
  - `PRIME_1`: Not prime(1)
  - `PRIME_GE_2`: All primes are >= 2
  - `PRIME_DIVEXP`: If p is prime and divides x^n, then p divides x
- Real number properties:
  - `REAL_LE_REFL`: x <= x
  - `LN_POS`: For x >= 1, ln(x) >= 0
- Sum properties:
  - `sum`: Basic properties of sum
  - `SUM_LE`: Monotonicity of sum
  - `SUM_SURJECT`: Inequality for sums with surjective mappings
- Prime divisor properties:
  - `APRIMEDIVISOR_PRIMEPOW`: The prime divisor of p^k is p
  - `APRIMEDIVISOR`: Properties of a prime divisor function

### Porting notes
- The proof relies heavily on the `aprimedivisor` function, which selects a prime divisor of a number. In other systems, you may need to define this function carefully, ensuring it satisfies the property that for any non-trivial number n, aprimedivisor(n) is a prime that divides n.
- The use of `SUM_SURJECT` is central to the proof. This is a fairly specialized theorem about sums and surjective mappings that may need to be ported first.
- The handling of conditionals in the summations may require different approaches in other proof assistants, possibly using indicator functions or case analysis.

---

## PSI_RESIDUES_COMPARE

### Name of formal statement
PSI_RESIDUES_COMPARE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_RESIDUES_COMPARE = prove
 (`!n. sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                     then ln(&(aprimedivisor d)) else &0)
       <= sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                        then ln(&(aprimedivisor d)) else &0)`,
  GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[sum; REAL_LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> (n = 1 + (n - 1))`)) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  MATCH_MP_TAC(REAL_ARITH
   `b <= d /\ (a = &0) /\ (c = &0) ==> a + b <= c + d`) THEN
  REWRITE_TAC[PSI_RESIDUES_COMPARE_2; ARITH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[EXP_EQ_1; PRIME_1; ARITH_RULE
    `1 <= k ==> ~(2 * k = 0) /\ ~(2 * k + 1 = 0)`]);;
```

### Informal statement
For any natural number $n$, we have:
$$\sum_{d=1}^{n} \left(\text{if }\exists p,k: 1 \leq k \land \text{prime}(p) \land (d = p^{2k+1}) \text{ then } \ln(a(d)) \text{ else } 0\right) \leq \sum_{d=1}^{n} \left(\text{if }\exists p,k: 1 \leq k \land \text{prime}(p) \land (d = p^{2k}) \text{ then } \ln(a(d)) \text{ else } 0\right)$$

where $a(d)$ represents $\text{aprimedivisor}(d)$, which is a prime number that divides $d$.

### Informal proof
The proof proceeds as follows:

- We first handle the base case where $n = 0$. In this case, both sums are equal to $0$, so the inequality holds trivially.

- For $n > 0$, we can split $n$ as $1 + (n-1)$ and use the sum splitting property to write:
  $$\sum_{d=1}^{n} f(d) = f(1) + \sum_{d=2}^{n} f(d)$$

- For the first term at $d=1$, we observe that $1$ is neither of the form $p^{2k}$ nor $p^{2k+1}$ for any prime $p$ and $k \geq 1$ because:
  - $1$ is not a prime (by theorem `PRIME_1`)
  - For any $k \geq 1$, we have $2k > 0$ and $2k+1 > 0$, so $p^{2k} \neq 1$ and $p^{2k+1} \neq 1$ for any prime $p$

- This means that both terms $f(1)$ in the left and right sums evaluate to $0$.

- The inequality now reduces to:
  $$\sum_{d=2}^{n} \left(\text{if }\exists p,k: 1 \leq k \land \text{prime}(p) \land (d = p^{2k+1}) \text{ then } \ln(a(d)) \text{ else } 0\right) \leq \sum_{d=2}^{n} \left(\text{if }\exists p,k: 1 \leq k \land \text{prime}(p) \land (d = p^{2k}) \text{ then } \ln(a(d)) \text{ else } 0\right)$$

- This inequality is proven by theorem `PSI_RESIDUES_COMPARE_2`, which establishes precisely this relation for sums starting at $d=2$.

### Mathematical insight
This theorem compares two sums related to the prime power structure of numbers up to $n$. Specifically, it shows that when we sum the logarithms of prime divisors for numbers that are odd powers of primes ($p^{2k+1}$), the result is at most the corresponding sum for even powers of primes ($p^{2k}$).

This result is likely a component in a larger proof related to the distribution of prime numbers, possibly in the context of Bertrand's postulate or related results (as suggested by the file name "bertrand.ml"). The comparison of residues associated with different prime powers is a common technique in analytic number theory.

The result ultimately relies on the fact that for corresponding terms in the sums, when a number is of the form $p^{2k+1}$, its prime divisor is $p$, which is the same as the prime divisor of $p^{2k}$. The inequality follows from carefully comparing these related terms.

### Dependencies
- **Theorems:**
  - `PRIME_1`: The number 1 is not prime
  - `REAL_LE_REFL`: For any real number x, x ≤ x
  - `sum`: Basic properties of summation
  - `SUM_SPLIT`: Splitting a sum into two parts
  - `PSI_RESIDUES_COMPARE_2`: The main inequality for sums starting at 2

- **Definitions:**
  - `ln`: Natural logarithm function
  - `aprimedivisor`: Function that returns a prime divisor of a number

### Porting notes
When porting this theorem, pay attention to:
1. The definition of `aprimedivisor` which uses the Hilbert choice operator `@` to select a prime divisor
2. The conditional expressions inside the sums require careful handling
3. The proof relies on splitting the sum and reducing to `PSI_RESIDUES_COMPARE_2`, which must be ported first

---

## PSI_SQRT

### Name of formal statement
PSI_SQRT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_SQRT = prove
 (`!n. psi(ISQRT(n)) =
        sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                      then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi] THEN INDUCT_TAC THEN
  REWRITE_TAC[ISQRT_0; sum; ISQRT_SUC] THEN
  ASM_CASES_TAC `?m. SUC n = m EXP 2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (1 + n = p EXP (2 * k)))`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
      ASM_MESON_TAC[ARITH_RULE `1 + n = SUC n`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL; sum] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `1 + ISQRT n = m` SUBST1_TAC THENL
   [SUBGOAL_THEN `(1 + ISQRT n) EXP 2 = SUC n` MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
      REWRITE_TAC[EXP_MONO_LE; EXP_MONO_LT; NOT_SUC]] THEN
    MP_TAC(SPEC `n:num` ISQRT_SUC) THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `SUC n` ISQRT_WORKS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[EXP_MONO_LE; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
  REWRITE_TAC[EXP_MONO_EQ; ARITH_EQ] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aprimedivisor] THEN
  REPEAT AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[EXP; EXP_1] THEN
  ASM_SIMP_TAC[PRIME_DIVEXP_EQ; ARITH_EQ]);;
```

### Informal statement
For any natural number $n$, the following equality holds:
$$\psi(\text{ISQRT}(n)) = \sum_{d=1}^{n} f(d)$$
where $f(d) = \begin{cases} 
\ln(p) & \text{if } \exists p,k \text{ such that } 1 \leq k \text{ and } p \text{ is prime and } d = p^{2k} \\
0 & \text{otherwise}
\end{cases}$

Here, $\psi$ is the second Chebyshev function, a sum of the von Mangoldt function $\Lambda$ over integers up to a certain bound, and ISQRT$(n)$ is the integer square root of $n$.

### Informal proof
We prove this by induction on $n$.

**Base case**: For $n = 0$:
- We have $\psi(\text{ISQRT}(0)) = \psi(0)$ since $\text{ISQRT}(0) = 0$
- Then $\psi(0) = \sum_{d=1}^{0} \Lambda(d) = 0$
- And $\sum_{d=1}^{0} f(d) = 0$
- So the base case holds.

**Inductive step**: Assume the theorem holds for $n$. We need to show it holds for $\text{SUC}(n) = n+1$.

We have two cases to consider based on whether $n+1$ is a perfect square:

1. If $n+1 = m^2$ for some $m$:
   - By the definition of ISQRT, we have $\text{ISQRT}(n+1) = m = \text{ISQRT}(n) + 1$
   - From the induction hypothesis, we know that $\psi(\text{ISQRT}(n)) = \sum_{d=1}^{n} f(d)$
   - We need to show: $\psi(\text{ISQRT}(n)+1) = \sum_{d=1}^{n+1} f(d)$
   - This can be rewritten as $\psi(\text{ISQRT}(n)) + \Lambda(m) = \sum_{d=1}^{n} f(d) + f(n+1)$ 
   - Using the definition of the von Mangoldt function and the fact that $n+1 = m^2$, we can show that $f(n+1) = \Lambda(m)$ if and only if $m$ is a prime power of the form $p^k$ and $n+1 = p^{2k}$
   - The theorem follows from the properties of the aprimedivisor function and the von Mangoldt function.

2. If $n+1$ is not a perfect square:
   - Then $\text{ISQRT}(n+1) = \text{ISQRT}(n)$
   - We need to show: $\psi(\text{ISQRT}(n)) = \sum_{d=1}^{n} f(d) + f(n+1)$
   - Since $n+1$ is not a perfect square, it cannot be of the form $p^{2k}$ for a prime $p$ and $k \geq 1$
   - Therefore $f(n+1) = 0$
   - So we have $\psi(\text{ISQRT}(n)) = \sum_{d=1}^{n} f(d) + 0 = \sum_{d=1}^{n+1} f(d)$

The result follows by induction.

### Mathematical insight
This theorem relates the second Chebyshev function $\psi$ evaluated at the integer square root of $n$ to a modified version of itself that only counts perfect even powers of primes. It essentially demonstrates that $\psi(\sqrt{n})$ captures exactly the contribution of numbers of the form $p^{2k}$ up to $n$ in the original Chebyshev function.

This result is important in analytic number theory, particularly in the study of the distribution of prime numbers. The relationship helps connect the behavior of primes to perfect powers, which is useful in various number theoretic estimates and the study of the Prime Number Theorem.

### Dependencies
- **Theorems**:
  - `PRIME_DIVEXP_EQ`: If $p$ is prime, then $p$ divides $x^n$ if and only if $p$ divides $x$ and $n \neq 0$
  - `sum`: Basic properties of summation, particularly that $\sum_{i=n}^{0} f(i) = 0$ and $\sum_{i=n}^{m+1} f(i) = \sum_{i=n}^{m} f(i) + f(n+m)$
  - `ISQRT_WORKS`: For any $n$, $\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n) + 1)^2$
  - `ISQRT_0`: $\text{ISQRT}(0) = 0$
  - `ISQRT_SUC`: Defines how ISQRT behaves with successor function

- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: Von Mangoldt function, defined as $\ln(p)$ if $n$ is a prime power $p^k$ and $0$ otherwise
  - `ISQRT`: Integer square root function
  - `primepow`: Predicate for whether a number is a prime power
  - `aprimedivisor`: Function returning a prime divisor of a number
  - `psi`: The second Chebyshev function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Porting notes
When porting this theorem:
1. Ensure your system has compatible definitions for Chebyshev functions, von Mangoldt function, and integer square root
2. The core of the proof relies on the relationship between prime powers and divisibility, so make sure these primitive number theory results are available
3. The inductive approach may need modification in systems that handle induction differently from HOL Light
4. The handling of conditionals and case analysis for perfect squares vs non-perfect squares is critical to the proof structure

---

## PSI_THETA

### PSI_THETA
- psi_theta

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_THETA = prove
 (`!n. theta(n) + psi(ISQRT n) <= psi(n) /\
       psi(n) <= theta(n) + &2 * psi(ISQRT n)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [PSI_SPLIT] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [PSI_SPLIT] THEN
  MP_TAC(SPEC `n:num` PSI_RESIDUES_COMPARE) THEN
  REWRITE_TAC[GSYM PSI_SQRT] THEN
  SIMP_TAC[REAL_MUL_2; GSYM REAL_ADD_ASSOC; REAL_LE_LADD; REAL_LE_ADDR] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SUM_POS_GEN THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
    ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`] THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ASM_MESON_TAC[PRIME_0; ARITH_RULE `~(p = 0) ==> 1 <= p`]);;
```

### Informal statement
For any natural number $n$, the following inequality holds:
$$\theta(n) + \psi(\text{ISQRT}(n)) \leq \psi(n) \leq \theta(n) + 2 \cdot \psi(\text{ISQRT}(n))$$

where:
- $\theta(n) = \sum_{p \leq n, \, p \text{ prime}} \ln(p)$
- $\psi(n) = \sum_{d \leq n} \Lambda(d)$ is Chebyshev's second function, where $\Lambda$ is the von Mangoldt function
- $\text{ISQRT}(n)$ is the integer square root of $n$

### Informal proof
We prove both inequalities:

Starting with the decomposition of $\psi(n)$ from `PSI_SPLIT`:

$$\psi(n) = \theta(n) + \sum_{d=1}^n f_1(d) + \sum_{d=1}^n f_2(d)$$

where:
- $f_1(d) = \ln(p)$ if $d = p^{2k}$ for some prime $p$ and $k \geq 1$, and 0 otherwise
- $f_2(d) = \ln(p)$ if $d = p^{2k+1}$ for some prime $p$ and $k \geq 1$, and 0 otherwise

We also use the theorem `PSI_SQRT` which states that:
$$\psi(\text{ISQRT}(n)) = \sum_{d=1}^n f_1(d)$$

And from `PSI_RESIDUES_COMPARE`, we know that:
$$\sum_{d=1}^n f_2(d) \leq \sum_{d=1}^n f_1(d)$$

For the lower bound:
- Since $\psi(n) = \theta(n) + \sum_{d=1}^n f_1(d) + \sum_{d=1}^n f_2(d)$
- And $\sum_{d=1}^n f_1(d) = \psi(\text{ISQRT}(n))$
- And $\sum_{d=1}^n f_2(d) \geq 0$ (proven by showing each term is non-negative)
- We have $\psi(n) \geq \theta(n) + \psi(\text{ISQRT}(n))$

For the upper bound:
- From `PSI_RESIDUES_COMPARE`: $\sum_{d=1}^n f_2(d) \leq \sum_{d=1}^n f_1(d) = \psi(\text{ISQRT}(n))$
- Thus $\psi(n) = \theta(n) + \sum_{d=1}^n f_1(d) + \sum_{d=1}^n f_2(d) \leq \theta(n) + 2\psi(\text{ISQRT}(n))$

The non-negativity of the sums follows because for each term where $d = p^{2k+1}$ for prime $p$ and $k \geq 1$, we have $\ln(p) \geq 0$ since $p \geq 2$ for any prime $p$.

### Mathematical insight
This theorem provides tight bounds on the relationship between Chebyshev's second function $\psi(n)$ and the first function $\theta(n)$ by expressing their difference in terms of $\psi(\text{ISQRT}(n))$. This relationship is crucial in number theory, particularly in the study of the distribution of prime numbers.

The theorem shows that $\psi(n)$ and $\theta(n)$ are close, with the difference controlled by $\psi$ evaluated at a much smaller value - the square root of $n$. This recursive relationship allows one to analyze the asymptotic behavior of both functions efficiently.

This result is a key ingredient in the proof of the Prime Number Theorem, as it allows one to translate estimates between different prime-counting functions.

### Dependencies
- Theorems:
  - `PSI_SPLIT`: Decomposition of $\psi(n)$ into $\theta(n)$ and two additional sums
  - `PSI_SQRT`: Relation between $\psi(\text{ISQRT}(n))$ and one of the sums from PSI_SPLIT
  - `PSI_RESIDUES_COMPARE`: Comparison between the two additional sums from PSI_SPLIT
  - `APRIMEDIVISOR_PRIMEPOW`: Properties of prime divisors of prime powers
  - `LN_POS`: Non-negativity of natural logarithm for arguments ≥ 1
  - `SUM_POS_GEN`: Non-negativity of sums with non-negative terms
  - `REAL_LE_LADD`: Cancellation law for inequality with addition
  - `REAL_LE_REFL`: Reflexivity of the real less-than-or-equal relation
  - `PRIME_0`: 0 is not prime

- Definitions:
  - `psi`: Chebyshev's second function
  - `theta`: Chebyshev's first function
  - `ISQRT`: Integer square root function

### Porting notes
When porting to other systems, note that:
1. The handling of natural numbers vs. reals might differ across systems
2. The precise definition of ISQRT might need careful implementation
3. The definitions of the Chebyshev functions need to be aligned with the standard number theory definitions
4. The proof relies heavily on the decomposition of $\psi(n)$ established in PSI_SPLIT, which should be ported first

---

## THETA_LE_PSI

### THETA_LE_PSI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_LE_PSI = prove
 (`!n. theta(n) <= psi(n)`,
  GEN_TAC THEN REWRITE_TAC[theta; psi] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[MANGOLDT_POS] THEN
  ASM_SIMP_TAC[mangoldt; PRIME_PRIMEPOW] THEN
  SUBGOAL_THEN `aprimedivisor p = p`
   (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_1; LE_REFL]);;
```

### Informal statement
For all natural numbers $n$, the following inequality holds:
$$\theta(n) \leq \psi(n)$$

where:
- $\theta(n) = \sum_{p=1}^{n} \begin{cases} \ln(p) & \text{if p is prime} \\ 0 & \text{otherwise} \end{cases}$
- $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the von Mangoldt function

### Informal proof
We prove that $\theta(n) \leq \psi(n)$ for all natural numbers $n$.

By the definitions of $\theta$ and $\psi$, we need to show:
$$\sum_{p=1}^{n} \begin{cases} \ln(p) & \text{if p is prime} \\ 0 & \text{otherwise} \end{cases} \leq \sum_{d=1}^{n} \Lambda(d)$$

To prove this, we apply the theorem `SUM_LE` which states that if $f(r) \leq g(r)$ for all $r$ in the summation range, then the sum of $f$ is less than or equal to the sum of $g$.

We need to show that for all $p$ where $1 \leq p < n+1$:
- If $p$ is prime, then $\ln(p) \leq \Lambda(p)$
- If $p$ is not prime, then $0 \leq \Lambda(p)$

For the case where $p$ is not prime:
- We know from `MANGOLDT_POS` that $\Lambda(d) \geq 0$ for all $d$, so $0 \leq \Lambda(p)$ holds.

For the case where $p$ is prime:
- By `PRIME_PRIMEPOW`, if $p$ is prime, then $p$ is a prime power.
- By the definition of the von Mangoldt function, $\Lambda(p) = \ln(q)$ where $q$ is the unique prime dividing $p$.
- Since $p$ is itself prime, the unique prime dividing $p$ is $p$ itself, so $q = p$ (this is formalized using `APRIMEDIVISOR_PRIMEPOW` with $k = 1$).
- Therefore, $\Lambda(p) = \ln(p)$, which means $\ln(p) \leq \Lambda(p)$ holds with equality.

Hence, for all values in the summation range, the corresponding terms in $\theta(n)$ are less than or equal to those in $\psi(n)$, which proves $\theta(n) \leq \psi(n)$.

### Mathematical insight
This theorem establishes a fundamental relationship between two important functions in analytic number theory:

1. $\theta(n)$ (Chebyshev's first function) counts primes directly, giving weight $\ln(p)$ to each prime $p \leq n$.
2. $\psi(n)$ (Chebyshev's second function) counts prime powers, giving weight $\ln(p)$ to each occurrence of $p^k \leq n$ where $p$ is prime and $k \geq 1$.

The inequality $\theta(n) \leq \psi(n)$ is expected because $\psi(n)$ counts all the terms that $\theta(n)$ counts (primes with weight $\ln(p)$), plus additional terms for higher prime powers. This inequality is important in the study of the distribution of prime numbers, particularly in the proof of the Prime Number Theorem.

### Dependencies
- **Theorems**:
  - `REAL_LE_REFL`: For any real number $x$, $x \leq x$.
  - `SUM_LE`: If $f(r) \leq g(r)$ for all $r$ in the summation range, then $\sum f \leq \sum g$.
  - `APRIMEDIVISOR_PRIMEPOW`: For any prime $p$ and $k \geq 1$, $\text{aprimedivisor}(p^k) = p$.
  - `PRIME_PRIMEPOW`: If $p$ is prime, then $p$ is a prime power.
  - `MANGOLDT_POS`: For all natural numbers $d$, the von Mangoldt function satisfies $\Lambda(d) \geq 0$.

- **Definitions**:
  - `mangoldt`: Definition of von Mangoldt function $\Lambda(d)$.
  - `aprimedivisor`: Definition that selects a prime divisor of a number.
  - `psi`: Definition of Chebyshev's second function $\psi(n)$.
  - `theta`: Definition of Chebyshev's first function $\theta(n)$.

### Porting notes
When porting this theorem, take care with the definitions of the number theoretic functions. The von Mangoldt function $\Lambda(d)$ is defined as $\ln(p)$ when $d = p^k$ for some prime $p$ and integer $k \geq 1$, and 0 otherwise. The implementation using `aprimedivisor` may be done differently in other proof assistants, so you might need to adapt the proof accordingly.

---

## PSI_UBOUND_30

### Name of formal statement
PSI_UBOUND_30

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_30 = prove
 (`!n. n <= 30 ==> psi(n) <= &65 / &64 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 30 <=> n < 31`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;
```

### Informal statement
For all natural numbers $n$, if $n \leq 30$, then $\psi(n) \leq \frac{65}{64} \cdot n$.

Here, $\psi(n)$ is the Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the von Mangoldt function.

### Informal proof
The proof establishes a tighter bound on the Chebyshev $\psi$ function for values of $n \leq 30$. The proof proceeds as follows:

- First, the inequality $n \leq 30$ is rewritten as $n < 31$ using arithmetic rules.
- The proof then uses precomputed values of the $\psi$ function stored in `PSI_LIST_300`.
- For each case $n = 1, 2, ..., 30$, the proof:
  - Uses a lemma establishing transitivity of inequalities: if $a \leq b$, $l \leq a$, and some other condition holds, then $l \leq a$, $l \leq b$, and the other condition holds.
  - Applies numerical calculations using `REALCALC_REL_CONV` to show that for each specific value of $n$, the inequality $\psi(n) \leq \frac{65}{64} \cdot n$ holds.
  - Uses `LN_N2_CONV` to decompose logarithm expressions that arise during the calculation.

The proof essentially verifies the bound by direct calculation for each value of $n$ in the range.

### Mathematical insight
This theorem provides a tighter upper bound for the Chebyshev $\psi$ function specifically in the range $n \leq 30$. The Chebyshev function $\psi(n)$ plays an important role in analytic number theory, particularly in the study of the distribution of prime numbers.

The bound $\psi(n) \leq \frac{65}{64} \cdot n$ is tighter than more general asymptotic bounds and is used to reduce case analysis in subsequent proofs. As noted in the comment, this theorem is established "to reduce later case analysis."

The constant factor $\frac{65}{64} = 1.015625$ is very close to 1, showing that $\psi(n)$ closely tracks $n$ for small values of $n$.

### Dependencies
- **Theorems**:
  - `REAL_LE_TRANS`: Transitivity of real number inequality
  - `LN_1`: The natural logarithm of 1 equals 0
  - `LN_N2_CONV`: A conversion for manipulating logarithm expressions

- **Definitions**:
  - `psi`: The Chebyshev function defined as the sum of the von Mangoldt function values

- **Other**:
  - `PSI_LIST_300`: A precomputed list of values of $\psi(n)$ for $n$ up to 300

### Porting notes
When implementing this in another proof assistant:
1. You'll need precomputed values for the Chebyshev function up to 30.
2. The proof relies heavily on numerical computations for specific cases, so you'll need similar automation for real number calculations.
3. The approach is straightforward case analysis, but the background infrastructure (Chebyshev function, von Mangoldt function) needs to be in place first.

---

## THETA_UBOUND_3_2

### THETA_UBOUND_3_2
- `THETA_UBOUND_3_2`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let THETA_UBOUND_3_2 = prove
 (`!n. theta(n) <= &3 / &2 * &n`,
  MESON_TAC[REAL_LE_TRANS; PSI_UBOUND_3_2; THETA_LE_PSI]);;
```

### Informal statement
For all natural numbers $n$, the Chebyshev function $\theta(n)$ is bounded by:
$$\theta(n) \leq \frac{3}{2} \cdot n$$

where $\theta(n) = \sum_{1 \leq p \leq n, \text{ $p$ prime}} \ln(p)$ is the first Chebyshev function.

### Informal proof
The proof follows directly from two facts:
- By theorem `THETA_LE_PSI`, we have $\theta(n) \leq \psi(n)$ for all $n$
- By theorem `PSI_UBOUND_3_2`, we know that $\psi(n) \leq \frac{3}{2} \cdot n$ for all $n$

Therefore, by transitivity of the $\leq$ relation (using `REAL_LE_TRANS`), we have:
$$\theta(n) \leq \psi(n) \leq \frac{3}{2} \cdot n$$

So $\theta(n) \leq \frac{3}{2} \cdot n$ for all $n$.

### Mathematical insight
This theorem provides an explicit upper bound for the first Chebyshev function $\theta(n)$. The Chebyshev functions are important in analytic number theory, particularly in the study of the distribution of prime numbers. 

The bound $\theta(n) \leq \frac{3}{2} \cdot n$ is significant for various estimates in number theory. This result shows that the sum of the logarithms of primes up to $n$ grows at most linearly with $n$, with a constant factor of $\frac{3}{2}$.

This theorem is derived from a similar bound on the second Chebyshev function $\psi(n)$, which is technically easier to work with in certain contexts. The relationship between $\theta(n)$ and $\psi(n)$ allows for transferring bounds between these functions.

### Dependencies
- Theorems:
  - `REAL_LE_TRANS`: Transitivity of the less-than-or-equal relation for real numbers
  - `PSI_UBOUND_3_2`: The upper bound $\psi(n) \leq \frac{3}{2} \cdot n$ for the second Chebyshev function
  - `THETA_LE_PSI`: The inequality $\theta(n) \leq \psi(n)$ relating the first and second Chebyshev functions
- Definitions:
  - `theta`: The first Chebyshev function $\theta(n) = \sum_{1 \leq p \leq n, \text{ $p$ prime}} \ln(p)$

### Porting notes
When porting this theorem, ensure that the prerequisite theorems about Chebyshev functions are already available. The proof is straightforward and should translate easily to other systems, requiring only the transitivity property of inequalities and the two referenced theorems.

---

## THETA_LBOUND_1_2

### THETA_LBOUND_1_2
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let THETA_LBOUND_1_2 = prove
 (`!n. 5 <= n ==> &1 / &2 * &n <= theta(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n >= 900` THENL
   [MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
    MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
    ASM_SIMP_TAC[ARITH_RULE `n >= 900 ==> 4 <= n`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
    REWRITE_TAC[PSI_UBOUND_3_2] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &1 / &30) pow 2` MP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH
     `(a * b) * (a * b) = a * a * b * b`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_LE_LDIV_EQ;
             REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `n >= 900` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n < 413` THENL
   [UNDISCH_TAC `5 <= n` THEN UNDISCH_TAC `n < 413` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(THETA_LIST 412) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
  ASM_SIMP_TAC[ARITH_RULE `5 <= n ==> 4 <= n`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&65 / &64 * &(ISQRT n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PSI_UBOUND_30 THEN
    SUBGOAL_THEN `(ISQRT n) EXP (SUC 1) <= 30 EXP (SUC 1)` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[EXP_MONO_LE; NOT_SUC]] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ARITH; ISQRT_WORKS] THEN
    UNDISCH_TAC `~(n >= 900)` THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &16 / &325) pow 2` MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `(a * b) * (a * b) = a * a * b * b`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ;
           REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&413` THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `~(n < 413)` THEN ARITH_TAC);;
```

### Informal statement
This theorem states that for any natural number $n \geq 5$, we have:

$$\frac{1}{2} \cdot n \leq \theta(n)$$

where $\theta(n)$ is the sum of the natural logarithms of all prime numbers $p$ with $1 \leq p \leq n$, i.e.,

$$\theta(n) = \sum_{1 \leq p \leq n, \, p \text{ prime}} \ln(p)$$

### Informal proof
The proof is structured in three main cases:

1. For large values ($n \geq 900$):
   * We use the relation between $\psi(n)$ and $\theta(n)$ from `PSI_THETA`: $\psi(n) \leq \theta(n) + 2 \cdot \psi(\text{ISQRT}(n))$
   * We apply the lower bound for $\psi(n)$ from `PSI_LBOUND_3_5`: $\frac{3}{5} \cdot n \leq \psi(n)$ for $n \geq 4$
   * We use the upper bound for $\psi(\text{ISQRT}(n))$ from `PSI_UBOUND_3_2`: $\psi(\text{ISQRT}(n)) \leq \frac{3}{2} \cdot \text{ISQRT}(n)$
   * By algebraic manipulation, we show that $\frac{1}{2} \cdot n \leq \theta(n)$ by establishing that 
     $\text{ISQRT}(n)^2 \leq (\frac{n}{30})^2$, which is true for $n \geq 900$

2. For small values ($5 \leq n < 413$):
   * We use explicit computation of $\theta$ values for these finite cases
   * The values are verified using conversion tactics that compute logarithms of numbers 
     (`LN_N2_CONV` and `REALCALC_REL_CONV`)

3. For medium values ($413 \leq n < 900$):
   * Similar to the large case, but using a tighter bound for $\psi(\text{ISQRT}(n))$
   * We apply `PSI_UBOUND_30`: $\psi(m) \leq \frac{65}{64} \cdot m$ for $m \leq 30$
   * This is applicable since for $n < 900$, we have $\text{ISQRT}(n) \leq 30$
   * Using algebraic manipulations, we derive that $\frac{1}{2} \cdot n \leq \theta(n)$ for this range

The proof uses a combination of previously established bounds on the functions $\psi$ and $\theta$, along with case analysis and numerical verification for small values.

### Mathematical insight
This theorem provides a lower bound for $\theta(n)$, the logarithmic sum of prime numbers up to $n$. The bound $\frac{1}{2} \cdot n \leq \theta(n)$ for $n \geq 5$ is a fundamental result in analytic number theory.

The function $\theta(n)$ is closely related to the prime counting function and the distribution of prime numbers. This lower bound is important because:

1. It confirms that $\theta(n)$ grows at least linearly with $n$
2. It's used in proving results about prime number distribution, including Chebyshev's bounds
3. The constant $\frac{1}{2}$ is non-trivial and close to optimal for elementary methods

This theorem is part of a collection of results establishing asymptotic behavior of number-theoretic functions without using the Prime Number Theorem, providing elementary bounds on the distribution of primes.

### Dependencies
- **Theorems:**
  - `REAL_MUL_RID`: $\forall x. x \cdot 1 = x$
  - `REAL_NOT_LE`: $\forall x,y. \neg(x \leq y) \Leftrightarrow y < x$
  - `REAL_LE_TRANS`: $\forall x,y,z. x \leq y \wedge y \leq z \Rightarrow x \leq z$
  - `REAL_LE_MUL`: $\forall x,y. 0 \leq x \wedge 0 \leq y \Rightarrow 0 \leq (x \cdot y)$
  - `REAL_POS`: $\forall n. 0 \leq n$
  - `LN_1`: $\ln(1) = 0$
  - `ISQRT_WORKS`: $\forall n. \text{ISQRT}(n)^2 \leq n \wedge n < (\text{ISQRT}(n)+1)^2$
  - `PSI_UBOUND_3_2`: $\forall n. \psi(n) \leq \frac{3}{2} \cdot n$
  - `PSI_LBOUND_3_5`: $\forall n. 4 \leq n \Rightarrow \frac{3}{5} \cdot n \leq \psi(n)$
  - `PSI_THETA`: $\forall n. \theta(n) + \psi(\text{ISQRT}(n)) \leq \psi(n) \wedge \psi(n) \leq \theta(n) + 2 \cdot \psi(\text{ISQRT}(n))$
  - `PSI_UBOUND_30`: $\forall n. n \leq 30 \Rightarrow \psi(n) \leq \frac{65}{64} \cdot n$

- **Definitions:**
  - `ISQRT`: $\text{ISQRT}(n) = @m. m^2 \leq n \wedge n < (m+1)^2$
  - `theta`: $\theta(n) = \sum_{i=1}^{n} \text{if prime}(i) \text{ then } \ln(i) \text{ else } 0$

### Porting notes
When porting this theorem to another system:

1. The proof heavily relies on numerical computation and case analysis which may require different approaches in other systems.

2. The `THETA_LIST` precomputed values would need to be recreated or replaced with a computational approach appropriate for the target system.

3. The logarithmic computations rely on `LN_N2_CONV`, which may need to be implemented differently in other systems.

4. The choice of case boundaries (5, 413, 900) might need adjustment depending on the numerical methods available in the target system.

5. Automating the numerical verification for small values might require custom tactics or computational capabilities in the target system.

---

## FLOOR_POS

### Name of formal statement
FLOOR_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_POS = prove
 (`!x. &0 <= x ==> &0 <= floor x`,
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x < &1` THENL
   [ASM_MESON_TAC[FLOOR_EQ_0; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(last(CONJUNCTS(SPEC `x:real` FLOOR))) THEN
  UNDISCH_TAC `~(x < &1)` THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers $x$, if $x \geq 0$, then $\lfloor x \rfloor \geq 0$.

Where $\lfloor x \rfloor$ denotes the floor function, which returns the greatest integer less than or equal to $x$.

### Informal proof
We proceed by case analysis on whether $x < 1$ or not:

* Case 1: $x < 1$
  
  In this case, since $0 \leq x < 1$, by theorem `FLOOR_EQ_0`, we have $\lfloor x \rfloor = 0$.
  Therefore, $\lfloor x \rfloor \geq 0$ holds trivially.

* Case 2: $x \geq 1$
  
  From the properties of the floor function (by `FLOOR`), we know that $\lfloor x \rfloor \leq x < \lfloor x \rfloor + 1$.
  Since $x \geq 1$, we have $\lfloor x \rfloor \leq x$ and $x \geq 1$.
  Combining these inequalities, we get $\lfloor x \rfloor \geq 0$.

Therefore, for all $x \geq 0$, we have $\lfloor x \rfloor \geq 0$.

### Mathematical insight
This theorem establishes a basic property of the floor function: the floor of a non-negative real number is also non-negative. This is intuitive since the floor function returns the greatest integer less than or equal to its argument. If that argument is non-negative, then its floor cannot be negative.

While the statement may seem obvious, formal systems require explicit proofs for such properties. This result is useful in many contexts where one needs to establish bounds on integer-valued functions derived from real values, particularly in number theory and analysis.

### Dependencies
- `FLOOR_EQ_0`: States that $\lfloor x \rfloor = 0$ if and only if $0 \leq x < 1$
- `FLOOR`: States the key properties of the floor function: $\lfloor x \rfloor$ is an integer, $\lfloor x \rfloor \leq x$, and $x < \lfloor x \rfloor + 1$
- `REAL_LE_REFL`: States that $x \leq x$ for all real numbers $x$

### Porting notes
When porting this theorem to other proof assistants, ensure that:
1. The floor function is defined with the same properties as in HOL Light (greatest integer less than or equal to x)
2. The case analysis structure is preserved (considering $x < 1$ and $x \geq 1$ separately)
3. The real arithmetic solver in the target system can handle the necessary inequalities, or you may need to prove them explicitly

---

## FLOOR_NUM_EXISTS

### Name of formal statement
FLOOR_NUM_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_NUM_EXISTS = prove
 (`!x. &0 <= x ==> ?k. floor x = &k`,
  REPEAT STRIP_TAC THEN MP_TAC(CONJUNCT1(SPEC `x:real` FLOOR)) THEN
  REWRITE_TAC[integer] THEN
  ASM_MESON_TAC[FLOOR_POS; REAL_ARITH `&0 <= x ==> (abs x = x)`]);;
```

### Informal statement
For all real numbers $x$, if $x \geq 0$, then there exists a natural number $k$ such that $\lfloor x \rfloor = k$, where $\lfloor x \rfloor$ denotes the floor function.

### Informal proof
The proof shows that for any non-negative real number $x$, its floor can be expressed as a natural number.

* First, we apply the theorem `FLOOR` to obtain that $\lfloor x \rfloor$ is an integer.
* Then we use the definition of an integer by rewriting with `integer`, which means there exists some $z$ such that $\lfloor x \rfloor = z$.
* Since $x \geq 0$, we apply `FLOOR_POS` to conclude that $\lfloor x \rfloor \geq 0$.
* Finally, applying the arithmetic property that for any real number $y \geq 0$, $|y| = y$, we can deduce that $\lfloor x \rfloor$ is a non-negative integer, which means it can be written as a natural number $k$.

### Mathematical insight
This theorem establishes that the floor of a non-negative real number is not just an integer but specifically a natural number. This is a fundamental property that connects the floor function with natural numbers, which is particularly useful in applications involving discrete mathematics, computer science algorithms, and number theory.

The floor function bridges continuous mathematics (real numbers) with discrete mathematics (integers/natural numbers), and this theorem specifically characterizes the behavior for non-negative reals.

### Dependencies
- **Theorems**:
  - `FLOOR`: For all real numbers $x$, $\lfloor x \rfloor$ is an integer, $\lfloor x \rfloor \leq x$, and $x < \lfloor x \rfloor + 1$.
  - `FLOOR_POS`: For all real numbers $x$, if $x \geq 0$ then $\lfloor x \rfloor \geq 0$.
- **Definitions**:
  - `integer`: Definition of what it means for a real number to be an integer.

### Porting notes
When porting this theorem:
1. Ensure that the target system has a floor function with the same properties.
2. Verify that the target system's definition of integers and natural numbers aligns with HOL Light's.
3. The proof relies on the arithmetic fact that absolute value of a non-negative number equals the number itself, which should be available in most systems but may need to be explicitly applied.

---

## FLOOR_DIV_INTERVAL

### Name of formal statement
FLOOR_DIV_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DIV_INTERVAL = prove
 (`!n d k. ~(d = 0)
           ==> ((floor(&n / &d) = &k) =
                  if k = 0 then &n < &d
                  else &n / &(k + 1) < &d /\ &d <= &n / &k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`; ARITH_RULE `0 < k + 1`] THEN
  REWRITE_TAC[REAL_MUL_AC; CONJ_ACI; REAL_OF_NUM_ADD]);;
```

### Informal statement
For all natural numbers $n$, $d$, and $k$, if $d \neq 0$, then $\lfloor\frac{n}{d}\rfloor = k$ if and only if:
- If $k = 0$, then $n < d$
- Otherwise, $\frac{n}{k+1} < d \leq \frac{n}{k}$

This theorem characterizes when the floor of the division of two natural numbers equals a specific natural number $k$.

### Informal proof
The proof proceeds by case analysis on whether $k = 0$ or not.

**Case 1**: If $k = 0$, we need to show that $\lfloor\frac{n}{d}\rfloor = 0$ if and only if $n < d$.
- We apply `FLOOR_EQ_0` which states that for any real $x$, $\lfloor x \rfloor = 0$ if and only if $0 \leq x < 1$.
- For $x = \frac{n}{d}$, we have $\lfloor\frac{n}{d}\rfloor = 0$ if and only if $0 \leq \frac{n}{d} < 1$.
- Since $n$ and $d$ are natural numbers with $d \neq 0$, we know that $\frac{n}{d} \geq 0$.
- Thus, the condition simplifies to $\frac{n}{d} < 1$, which is equivalent to $n < d$ (by multiplying both sides by $d$, noting that $d > 0$).

**Case 2**: If $k \neq 0$, we need to show that $\lfloor\frac{n}{d}\rfloor = k$ if and only if $\frac{n}{k+1} < d \leq \frac{n}{k}$.
- We apply `FLOOR_UNIQUE`, which states that for any real $x$ and integer $a$, $\lfloor x \rfloor = a$ if and only if $a \leq x < a+1$.
- For $x = \frac{n}{d}$ and $a = k$, we have $\lfloor\frac{n}{d}\rfloor = k$ if and only if $k \leq \frac{n}{d} < k+1$.
- This is equivalent to $kd \leq n < (k+1)d$ (multiplying by $d > 0$).
- Rearranging to isolate $d$: $\frac{n}{k+1} < d \leq \frac{n}{k}$.

Both cases together complete the proof.

### Mathematical insight
This theorem provides a precise characterization of when the floor of a fraction of natural numbers equals a specific integer $k$. It's particularly useful for analyzing integer division and modular arithmetic.

The relationship $\frac{n}{k+1} < d \leq \frac{n}{k}$ when $k \neq 0$ gives us bounds on $d$ in terms of $n$ and $k$. This can be useful for algorithmic applications involving integer division, such as finding all divisors that produce a specific quotient.

When $k = 0$, the condition simplifies to just $n < d$, which means the division results in a value less than 1.

### Dependencies
- **Theorems**:
  - `FLOOR_EQ_0`: $\forall x. (\lfloor x \rfloor = 0) \iff 0 \leq x < 1$
  - `FLOOR_UNIQUE`: $\forall x, a. \text{integer}(a) \land a \leq x \land x < a + 1 \iff (\lfloor x \rfloor = a)$
  - `INTEGER_CLOSED`: Various integer closure properties
  - `REAL_MUL_LZERO`: $\forall x. 0 \cdot x = 0$
  - `REAL_POS`: $\forall n. 0 \leq n$

### Porting notes
When porting this theorem:
1. Ensure that your system has a proper definition of the floor function with its basic properties.
2. Pay attention to the typing - in HOL Light, `&n` represents the injection from natural numbers to reals.
3. The handling of division by zero may differ between systems, so the precondition `~(d = 0)` should be carefully translated.
4. The case analysis on `k = 0` might be structured differently in other proof assistants.

---

## FLOOR_DIV_EXISTS

### Name of formal statement
FLOOR_DIV_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DIV_EXISTS = prove
 (`!n d. ~(d = 0)
         ==> ?k. (floor(&n / &d) = &k) /\
                 d * k <= n /\ n < d * (k + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. floor (&n / &d) = &k` MP_TAC THENL
   [ASM_SIMP_TAC[FLOOR_NUM_EXISTS; REAL_LE_DIV; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:num` THEN SIMP_TAC[] THEN ASM_SIMP_TAC[FLOOR_DIV_INTERVAL] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0; ADD_CLAUSES; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k + 1 /\ (~(k = 0) ==> 0 < k)`] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[CONJ_ACI]);;
```

### Informal statement
For all natural numbers $n$ and $d$ where $d \neq 0$, there exists a natural number $k$ such that $\lfloor \frac{n}{d} \rfloor = k$, and the following inequalities hold:
$d \cdot k \leq n < d \cdot (k + 1)$

In other words, when dividing $n$ by $d$, the floor of the quotient $\frac{n}{d}$ gives a number $k$ such that $k$ is the largest integer not exceeding $\frac{n}{d}$, and $k$ satisfies the given inequalities.

### Informal proof
We want to prove that there exists a $k$ such that $\lfloor\frac{n}{d}\rfloor = k$ and $d \cdot k \leq n < d \cdot (k + 1)$.

First, we establish the existence of $k$ such that $\lfloor\frac{n}{d}\rfloor = k$:
- By `FLOOR_NUM_EXISTS`, for any real number $x \geq 0$, there exists a natural number $k$ such that $\lfloor x \rfloor = k$.
- Since $d \neq 0$ and both $n$ and $d$ are natural numbers, we have $\frac{n}{d} \geq 0$ (by `REAL_LE_DIV` and `REAL_POS`).
- Therefore, there exists a natural number $k$ such that $\lfloor\frac{n}{d}\rfloor = k$.

Next, we need to show that this $k$ satisfies the inequalities $d \cdot k \leq n < d \cdot (k + 1)$:
- Using `FLOOR_DIV_INTERVAL`, we know that for $d \neq 0$:
  - If $k = 0$, then $\lfloor\frac{n}{d}\rfloor = 0$ if and only if $n < d$
  - If $k \neq 0$, then $\lfloor\frac{n}{d}\rfloor = k$ if and only if $\frac{n}{k+1} < d \leq \frac{n}{k}$

We consider these cases separately:
- When $k = 0$: We have $0 \leq n < d$, which is equivalent to $d \cdot 0 \leq n < d \cdot (0 + 1)$.
- When $k \neq 0$: We have $\frac{n}{k+1} < d \leq \frac{n}{k}$.
  - Rearranging $\frac{n}{k+1} < d$ gives $n < d \cdot (k+1)$.
  - Rearranging $d \leq \frac{n}{k}$ gives $d \cdot k \leq n$.
  - Thus we have $d \cdot k \leq n < d \cdot (k+1)$, which is what we wanted to prove.

Therefore, in both cases, the $k$ such that $\lfloor\frac{n}{d}\rfloor = k$ satisfies $d \cdot k \leq n < d \cdot (k + 1)$.

### Mathematical insight
This theorem establishes a fundamental connection between the floor function and integer division. It provides a precise characterization of what the floor of a quotient $\lfloor\frac{n}{d}\rfloor$ means in terms of inequalities involving the original numbers.

The key insight is that the result of the integer division $n$ divided by $d$ is the largest integer $k$ such that $d \cdot k \leq n$. The theorem captures this precisely and provides the upper bound $n < d \cdot (k + 1)$ as well, showing that $k$ is exactly the integer part of $\frac{n}{d}$.

This theorem is important in number theory and computer science, particularly in algorithms involving integer division and in establishing properties of various number-theoretic functions.

### Dependencies
- `REAL_POS`: For all natural numbers $n$, $0 \leq n$.
- `FLOOR_NUM_EXISTS`: For all real numbers $x \geq 0$, there exists a natural number $k$ such that $\lfloor x \rfloor = k$.
- `FLOOR_DIV_INTERVAL`: For all natural numbers $n$, $d$, and $k$ where $d \neq 0$, $\lfloor\frac{n}{d}\rfloor = k$ if and only if:
  - when $k = 0$: $n < d$
  - when $k \neq 0$: $\frac{n}{k+1} < d \leq \frac{n}{k}$

### Porting notes
When implementing this theorem in other proof assistants, note that:
1. The treatment of natural numbers and reals might differ between systems
2. The floor function might be defined differently or require separate import
3. Some systems may use different notation for division involving natural numbers
4. The handling of division by zero might require explicit attention

---

## FLOOR_HALF_INTERVAL

### Name of formal statement
FLOOR_HALF_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_HALF_INTERVAL = prove
 (`!n d. ~(d = 0)
         ==> (floor (&n / &d) - &2 * floor (&(n DIV 2) / &d) =
                if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                then &1 else &0)`,
  let lemma = prove(`ODD(k) ==> ~(k = 0)`,MESON_TAC[EVEN; NOT_EVEN]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n DIV 2` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  MAP_EVERY UNDISCH_TAC [`n DIV 2 < d * (k1 + 1)`; `d * k1 <= n DIV 2`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a ==> ~(b /\ c))`] THEN
  SIMP_TAC[GSYM NOT_LE; LE_LDIV_EQ; LE_RDIV_EQ; ARITH_EQ; lemma; ADD_EQ_0] THEN
  REWRITE_TAC[NOT_LE; NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `d * 2 * k1 < d * (k2 + 1) /\ d * k2 < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ARITH_RULE
     `2 * k1 < k2 + 1 /\ k2 < 2 * (k1 + 1)
      ==> (k2 = 2 * k1) \/ (k2 = 2 * k1 + 1)`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_ADD_SUB; REAL_SUB_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k1 + 1`) THEN
    ASM_REWRITE_TAC[ARITH_ODD; ODD_ADD; ODD_MULT] THEN
    ASM_MESON_TAC[MULT_AC]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `d * 2 * k1 < d * ((2 * k3 + 1) + 1) /\
                d * (2 * k3 + 1) < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * k1 < (2 * k3 + 1) + 1 /\ 2 * k3 + 1 < 2 * (k1 + 1)
    ==> (k3 = k1)`)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
Let $n$ and $d$ be natural numbers with $d \neq 0$. Then:

$$\lfloor \frac{n}{d} \rfloor - 2 \cdot \lfloor \frac{\lfloor n/2 \rfloor}{d} \rfloor = 
\begin{cases}
1 & \text{if } \exists k \text{ such that } k \text{ is odd and } \lfloor n/(k+1) \rfloor < d \leq \lfloor n/k \rfloor \\
0 & \text{otherwise}
\end{cases}$$

where $\lfloor x \rfloor$ denotes the floor function (greatest integer not exceeding $x$).

### Informal proof
The proof establishes when the difference between $\lfloor \frac{n}{d} \rfloor$ and $2 \cdot \lfloor \frac{\lfloor n/2 \rfloor}{d} \rfloor$ equals 1 versus 0.

- First, we note that for any odd number $k$, $k \neq 0$ (using lemma `ODD(k) ==> ~(k = 0)`).

- By applying `FLOOR_DIV_EXISTS`, we establish that there exist integers $k_1$ and $k_2$ such that:
  * $\lfloor \frac{n}{d} \rfloor = k_2$
  * $d \cdot k_2 \leq n < d \cdot (k_2 + 1)$
  * $\lfloor \frac{\lfloor n/2 \rfloor}{d} \rfloor = k_1$
  * $d \cdot k_1 \leq \lfloor n/2 \rfloor < d \cdot (k_1 + 1)$

- From these inequalities, we derive:
  * $d \cdot 2 \cdot k_1 < d \cdot (k_2 + 1)$
  * $d \cdot k_2 < d \cdot 2 \cdot (k_1 + 1)$

- Cancelling $d$ (since $d \neq 0$), we get:
  * $2k_1 < k_2 + 1$
  * $k_2 < 2(k_1 + 1)$

- These inequalities imply that $k_2$ must equal either $2k_1$ or $2k_1 + 1$.

- If $k_2 = 2k_1$, then $\lfloor \frac{n}{d} \rfloor - 2 \cdot \lfloor \frac{\lfloor n/2 \rfloor}{d} \rfloor = k_2 - 2k_1 = 0$.

- If $k_2 = 2k_1 + 1$, then $\lfloor \frac{n}{d} \rfloor - 2 \cdot \lfloor \frac{\lfloor n/2 \rfloor}{d} \rfloor = k_2 - 2k_1 = 1$.

- The proof then shows that $k_2 = 2k_1 + 1$ if and only if there exists an odd number $k$ such that $\lfloor n/(k+1) \rfloor < d \leq \lfloor n/k \rfloor$.

- For such a $k$, we establish that $k = 2k_1 + 1$ (an odd number), and the conditions on dividing $n$ by $k$ and $k+1$ correspond exactly to the case distinction in our theorem.

### Mathematical insight
This theorem characterizes when the floor of a division differs from twice the floor of half the division. This difference can only be 0 or 1, and the theorem provides a criterion for when it's 1 based on the existence of an odd divisor with specific properties.

The result is useful in number theory contexts, particularly when analyzing division with remainder and floor functions. It helps in understanding how the floor function interacts with arithmetic operations like division and multiplication.

### Dependencies
- **Theorems:**
  - `FLOOR_DIV_EXISTS`: For any non-zero divisor $d$ and number $n$, there exists a $k$ such that $\lfloor \frac{n}{d} \rfloor = k$ and $d \cdot k \leq n < d \cdot (k+1)$
  - `REAL_SUB_REFL`: $\forall x. x - x = 0$

### Porting notes
When implementing this theorem in other proof assistants:
- Ensure the floor function is properly defined
- The theorem heavily relies on division and floor properties of natural numbers
- The proof uses case splitting based on parity (odd/even) which might require different tactics in other systems
- Pay attention to how division of natural numbers is handled, as some systems might have different conventions for division with remainder

---

## SUM_EXPAND_LEMMA

### SUM_EXPAND_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_EXPAND_LEMMA = prove
 (`!n m k. (m + 2 * k = n)
         ==> (sum (1,n DIV (2 * k + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0) =
              sum (1,n) (\d. --(&1) pow (d + 1) * psi (n DIV d)) -
              sum (1,2 * k)
                  (\d. --(&1) pow (d + 1) * psi (n DIV d)))`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[DIV_0; ADD_EQ_0; ARITH_EQ; REAL_SUB_REFL; sum]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[DIV_REFL; SUM_1; DIV_1; REAL_SUB_REFL] THEN
    SUBGOAL_THEN `n DIV (n + 1) = 0` (fun th -> REWRITE_TAC[th; sum]) THEN
    ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `n < n + 1 /\ ~(n + 1 = 0)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM ADD1; ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC; sum; SUM_1] THEN
    REWRITE_TAC[REAL_ADD_SUB; mangoldt] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIMEPOW_CONV) THEN
    REWRITE_TAC[COND_ID] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC] THEN REWRITE_TAC(LN_1::PSI_LIST 1);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 2 < m`] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ANTS_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o TOP_DEPTH_CONV)
   [ARITH_RULE `2 * SUC k = SUC(SUC(2 * k))`; sum] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(s - ss = x + y) ==> (ss = a - ((b + x) + y)) ==> (s = a - b)`) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; ARITH_EVEN; EVEN; EVEN_MULT] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[psi; GSYM real_sub] THEN
  MATCH_MP_TAC(REAL_ARITH `!b. (a - b = d) /\ (b = c) ==> (a - c = d)`) THEN
  EXISTS_TAC `sum (1,n DIV (SUC (2 * k) + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_DIFFERENCES_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:num` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k + 1`) THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= r <=> n < 1 + r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < r <=> 1 + n <= r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * k + 1) + 1 = SUC(2 * k) + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_MORETERMS_EQ THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC k + 1 = 2 * k + 3`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `oj:num` MP_TAC) THEN
  REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 + a <= b ==> a < b`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a < 1 + b ==> a <= b`)) THEN
  SIMP_TAC[GSYM NOT_LE; LE_RDIV_EQ; LE_LDIV_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[NOT_LE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(2 * j + 1) * r < (2 * k + 3) * r /\
                (2 * k + 2) * r < (2 * j + 2) * r`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * j + 1 < 2 * k + 3 /\ 2 * k + 2 < 2 * j + 2 ==> (j = k)`)) THEN
  ASM_MESON_TAC[LET_TRANS; LT_REFL; MULT_AC]);;
```

### Informal statement
For all natural numbers $n$, $m$, and $k$ where $m + 2k = n$, the following equality holds:

$$\sum_{d=1}^{\lfloor n/(2k+1) \rfloor} \left\{ \begin{array}{ll}
\Lambda(d) & \text{if } \exists k \text{ such that } k \text{ is odd and } \lfloor n/(k+1) \rfloor < d \leq \lfloor n/k \rfloor \\
0 & \text{otherwise}
\end{array} \right\} = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor) - \sum_{d=1}^{2k} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor)$$

where:
- $\Lambda(d)$ is the von Mangoldt function (denoted as `mangoldt d` in HOL Light)
- $\psi(n)$ is the Chebyshev psi function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Informal proof
We prove this by well-founded induction on $m$. The proof proceeds by examining several base cases and then establishing the inductive step.

**Base Cases:**

1. **Case $n = 0$:**
   - When $n = 0$, both sides of the equation reduce to $0$ since $\psi(0) = \ln(1) = 0$, and the sums become empty.

2. **Case $m = 0$ (with $n \neq 0$):**
   - If $m = 0$, then $n = 2k$.
   - The left side simplifies to $\sum_{d=1}^{1} [...]$ since $n/(2k+1) = n/(n+1) = 0$.
   - The right side becomes $\sum_{d=1}^{n} (-1)^{d+1}\psi(\lfloor n/d \rfloor) - \sum_{d=1}^{n} (-1)^{d+1}\psi(\lfloor n/d \rfloor) = 0$.

3. **Case $m = 1$ (with $n \neq 0$):**
   - If $m = 1$, then $n = 1 + 2k$.
   - We simplify the dividend $n/(2k+1) = (1+2k)/(2k+1) = 1$.
   - The left side becomes $\Lambda(1)$ if the condition is satisfied, and $0$ otherwise.
   - Since $1$ is not a prime power, $\Lambda(1) = 0$.
   - The right side reduces to subtraction of appropriate terms.

**Inductive Step:**
- Assume the theorem holds for $m - 2$ (where $m > 1$).
- We want to prove it holds for $m$.
- Let $n = m + 2k$ and show the equality holds.
- Using the induction hypothesis with $k' = k+1$, we get:
  $$\sum_{d=1}^{\lfloor n/(2k'+1) \rfloor} [...] = \sum_{d=1}^{n} (-1)^{d+1}\psi(\lfloor n/d \rfloor) - \sum_{d=1}^{2k'} (-1)^{d+1}\psi(\lfloor n/d \rfloor)$$

- We then manipulate this equation to obtain the desired result for parameter $k$.
- The key insight is using the relationship between consecutive terms in the sums.
- Using properties of divisibility and alternating sums, we analyze how terms change between the sums for $k$ and $k+1$.
- We use the fact that $2 \cdot (k+1) = 2k + 2$ and related arithmetic manipulations.
- Finally, we show that the difference between the sums with parameters $k$ and $k+1$ has a particular form.

The proof finishes by applying algebraic manipulations and showing that the equation holds for all $m$, given the base cases and inductive step.

### Mathematical insight
This theorem provides an expansion formula relating sums involving the Mangoldt function ($\Lambda$) and the Chebyshev psi function ($\psi$). The equation expresses a sum of specific Mangoldt function values (selected by divisibility conditions) in terms of alternating sums of psi function values.

This type of relationship is important in analytic number theory, where sums involving the Mangoldt function are crucial for studying the distribution of prime numbers. The formula offers a way to rewrite certain sums involving $\Lambda(d)$ in terms of $\psi$ functions evaluated at integer divisions, which is often more manageable for asymptotic analysis.

The parameter $k$ provides flexibility in applying this result, allowing one to choose different summation ranges based on the specific problem requirements.

### Dependencies
- **Theorems:**
  - `REAL_SUB_REFL`: For all real $x$, $x - x = 0$
  - `sum`: Basic properties of summation: $\sum_{i=n}^{0} f(i) = 0$ and $\sum_{i=n}^{m+1} f(i) = \sum_{i=n}^{m} f(i) + f(n+m)$
  - `SUM_MORETERMS_EQ`: If $n \leq p$ and $\forall r (m+n \leq r \wedge r < m+p \Rightarrow f(r) = 0)$, then $\sum_{i=m}^{p} f(i) = \sum_{i=m}^{n} f(i)$
  - `SUM_DIFFERENCES_EQ`: If $n \leq p$ and $\forall r (m+n \leq r \wedge r < m+p \Rightarrow f(r) = g(r))$, then $\sum_{i=m}^{p} f(i) - \sum_{i=m}^{n} f(i) = \sum_{i=m}^{p} g(i) - \sum_{i=m}^{n} g(i)$
  - `LN_1`: $\ln(1) = 0$
  - `PRIMEPOW_CONV`: Conversion for primality test
  - `PSI_LIST`: List of values for the psi function

- **Definitions:**
  - `mangoldt`: Von Mangoldt function, defined as $\Lambda(d) = \ln(p)$ if $d = p^k$ for some prime $p$ and integer $k \geq 1$, and $0$ otherwise
  - `psi`: Chebyshev's psi function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Porting notes
When porting this theorem:
1. The proof relies heavily on arithmetic manipulations and divisibility properties.
2. The handling of special cases ($n=0$, $m=0$, $m=1$) should be carefully maintained.
3. The number-theoretic functions (Mangoldt function and Chebyshev psi function) need to be defined consistently.
4. Care is needed when translating floor division operations (represented as `DIV` in HOL Light).
5. The well-founded induction strategy might need to be adapted to the induction principles available in the target system.
6. The conditional sums and logical conditions within the summation may require special attention in systems with different syntax for handling such expressions.

---

## FACT_EXPAND_PSI

### FACT_EXPAND_PSI
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FACT_EXPAND_PSI = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) =
          sum(1,n) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN REWRITE_TAC[MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n DIV 2) (\d. mangoldt d * floor (&(n DIV 2) / &d)) =
    sum (1,n) (\d. mangoldt d * floor (&(n DIV 2) / &d))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `n = n DIV 2 + (n - n DIV 2)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [MESON_TAC[SUB_ADD; DIV_LE; ADD_SYM; NUM_REDUCE_CONV `2 = 0`];
           ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE; FLOOR_EQ_0] THEN DISJ2_TAC THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    SUBGOAL_THEN `0 < r /\ n DIV 2 < r` MP_TAC THENL
     [UNDISCH_TAC `1 + n DIV 2 <= r` THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `m * x - &2 * m * y = m * (x - &2 * y)`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                  then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FLOOR_HALF_INTERVAL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `0`] SUM_EXPAND_LEMMA) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; sum; REAL_SUB_RZERO; DIV_1]);;
```

### Informal statement

For all natural numbers $n$, the following equality holds:
$$\ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(\lfloor n/2 \rfloor)) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor)$$

where:
- $\text{FACT}(n)$ represents the factorial of $n$
- $\ln$ is the natural logarithm
- $\psi(n)$ is the Chebyshev psi function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$
- $\Lambda(d)$ is the von Mangoldt function: $\Lambda(d) = \ln(p)$ if $d = p^k$ for some prime $p$ and integer $k \geq 1$, and $\Lambda(d) = 0$ otherwise

### Informal proof

The proof combines results from number theory related to the factorial function and the Chebyshev psi function. The key steps are:

1. We start with the result from `MANGOLDT` theorem that connects the factorial function to the von Mangoldt function:
   $$\ln(\text{FACT}(n)) = \sum_{d=1}^{n} \Lambda(d) \cdot \lfloor n/d \rfloor$$

2. First, we show that:
   $$\sum_{d=1}^{\lfloor n/2 \rfloor} \Lambda(d) \cdot \lfloor \lfloor n/2 \rfloor/d \rfloor = \sum_{d=1}^{n} \Lambda(d) \cdot \lfloor \lfloor n/2 \rfloor/d \rfloor$$

   This is true because for any $d > \lfloor n/2 \rfloor$, we have $\lfloor \lfloor n/2 \rfloor/d \rfloor = 0$. The proof shows this by:
   - Writing $n = \lfloor n/2 \rfloor + (n - \lfloor n/2 \rfloor)$
   - Using the sum splitting property
   - Showing that the second part of the sum equals zero because $\lfloor \lfloor n/2 \rfloor/d \rfloor = 0$ for $d > \lfloor n/2 \rfloor$

3. We then rewrite the target expression using the distributive property of multiplication over subtraction:
   $$\ln(\text{FACT}(n)) - 2 \cdot \ln(\text{FACT}(\lfloor n/2 \rfloor)) = \sum_{d=1}^{n} \Lambda(d) \cdot (\lfloor n/d \rfloor - 2 \cdot \lfloor \lfloor n/2 \rfloor/d \rfloor)$$

4. Using the `FLOOR_HALF_INTERVAL` theorem, we prove that:
   $$\lfloor n/d \rfloor - 2 \cdot \lfloor \lfloor n/2 \rfloor/d \rfloor = \begin{cases}
   1 & \text{if } \exists k \text{ such that } k \text{ is odd}, \lfloor n/(k+1) \rfloor < d \leq \lfloor n/k \rfloor \\
   0 & \text{otherwise}
   \end{cases}$$

5. This allows us to reformulate our sum as:
   $$\sum_{d=1}^{n} \Lambda(d) \cdot (\lfloor n/d \rfloor - 2 \cdot \lfloor \lfloor n/2 \rfloor/d \rfloor) = \sum_{d=1}^{n} \begin{cases}
   \Lambda(d) & \text{if } \exists k \text{ such that } k \text{ is odd}, \lfloor n/(k+1) \rfloor < d \leq \lfloor n/k \rfloor \\
   0 & \text{otherwise}
   \end{cases}$$

6. Finally, we apply the `SUM_EXPAND_LEMMA` with parameters $n$, $n$, and $0$ to convert this sum into the alternating sum of the Chebyshev psi function:
   $$\sum_{d=1}^{n} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor)$$

The proof completes by simplifying the resulting expression.

### Mathematical insight

This theorem provides a connection between the factorial function and the Chebyshev psi function through an alternating sum. The Chebyshev psi function $\psi(n)$ sums the logarithms of prime powers up to $n$, which makes it a key function in analytic number theory.

The formula expresses the difference between $\ln(n!)$ and $2\ln(\lfloor n/2 \rfloor!)$ in terms of an alternating sum involving $\psi$. This can be viewed as a variant of the prime number theorem in a form that relates to factorials rather than directly to the counting of primes.

The result is also related to Chebyshev's approach to estimating prime counting functions and understanding the asymptotic behavior of the factorial function. The alternating nature of the sum provides an elegant algebraic structure to this number-theoretic relationship.

### Dependencies

- **Theorems**:
  - `MANGOLDT`: Connects the factorial function to the von Mangoldt function
  - `FLOOR_HALF_INTERVAL`: Provides a formula for the difference between floor functions
  - `SUM_EXPAND_LEMMA`: Converts certain sums into alternating sums
  - `FLOOR_EQ_0`: Characterizes when floor equals zero
  - `REAL_MUL_RID`, `REAL_MUL_RZERO`, `REAL_SUB_RZERO`: Basic properties of real arithmetic
  - `REAL_POS`: Positivity of real numbers
  - `SUM_EQ`, `SUM_CMUL`, `SUM_SUB`, `SUM_SPLIT`, `SUM_EQ_0`: Properties of summation

- **Definitions**:
  - `ln`: Natural logarithm
  - `mangoldt`: Von Mangoldt function
  - `psi`: Chebyshev psi function

### Porting notes

When porting this theorem:

1. The representation of the factorial function may differ between systems. Some systems might use a dedicated factorial function while others might define it recursively.

2. The floor function might be represented differently or have different notational conventions.

3. The von Mangoldt function and Chebyshev psi function are specialized number theory concepts that might need to be defined if they don't exist in the target system.

4. The proof relies on several helper theorems about floor functions and summations. These might need to be ported first or alternative proofs might need to be developed using the target system's library.

5. The alternating sum pattern might be represented differently in other systems, potentially requiring adjustments to the statement or proof.

---

## PSI_MONO

### PSI_MONO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_MONO = prove
 (`!m n. m <= n ==> psi(m) <= psi(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; psi] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN REWRITE_TAC[MANGOLDT_POS]);;
```

### Informal statement
The theorem states that the Chebyshev's psi function is monotone increasing. Formally:

$$\forall m, n \in \mathbb{N},\; m \leq n \Rightarrow \psi(m) \leq \psi(n)$$

where $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ and $\Lambda$ is the Mangoldt function.

### Informal proof
The proof proceeds as follows:

1. We first use the fact that if $m \leq n$, then there exists $p$ such that $n = m + p$.

2. Then, using the definition of $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, we have:
   $$\psi(n) = \psi(m+p) = \sum_{d=1}^{m+p} \Lambda(d)$$

3. By the sum splitting property (`SUM_SPLIT`), we can write:
   $$\sum_{d=1}^{m+p} \Lambda(d) = \sum_{d=1}^{m} \Lambda(d) + \sum_{d=m+1}^{p} \Lambda(d)$$
   
   So $\psi(n) = \psi(m) + \sum_{d=m+1}^{p} \Lambda(d)$

4. Then $\psi(m) \leq \psi(n)$ follows because $\psi(n) = \psi(m) + \sum_{d=m+1}^{p} \Lambda(d)$ and $\sum_{d=m+1}^{p} \Lambda(d) \geq 0$. 

5. The non-negativity of the sum comes from `SUM_POS_GEN` and the fact that the Mangoldt function is always non-negative (`MANGOLDT_POS`).

### Mathematical insight
The monotonicity of Chebyshev's psi function is a fundamental property following directly from its definition as a sum of Mangoldt function values. This theorem establishes that as $n$ increases, we're adding more terms to the sum, and since each Mangoldt function value is non-negative, the sum can only increase.

The psi function plays a crucial role in analytic number theory, particularly in the study of the distribution of prime numbers. Its asymptotic behavior is closely related to the Prime Number Theorem, and its monotonicity is essential in various proofs involving prime number bounds.

### Dependencies
- **Definitions**:
  - `psi`: Defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the Mangoldt function.

- **Theorems**:
  - `SUM_POS_GEN`: If $f(n) \geq 0$ for all $n \geq m$, then $\sum_{i=m}^{n} f(i) \geq 0$.
  - `SUM_SPLIT`: $\sum_{i=m}^{n} f(i) + \sum_{i=m+n}^{p} f(i) = \sum_{i=m}^{n+p} f(i)$.
  - `MANGOLDT_POS`: The Mangoldt function is non-negative: $\Lambda(d) \geq 0$ for all $d$.

### Porting notes
When porting this theorem to other systems, ensure that:
1. The Mangoldt function is properly defined
2. The sum notation and manipulation rules are available
3. The basic properties of the Mangoldt function (like non-negativity) are established

---

## PSI_POS

### Name of formal statement
PSI_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_POS = prove
 (`!n. &0 <= psi(n)`,
  SUBGOAL_THEN `psi(0) = &0` (fun th -> MESON_TAC[th; PSI_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PSI_LIST 0));;
```

### Informal statement
For all natural numbers $n$, $\psi(n) \geq 0$, where $\psi$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ with $\Lambda$ being the von Mangoldt function.

### Informal proof
The proof shows that $\psi(n) \geq 0$ for all natural numbers $n$ by establishing two key facts:
1. $\psi(0) = 0$
2. $\psi$ is a monotonically increasing function (from the theorem `PSI_MONO`)

Step 1: We first establish the subgoal $\psi(0) = 0$.
- This is proven by rewriting using the theorem `LN_1` (which states that $\ln(1) = 0$) and `PSI_LIST 0` (which includes the fact that $\psi(0) = \ln(1)$).

Step 2: Once we have $\psi(0) = 0$ and the monotonicity of $\psi$, we can conclude that for all $n \geq 0$, $\psi(n) \geq \psi(0) = 0$.
- This follows from applying `PSI_MONO` and the fact that $0 \leq n$ for all natural numbers $n$ (indicated by `LE_0`).

### Mathematical insight
The Chebyshev function $\psi(n)$ is an important function in analytic number theory, particularly in the study of the distribution of prime numbers. The non-negativity of $\psi(n)$ is a basic property that follows from its definition as a sum of non-negative values (as the von Mangoldt function $\Lambda(n)$ is always non-negative).

This property is fundamental when studying the asymptotic behavior of $\psi(n)$ in relation to the Prime Number Theorem. The non-negativity combined with the monotonicity of $\psi$ provides a foundation for further analysis of this function.

### Dependencies
- Theorems:
  - `LN_1`: States that $\ln(1) = 0$
  - `PSI_LIST`: Contains various facts about $\psi(n)$ for specific values, including $\psi(0) = \ln(1)$
  - `PSI_MONO`: States that if $m \leq n$ then $\psi(m) \leq \psi(n)$ (monotonicity of $\psi$)
- Definitions:
  - `psi`: Defines the Chebyshev function $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ where $\Lambda$ is the von Mangoldt function

### Porting notes
When porting this theorem to another proof assistant:
- Ensure the von Mangoldt function and Chebyshev function are properly defined first
- The proof is relatively straightforward once these definitions and the basic properties (`LN_1` and `PSI_MONO`) are in place
- Some systems might require explicit reasoning about summations of non-negative terms

---

## PSI_EXPANSION_CUTOFF

### PSI_EXPANSION_CUTOFF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_EXPANSION_CUTOFF = prove
 (`!n m p. m <= p
         ==> sum(1,2 * m) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * p) (\d. --(&1) pow (d + 1) * psi(n DIV d)) /\
             sum(1,2 * p + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * m + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  X_GEN_TAC `m:num` THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = SUC(SUC(2 * n))`;
              ARITH_RULE `SUC(SUC n) + 1 = SUC(SUC(n + 1))`; sum] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `s1 <= s1' /\ s2' <= s2
    ==> &0 <= a + b /\ &0 <= --c + --d
        ==> s1 <= (s1' + a) + b /\ (s2' + c) + d <= s2`)) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN; EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= a + --b <=> b <= a`] THEN
  CONJ_TAC THEN MATCH_MP_TAC PSI_MONO THEN
  MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, $m$, and $p$, if $m \leq p$, then:

1. $\sum_{d=1}^{2m} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor) \leq \sum_{d=1}^{2p} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor)$
2. $\sum_{d=1}^{2p+1} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor) \leq \sum_{d=1}^{2m+1} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor)$

where $\psi(n)$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, and $\Lambda(d)$ is the Mangoldt function.

### Informal proof
We prove this theorem by induction on the difference between $p$ and $m$.

First, we use the fact that $m \leq p$ means there exists some $k$ such that $p = m + k$. We rewrite the goal to use this representation and then perform induction on $k$.

**Base case**: When $k = 0$, we have $p = m$, and both inequalities become equalities, which are trivially true by reflexivity of $\leq$.

**Inductive step**: Assume the result holds for some $k$. We need to prove it for $k+1$.

We rewrite the terms involving $2 \cdot \text{SUC}(k+m)$ using arithmetic properties:
- $2 \cdot \text{SUC}(n) = \text{SUC}(\text{SUC}(2 \cdot n))$
- $\text{SUC}(\text{SUC}(n)) + 1 = \text{SUC}(\text{SUC}(n+1))$

Then we apply the summation recurrence relation to break down the sums. For the first inequality, we get:
- $\sum_{d=1}^{2(m+k+1)} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor) = \sum_{d=1}^{2(m+k)} (-1)^{d+1} \cdot \psi(\lfloor n/d \rfloor) + (-1)^{2(m+k)+1+1} \cdot \psi(\lfloor n/(2(m+k)+1) \rfloor) + (-1)^{2(m+k)+2+1} \cdot \psi(\lfloor n/(2(m+k)+2) \rfloor)$

Similarly for the second inequality.

The proof then simplifies the powers of $-1$ using the fact that $(-1)^{d+1}$ is $-1$ when $d$ is even and $1$ when $d$ is odd. Since $2(m+k)+1$ is odd and $2(m+k)+2$ is even, we get appropriate simplifications.

Finally, we use the monotonicity of $\psi$ (theorem PSI_MONO) combined with the monotonicity of the division function to show that:
- $\psi(\lfloor n/(2(m+k)+1) \rfloor) \leq \psi(\lfloor n/(2m+1) \rfloor)$
- $\psi(\lfloor n/(2m+2) \rfloor) \leq \psi(\lfloor n/(2(m+k)+2) \rfloor)$

These inequalities, along with the induction hypothesis, establish the desired result.

### Mathematical insight
This theorem establishes monotonicity properties of certain alternating sums involving the second Chebyshev function $\psi$. These properties are crucial for analyzing the behavior of the Chebyshev function in number theory, particularly in the context of studying the distribution of prime numbers.

The theorem captures an interesting pattern: sums with an even upper limit ($2m$ or $2p$) increase when the upper limit increases, while sums with an odd upper limit ($2m+1$ or $2p+1$) decrease when the upper limit increases. This alternating behavior is related to the alternating signs in the summation and plays an important role in analytic number theory.

These types of cutoff properties are often used in the proofs of number theoretic results, particularly those related to the Prime Number Theorem and its variations.

### Dependencies
- **Theorems**:
  - `REAL_NEG_NEG`: $\forall x. -(-x) = x$
  - `REAL_LE_REFL`: $\forall x. x \leq x$
  - `sum`: $(sum(n,0) f = 0) \wedge (sum(n,SUC m) f = sum(n,m) f + f(n + m))$
  - `PSI_MONO`: $\forall m\ n. m \leq n \Rightarrow \psi(m) \leq \psi(n)$
- **Definitions**:
  - `psi`: $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, where $\Lambda$ is the Mangoldt function

### Porting notes
When porting this theorem:
1. Ensure that your system has a well-defined second Chebyshev function $\psi$ and Mangoldt function $\Lambda$.
2. The proof relies heavily on arithmetic simplifications and properties of the division operation, so these need to be available in your target system.
3. Note that HOL Light's `DIV` operator corresponds to floor division, which should be handled accordingly in the target system.
4. The alternating pattern of signs is crucial, so ensure that the powers of -1 are correctly translated.
5. The induction pattern might require adaptation depending on how your system handles induction on differences between variables.

---

## FACT_PSI_BOUND_ODD

### FACT_PSI_BOUND_ODD
- FACT_PSI_BOUND_ODD

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_ODD = prove
 (`!n k. ODD(k)
         ==> ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
             <= sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(b = a) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,SUC(2 * n DIV 2))
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;
```

### Informal statement
For any natural numbers $n$ and $k$, if $k$ is odd, then:
$$\ln(n!) - 2 \ln((n \div 2)!) \leq \sum_{d=1}^{k} (-1)^{d+1} \cdot \psi(n \div d)$$

where $\psi(n)$ is the Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ with $\Lambda$ being the von Mangoldt function, and $\div$ denotes integer division.

### Informal proof
This proof establishes an upper bound for the expression $\ln(n!) - 2\ln((n \div 2)!)$ in terms of a finite sum involving the Chebyshev psi function.

* First, we use `FACT_EXPAND_PSI` which tells us that 
  $$\ln(n!) - 2\ln((n \div 2)!) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi(n \div d)$$

* We consider two cases:
  1. When $k \leq n$:
     - Let $m$ be such that $k = 2m + 1$ (since $k$ is odd)
     - We want to show that the sum up to $k$ is at least the full sum up to $n$
     - We prove this by showing:
       * The sum up to $\text{SUC}(2 \cdot (n \div 2))$ is an intermediate value
       * Applying `PSI_EXPANSION_CUTOFF` with the condition $m \leq n \div 2$
       * This gives us the required inequality

  2. When $k > n$:
     - We show that the sum from $n+1$ to $k$ contributes no additional terms
     - This is because $n \div r = 0$ for all $r > n$
     - And $\psi(0) = \ln(1) = 0$, so these terms are zero

* For the first case, we analyze what happens when we write $n = 2q + r$ where $q = n \div 2$ and $r = n \bmod 2$
* When $r = 0$, we get $n = 2q$, and the inequality reduces to equality
* When $r = 1$, we get $n = 2q + 1$, and we need to show that the additional term is non-negative
* This follows from the positivity of the $\psi$ function (`PSI_POS`) and properties of the alternating powers of $-1$

### Mathematical insight
This theorem establishes an important bound for the logarithm of factorials in terms of the Chebyshev $\psi$ function. The bound is particularly useful in number theory, especially in estimates related to prime numbers.

The result has a special form when $k$ is odd, which gives a cleaner alternating pattern in the sum. The relationship between the factorial function and the Chebyshev function highlights deep connections in analytic number theory.

This theorem is part of a broader set of results used to establish the Bertrand's postulate (that there's always a prime between $n$ and $2n$ for $n > 1$) and related number-theoretic results.

### Dependencies
- **Theorems**:
  - `REAL_LE_REFL`: $\forall x. x \leq x$
  - `REAL_LE_TRANS`: $\forall x\ y\ z. x \leq y \land y \leq z \Rightarrow x \leq z$
  - `sum`: $(sum(n,0) f = 0) \land (sum(n,SUC m) f = sum(n,m) f + f(n + m))$
  - `SUM_MORETERMS_EQ`: $\forall m\ n\ p. n \leq p \land (\forall r. m + n \leq r \land r < m + p \Rightarrow (f(r) = 0)) \Rightarrow (sum(m,p) f = sum(m,n) f)$
  - `LN_1`: $\ln(1) = 0$
  - `PSI_LIST`: $\psi(0) = \ln(1)$
  - `FACT_EXPAND_PSI`: $\forall n. \ln(n!) - 2 \cdot \ln((n \div 2)!) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi(n \div d)$
  - `PSI_POS`: $\forall n. 0 \leq \psi(n)$
  - `PSI_EXPANSION_CUTOFF`: Theorem about monotonicity of partial sums of the psi expansion

- **Definitions**:
  - `ln`: $\ln x = \epsilon u. \exp(u) = x$
  - `psi`: $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Porting notes
When porting this theorem, special attention should be paid to:
1. The handling of integer division (represented as $\div$ in the statement)
2. The formalization of the Chebyshev psi function, which depends on the von Mangoldt function
3. The handling of factorial in the target system
4. The alternating sign in the sum, which requires careful treatment

Most proof assistants have libraries for number theory that already include these functions, but their exact definitions might differ slightly.

---

## FACT_PSI_BOUND_EVEN

### FACT_PSI_BOUND_EVEN
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_EVEN = prove
 (`!n k. EVEN(k)
         ==> sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))
             <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(a = b) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,2 * n DIV 2)
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;
```

### Informal statement
For all natural numbers $n$ and $k$, if $k$ is even, then:

$$\sum_{d=1}^{k} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right) \leq \ln(n!) - 2 \cdot \ln\left(\left\lfloor\frac{n}{2}\right\rfloor!\right)$$

where $\psi(n)$ is the second Chebyshev function defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$, with $\Lambda$ being the von Mangoldt function.

### Informal proof
We begin by applying `FACT_EXPAND_PSI`, which tells us that 
$$\ln(n!) - 2\ln\left(\left\lfloor\frac{n}{2}\right\rfloor!\right) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$$

We consider two cases:

1. If $k \leq n$:
   - Since $k$ is even, we can write $k = 2m$ for some natural number $m$.
   - We need to show that $\sum_{d=1}^{2m} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right) \leq \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$
   - From `PSI_EXPANSION_CUTOFF`, if $m \leq n/2$ then:
     $$\sum_{d=1}^{2m} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right) \leq \sum_{d=1}^{2 \cdot \lfloor n/2 \rfloor} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$$
   - We know $m \leq n/2$ because $2m = k \leq n$ implies $m \leq n/2$.

2. If $k > n$:
   - Then we have 
     $$\sum_{d=1}^{k} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$$
   - This is because for all $r$ where $n < r \leq k$, we have $\lfloor n/r \rfloor = 0$, and $\psi(0) = \ln(1) = 0$.

Let's now handle the remaining case with $k \leq n$. By the division theorem, $n = 2q + r$ where $q = \lfloor n/2 \rfloor$ and $r < 2$.

- If $r = 0$, then $n = 2q$, and thus $2 \cdot \lfloor n/2 \rfloor = n$. The right side of our desired inequality equals $\sum_{d=1}^{n} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$, and we already established our sum is less than or equal to this value.

- If $r = 1$, then $n = 2q + 1$, which means $2 \cdot \lfloor n/2 \rfloor = 2q < n$. The sum on the right side becomes:
  $$\sum_{d=1}^{2q} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right) + (-1)^{2q+2} \cdot \psi\left(\left\lfloor\frac{n}{2q+1}\right\rfloor\right)$$

  Since $2q+1$ is odd and $(-1)^{2q+2} = 1$, the last term is positive. Also, $\psi$ is non-negative by `PSI_POS`, so adding this term only makes the sum larger. Thus, our original sum is still less than or equal to the right side of the inequality.

### Mathematical insight
This theorem establishes a bound on oscillating sums involving the second Chebyshev function $\psi(n)$, which is important in number theory, especially in prime number theory. The result relates these sums to logarithms of factorials, which is a key step in analytical number theory approaches.

This bound is particularly useful in the context of Bertrand's postulate, which states that for any positive integer $n$, there always exists a prime number $p$ such that $n < p < 2n$. The theorem helps establish bounds on the distribution of prime numbers in specific intervals.

The alternating behavior in the sum (through the $(-1)^{d+1}$ term) captures the oscillating nature of the prime distribution, while the even constraint on $k$ ensures specific convergence properties of the sum.

### Dependencies
- `FACT_EXPAND_PSI`: Establishes that $\ln(n!) - 2\ln\left(\left\lfloor\frac{n}{2}\right\rfloor!\right) = \sum_{d=1}^{n} (-1)^{d+1} \cdot \psi\left(\left\lfloor\frac{n}{d}\right\rfloor\right)$
- `PSI_EXPANSION_CUTOFF`: Provides inequalities for truncated alternating sums of $\psi$ values
- `PSI_LIST`: Contains basic values of the $\psi$ function, specifically $\psi(0) = \ln(1) = 0$
- `LN_1`: States that $\ln(1) = 0$
- `PSI_POS`: Establishes that $\psi(n) \geq 0$ for all natural numbers $n$
- `SUM_MORETERMS_EQ`: Handles equality of sums with zero terms
- `sum`: Basic properties of finite sums
- `REAL_LE_TRANS`: Transitivity of the less-than-or-equal relation on real numbers
- `REAL_LE_REFL`: Reflexivity of the less-than-or-equal relation on real numbers

### Porting notes
When porting this theorem:
1. Ensure that your proof assistant has a well-defined definition of the von Mangoldt function $\Lambda$ and the second Chebyshev function $\psi$.
2. The handling of integer division (DIV) and floor functions might differ between systems - make sure these operations are properly defined and behave consistently.
3. The alternating sign in sums (via the power of -1) might require careful handling in systems with different approaches to such expressions.
4. Pay special attention to the handling of even/odd numbers and the division properties used in the proof.

---

## FACT_PSI_BOUND_2_3

### FACT_PSI_BOUND_2_3
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_2_3 = prove
 (`!n. psi(n) - psi(n DIV 2)
       <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) /\
       ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
       <= psi(n) - psi(n DIV 2) + psi(n DIV 3)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `2`] FACT_PSI_BOUND_EVEN) THEN
  MP_TAC(SPECL [`n:num`; `3`] FACT_PSI_BOUND_ODD) THEN
  REWRITE_TAC[ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ARITH; REAL_ADD_LID; DIV_1] THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_ONE; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the following inequalities hold:
$$\psi(n) - \psi(n \div 2) \leq \ln(n!) - 2\ln((n \div 2)!) \leq \psi(n) - \psi(n \div 2) + \psi(n \div 3)$$

where:
- $\psi(n)$ is the second Chebyshev function, defined as the sum of the von Mangoldt function $\Lambda(d)$ for $1 \leq d \leq n$
- $n \div 2$ represents integer division of $n$ by $2$
- $\ln$ is the natural logarithm function

### Informal proof
The proof establishes both the lower and upper bounds through the following steps:

* For the lower bound:
  - We apply theorem `FACT_PSI_BOUND_EVEN` with parameters $n$ and $k=2$ (which is even)
  - This gives us: $\sum_{d=1}^{2} (-1)^{d+1} \cdot \psi(n \div d) \leq \ln(n!) - 2\ln((n \div 2)!)$

* For the upper bound:
  - We apply theorem `FACT_PSI_BOUND_ODD` with parameters $n$ and $k=3$ (which is odd)
  - This gives us: $\ln(n!) - 2\ln((n \div 2)!) \leq \sum_{d=1}^{3} (-1)^{d+1} \cdot \psi(n \div d)$

* We then expand the sums using `REAL_SUM_CONV` to obtain:
  - For $k=2$: $\psi(n) - \psi(n \div 2) \leq \ln(n!) - 2\ln((n \div 2)!)$
  - For $k=3$: $\ln(n!) - 2\ln((n \div 2)!) \leq \psi(n) - \psi(n \div 2) + \psi(n \div 3)$

* The proof concludes with routine arithmetic manipulation to establish the desired inequalities.

### Mathematical insight
This theorem establishes tight bounds for the difference between the natural logarithm of the factorial $n!$ and twice the natural logarithm of $(n \div 2)!$. The bounds are expressed in terms of the second Chebyshev function $\psi$, which counts prime powers with logarithmic weights.

This is a key step in the formal proof of Bertrand's postulate (which states that for every $n > 1$, there is always a prime $p$ such that $n < p < 2n$). The bounds established here help control the growth of factorials in terms of the Chebyshev function, which is directly related to the distribution of prime numbers.

The relationship between factorial growth and the Chebyshev function is crucial in analytic number theory, particularly in studying the asymptotic distribution of prime numbers.

### Dependencies
- Theorems:
  - `FACT_PSI_BOUND_ODD`: Relates the logarithm of factorials to the sum of weighted $\psi$ values for odd values of $k$
  - `FACT_PSI_BOUND_EVEN`: Relates the logarithm of factorials to the sum of weighted $\psi$ values for even values of $k$
  - `REAL_SUM_CONV`: Conversion for expanding finite sums to their explicit form

- Definitions:
  - `psi`: The second Chebyshev function, defined as the sum of von Mangoldt function values
  - `ln`: The natural logarithm function

### Porting notes
When porting this theorem:
- Ensure that the number theory library in the target system has the necessary machinery for the Chebyshev function and von Mangoldt function
- The proof relies heavily on the alternating sum structure of the Chebyshev function expansions, so make sure these patterns are preserved
- The integer division operation (`DIV` in HOL Light) should be properly implemented in the target system, particularly its behavior with natural numbers

---

## PSI_DOUBLE_LEMMA

### PSI_DOUBLE_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSI_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> &n / &6 <= psi(n) - psi(n DIV 2)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:num` FACT_PSI_BOUND_2_3) THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + p3 <= a ==> u <= v /\ a <= p - p2 + p3 ==> b <= p - p2`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n / &6 + &n / &2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN MP_TAC(SPEC `n DIV 3` PSI_UBOUND_3_2) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &n / &3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `3`] DIVISION) THEN ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` LN_FACT_DIFF_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `ltm <= nl2 - a ==> abs(lf - nl2) <= ltm ==> a <= lf`) THEN
  ASM_SIMP_TAC[ARITH_RULE `n >= 1200 ==> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n * &1 / &38` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_LE_SUB_LADD] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `n >= b ==> b <= n:num`)) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `a <= n ==> a - &1 <= n - &1`)) THEN
  ABBREV_TAC `x = &n - &1` THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement

For all natural numbers $n$, if $n \geq 1200$, then $\frac{n}{6} \leq \psi(n) - \psi(n \text{ DIV } 2)$.

Here, $\psi(n)$ is the second Chebyshev function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$ where $\Lambda(d)$ is the von Mangoldt function.

### Informal proof

The proof establishes a lower bound for the difference $\psi(n) - \psi(n \text{ DIV } 2)$ by using various bounds and inequalities. The main steps are:

- Start with the theorem `FACT_PSI_BOUND_2_3`, which relates the difference $\psi(n) - \psi(n \text{ DIV } 2)$ to the expression $\ln(n!) - 2\ln((n \text{ DIV } 2)!)$.

- From this, we establish:
  $$\psi(n) - \psi(n \text{ DIV } 2) \geq \ln(n!) - 2\ln((n \text{ DIV } 2)!) - \psi(n \text{ DIV } 3)$$

- Use `PSI_UBOUND_3_2` to bound $\psi(n \text{ DIV } 3) \leq \frac{3}{2} \cdot \frac{n}{3} = \frac{n}{2}$

- Then apply `LN_FACT_DIFF_BOUNDS` which bounds the absolute difference between $\ln(n!) - 2\ln((n \text{ DIV } 2)!)$ and $n\ln(2)$.

- We show that:
  $$\ln(n!) - 2\ln((n \text{ DIV } 2)!) \geq n\ln(2) - \text{error term}$$

- For $n \geq 1200$, we can ensure the error term is suitably small, giving:
  $$\ln(n!) - 2\ln((n \text{ DIV } 2)!) \geq \frac{n}{6} + \frac{n}{2}$$

- Combining these bounds, we get:
  $$\psi(n) - \psi(n \text{ DIV } 2) \geq \frac{n}{6} + \frac{n}{2} - \psi(n \text{ DIV } 3) \geq \frac{n}{6} + \frac{n}{2} - \frac{n}{2} = \frac{n}{6}$$

- The proof makes extensive use of calculus and real analysis to handle the asymptotic behavior, including differential calculus via the `OVERPOWER_LEMMA` to establish monotonicity of certain functions.

### Mathematical insight

This lemma provides a crucial lower bound for the difference $\psi(n) - \psi(n \text{ DIV } 2)$, which is an important quantity in number theory. The result shows that this difference grows linearly with $n$ (at least at rate $n/6$), which is significant for understanding the distribution of prime numbers.

This result is particularly useful in the context of Bertrand's postulate or related results about prime gaps. The Chebyshev function $\psi(n)$ counts primes with logarithmic weights, and understanding the growth rate of differences like $\psi(n) - \psi(n/2)$ helps establish bounds on prime gaps.

The bound $n/6$ is not tight but sufficient for applications in the surrounding formalization. The constant 1200 is a concrete threshold beyond which the asymptotic behavior becomes guaranteed.

### Dependencies
- Theorems:
  - `REAL_MUL_RID`: $\forall x. x \cdot 1 = x$
  - `REAL_MUL_LZERO`: $\forall x. 0 \cdot x = 0$
  - `REAL_LE_REFL`: $\forall x. x \leq x$
  - `REAL_LE_TRANS`: $\forall x\,y\,z. x \leq y \land y \leq z \Rightarrow x \leq z$
  - `REAL_LE_LADD`: $\forall x\,y\,z. (x + y) \leq (x + z) \iff y \leq z$
  - `REAL_SUB_LE`: $\forall x\,y. 0 \leq (x - y) \iff y \leq x$
  - `REAL_SUB_LDISTRIB`: $\forall x\,y\,z. x \cdot (y - z) = (x \cdot y) - (x \cdot z)$
  - `REAL_POS`: $\forall n. 0 \leq n$ (for natural numbers)
  - `REAL_LE_SUB_LADD`: $\forall x\,y\,z. x \leq (y - z) \iff (x + z) \leq y$
  - `LN_FACT_DIFF_BOUNDS`: Bounds for $|\ln(n!) - 2\ln((n \text{ DIV } 2)!) - n\ln(2)|$
  - `PSI_UBOUND_3_2`: $\forall n. \psi(n) \leq \frac{3}{2} \cdot n$
  - `FACT_PSI_BOUND_2_3`: Relates $\psi(n) - \psi(n \text{ DIV } 2)$ to $\ln(n!) - 2\ln((n \text{ DIV } 2)!)$
  - `OVERPOWER_LEMMA`: A lemma about maintaining inequalities through differentiation

- Definitions:
  - `psi`: The second Chebyshev function, defined as $\psi(n) = \sum_{d=1}^{n} \Lambda(d)$

### Porting notes
- This proof relies heavily on numerical calculations and concrete bounds, which might need to be adjusted depending on how precise the arithmetic tactics are in the target system.
- The threshold value 1200 is determined through numerical computation and would need verification in another system.
- The proof makes use of differentiation and advanced real analysis, so the target system would need good support for calculus.
- Managing the interplay between discrete properties (DIV operation) and continuous functions (logarithms) may require careful handling in other systems.

---

## THETA_DOUBLE_LEMMA

### THETA_DOUBLE_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let THETA_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> theta(n DIV 2) < theta(n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2 (SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(CONJUNCT1 (SPEC `n DIV 2` PSI_THETA)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PSI_DOUBLE_LEMMA) THEN
  MP_TAC(SPEC `ISQRT(n DIV 2)` PSI_POS) THEN
  SUBGOAL_THEN
   `&2 * psi (ISQRT n) < &n / &6`
   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
  REWRITE_TAC[PSI_UBOUND_3_2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
  SUBGOAL_THEN `(ISQRT n * 18) EXP (SUC 1) < n EXP (SUC 1)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXP_MONO_LT; NOT_SUC]] THEN
  REWRITE_TAC[EXP; EXP_1] THEN
  MATCH_MP_TAC(ARITH_RULE `324 * i * i < a ==> (i * 18) * (i * 18) < a`) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `324 * n` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS; LE_MULT_LCANCEL];
    REWRITE_TAC[LT_MULT_RCANCEL] THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;
```

### Informal statement
This theorem states that for any natural number $n \geq 1200$, we have:

$$\theta(n \div 2) < \theta(n)$$

where $\theta(n)$ is defined as the sum $\sum_{1 \leq p \leq n} \ln(p)$ over all prime numbers $p$, and $n \div 2$ denotes integer division of $n$ by $2$.

### Informal proof
The proof demonstrates that $\theta(n \div 2) < \theta(n)$ for $n \geq 1200$ by relating $\theta$ to the function $\psi$. The main steps are:

1. We use the relationship between $\theta$ and $\psi$ given by `PSI_THETA`:
   - $\theta(n \div 2) + \psi(\text{ISQRT}(n \div 2)) \leq \psi(n \div 2)$
   - $\psi(n) \leq \theta(n) + 2\psi(\text{ISQRT}(n))$

2. From `PSI_DOUBLE_LEMMA`, for $n \geq 1200$:
   - $\frac{n}{6} \leq \psi(n) - \psi(n \div 2)$

3. We show that $2\psi(\text{ISQRT}(n)) < \frac{n}{6}$ by:
   - Using `PSI_UBOUND_3_2`: $\psi(\text{ISQRT}(n)) \leq \frac{3}{2}\text{ISQRT}(n)$
   - Proving that $\frac{3}{2}\text{ISQRT}(n) \cdot \frac{12}{1} < \frac{n}{1}$
   - This is equivalent to showing that $18\text{ISQRT}(n) < n$
   - We prove this by showing that $(18\text{ISQRT}(n))^2 < n^2$
   - Using `ISQRT_WORKS`: $\text{ISQRT}(n)^2 \leq n < (\text{ISQRT}(n)+1)^2$
   - For $n \geq 1200$, we have $324 \cdot \text{ISQRT}(n)^2 < 324n < n^2$

4. Combining these inequalities:
   - $\theta(n \div 2) \leq \psi(n \div 2) - \psi(\text{ISQRT}(n \div 2))$
   - $\theta(n) \geq \psi(n) - 2\psi(\text{ISQRT}(n))$
   - $\psi(n) - \psi(n \div 2) \geq \frac{n}{6}$
   - $2\psi(\text{ISQRT}(n)) < \frac{n}{6}$
   - $\psi(\text{ISQRT}(n \div 2)) \geq 0$ by `PSI_POS`

5. Therefore, $\theta(n \div 2) < \theta(n)$.

### Mathematical insight
This theorem establishes an important monotonicity property for the prime-counting function $\theta(n)$. It shows that $\theta(n)$ is strictly increasing when $n$ is doubled, for sufficiently large $n$ (specifically, $n \geq 1200$).

The result connects to the distribution of prime numbers by showing that the sum of logarithms of primes in the range from $n/2$ to $n$ is always positive for large enough $n$. This is a key step in establishing results about prime gaps and the density of primes, including Bertrand's postulate (that there is always a prime between $n$ and $2n$ for $n > 1$).

The bound $n \geq 1200$ is a concrete, explicit threshold that makes the result effective rather than merely existential.

### Dependencies
- Theorems:
  - `PSI_THETA`: Relates $\theta(n)$ and $\psi(n)$ via inequalities
  - `PSI_DOUBLE_LEMMA`: Provides a lower bound for $\psi(n) - \psi(n \div 2)$
  - `PSI_POS`: Shows that $\psi(n) \geq 0$
  - `PSI_UBOUND_3_2`: Upper bound for $\psi(n)$
  - `ISQRT_WORKS`: Properties of integer square root function

- Definitions:
  - `theta`: Sum of logarithms of prime numbers up to $n$
  - `psi`: Chebyshev's second function (sum of von Mangoldt function values)
  - `ISQRT`: Integer square root function

### Porting notes
- The proof relies heavily on arithmetic manipulation and comparison of explicit bounds.
- When porting this theorem, pay attention to how the integer division operation `DIV` is defined in the target system, as its behavior for negative numbers might differ.
- The theorem uses `ISQRT` which selects the integer square root using Hilbert's epsilon operator. In other systems, you may need to explicitly define this function constructively.

---

## BIG_BERTRAND

### Name of formal statement
BIG_BERTRAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIG_BERTRAND = prove
 (`!n. n >= 2400 ==> ?p. prime(p) /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `2 * n` THETA_DOUBLE_LEMMA) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sum(n + 1,n) (\p. if prime p then ln (&p) else &0) = &0`
  MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(n + 1,n) (\r. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE
     `n + 1 <= r /\ r < n + n + 1 ==> n <= r /\ r <= 2 * n`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b + a = c) ==> (a = &0) ==> ~(b < c)`) THEN
  REWRITE_TAC[theta] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[SUM_SPLIT] THEN
  REWRITE_TAC[MULT_2]);;
```

### Informal statement
For all natural numbers $n \geq 2400$, there exists a prime number $p$ such that $n \leq p \leq 2n$.

This is a statement of Bertrand's postulate for sufficiently large numbers, which asserts that between any number and its double, there always exists at least one prime number.

### Informal proof

The proof uses reductio ad absurdum and relies on properties of the Chebyshev theta function.

* We start by assuming $n \geq 2400$.
* Apply THETA_DOUBLE_LEMMA to $2n$, which states that for $n \geq 1200$: $\theta(n) < \theta(2n)$.
  * This application is valid since $2n \geq 4800 > 1200$.
  * We simplify $2n \text{ DIV } 2 = n$ in the lemma.
  
* We use contradiction by assuming there is no prime $p$ such that $n \leq p \leq 2n$.
  * Under this assumption, for any $r$ where $n+1 \leq r < 2n+1$, if we evaluate $f(r) = \ln(r)$ when $r$ is prime and $0$ otherwise, we get $f(r) = 0$.
  * Therefore, $\sum_{r=n+1}^{2n} f(r) = \sum_{r=n+1}^{2n} 0 = 0$

* Using the definition of the Chebyshev theta function:
  $\theta(n) = \sum_{p=1}^{n} \ln(p)$ where $p$ ranges over primes only

* We can rewrite $\theta(2n) = \theta(n) + \sum_{r=n+1}^{2n} f(r)$
  * By our assumption, $\sum_{r=n+1}^{2n} f(r) = 0$
  * Therefore, $\theta(2n) = \theta(n)$

* But this contradicts the lemma that $\theta(n) < \theta(2n)$

Therefore, there must exist a prime $p$ such that $n \leq p \leq 2n$.

### Mathematical insight
This theorem proves Bertrand's postulate for sufficiently large values ($n \geq 2400$). Bertrand's postulate states that for any integer $n > 1$, there always exists at least one prime number $p$ such that $n < p < 2n$.

The proof leverages the Chebyshev theta function $\theta(n)$, which sums the logarithms of all primes up to $n$. The crucial insight is that if there were no primes between $n$ and $2n$, then $\theta(2n) = \theta(n)$, but this contradicts the established lemma that $\theta(n) < \theta(2n)$ for large enough $n$.

The theorem provides a concrete bound ($n \geq 2400$) for which Bertrand's postulate holds, though it's known to be true for all $n > 1$. The complete proof for all values requires more refined estimates.

### Dependencies
- **Theorems**:
  - `sum`: Defines the summation function with base case and inductive step
  - `SUM_EQ`: If two functions are equal on the summation range, their sums are equal
  - `SUM_0`: The sum of the zero function is zero
  - `SUM_SPLIT`: Splitting a sum at an intermediate point
  - `THETA_DOUBLE_LEMMA`: Key lemma showing that $\theta(n \text{ DIV } 2) < \theta(n)$ for $n \geq 1200$

- **Definitions**:
  - `ln`: The natural logarithm function
  - `theta`: The Chebyshev theta function, defined as the sum of logarithms of primes up to n

### Porting notes
When implementing this theorem in other proof assistants:
1. The use of the Chebyshev theta function is central to the proof, so this definition needs to be ported precisely
2. The exact value 2400 as the lower bound matters for the proof, as it relies on THETA_DOUBLE_LEMMA which has its own threshold of 1200
3. The proof uses some arithmetic simplifications (like DIV_MULT) that might need explicit handling in other systems
4. The contrapositive argument might require explicit steps in systems with different automation capabilities

---

## LANDAU_TRICK

### LANDAU_TRICK
- LANDAU_TRICK

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LANDAU_TRICK = prove
 (`!n. 0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n`,
  let lemma = TAUT
   `(p /\ b1 ==> a1) /\ (~b1 ==> a2) ==> p ==> b1 /\ a1 \/ a2` in
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> c \/ ~b`] THEN
  REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  REPEAT(MATCH_MP_TAC lemma THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  ARITH_TAC);;
```

### Informal statement
For any integer $n$ such that $0 < n < 2400$, at least one of the following pairs of inequalities holds:
- $n \leq 2$ and $2 \leq 2n$
- $n \leq 3$ and $3 \leq 2n$
- $n \leq 5$ and $5 \leq 2n$
- $n \leq 7$ and $7 \leq 2n$
- $n \leq 13$ and $13 \leq 2n$
- $n \leq 23$ and $23 \leq 2n$
- $n \leq 43$ and $43 \leq 2n$
- $n \leq 83$ and $83 \leq 2n$
- $n \leq 163$ and $163 \leq 2n$
- $n \leq 317$ and $317 \leq 2n$
- $n \leq 631$ and $631 \leq 2n$
- $n \leq 1259$ and $1259 \leq 2n$
- $n \leq 2503$ and $2503 \leq 2n$

### Informal proof
The proof employs a tautology-based approach with case analysis:

* First, we establish a key lemma: 
  $(p \wedge b_1 \Rightarrow a_1) \wedge (\neg b_1 \Rightarrow a_2) \Rightarrow (p \Rightarrow b_1 \wedge a_1 \vee a_2)$

* Then we apply a logical rewriting:
  $a \wedge b \Rightarrow c$ equivalently becomes $a \Rightarrow c \vee \neg b$

* We repeatedly apply the lemma in a case analysis manner, generating the respective claims.

* For each boundary value (2, 3, 5, etc.), we evaluate the corresponding inequalities by arithmetic reasoning.

* The proof ultimately verifies that for any $n$ in the specified range, at least one of the listed pairs of inequalities must hold.

### Mathematical insight
This theorem establishes a finite case analysis for integers in the range $(0, 2400)$. It's known as "Landau's trick" and serves to break down a numerical range into cases where specific inequalities hold. These particular boundary values (2, 3, 5, 7, 13, etc.) form an increasing sequence where each value has specific properties relevant to the context where this result is applied.

The comment notes that while this could be proved directly with the arithmetic decision procedure (`ARITH_RULE`), such an approach would be computationally expensive (taking "about 3 minutes"). The implemented proof is more efficient, using case analysis with the given thresholds.

This type of case analysis is a common technique in number theory and computational proofs where boundaries need to be established for different behaviors of functions or properties.

### Dependencies
- Tactics: 
  - `GEN_TAC`
  - `ONCE_REWRITE_TAC`
  - `REWRITE_TAC`
  - `MATCH_MP_TAC`
  - `CONJ_TAC`
  - `ARITH_TAC`
- Functions:
  - `TAUT`
  - `GSYM`
  - `DISJ_ASSOC`

### Porting notes
When porting this theorem to other systems:
1. The proof structure relies on HOL Light's tactical proof style. In other systems, you might need to use different approaches for case analysis.
2. The specific arithmetic reasoning might need different tactics in other systems.
3. The sequence of boundary values (2, 3, 5, 7, 13, etc.) appears to follow a pattern - each approximately doubles. This might be relevant to understand why these specific values were chosen.
4. The comment indicates this is a performance optimization. In other systems, you might be able to use more direct arithmetic decision procedures if they are efficient enough.

---

## BERTRAND

### BERTRAND
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let BERTRAND = prove
 (`!n. ~(n = 0) ==> ?p. prime p /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `n >= 2400 \/ n < 2400`) THEN
  ASM_SIMP_TAC[BIG_BERTRAND] THEN MP_TAC(SPEC `n:num` LANDAU_TRICK) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC(map (PRIME_CONV o curry mk_comb `prime` o mk_small_numeral)
                    [2;3;5;7;13;23;43;83;163;317;631;1259;2503]));;
```

### Informal statement
For all natural numbers $n$ where $n \neq 0$, there exists a prime number $p$ such that $n \leq p \leq 2n$.

This is Bertrand's postulate (also known as Bertrand-Chebyshev theorem), which states that for any $n > 0$, there is always at least one prime number in the interval $[n, 2n]$.

### Informal proof
The proof proceeds by case analysis:

* First, we split into two cases: $n \geq 2400$ or $n < 2400$.

* For the case $n \geq 2400$, we apply the theorem `BIG_BERTRAND`, which directly proves Bertrand's postulate for $n \geq 2400$.

* For the case $n < 2400$, we apply the `LANDAU_TRICK` theorem to $n$. This theorem states that for $0 < n < 2400$, at least one of the following holds:
  - $n \leq 2$ and $2 \leq 2n$
  - $n \leq 3$ and $3 \leq 2n$
  - $n \leq 5$ and $5 \leq 2n$
  - ...and so on for primes $7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503$

* We then verify that each of these numbers (2, 3, 5, 7, 13, etc.) is prime using `PRIME_CONV`.

* Therefore, in each case, we have found a prime $p$ such that $n \leq p \leq 2n$, completing the proof.

### Mathematical insight
Bertrand's postulate is a fundamental result in number theory that guarantees the existence of a prime in every interval $[n, 2n]$ for $n > 0$. While now considered a relatively "weak" result (as we now know there are many more primes in such intervals), it was historically significant.

The proof uses a clever technique sometimes called the "Landau trick," where we directly verify the theorem for small values of $n$, and prove it theoretically for large values. This approach is common in number theory, where asymptotic methods work well for large numbers, but small cases might need direct verification.

The HOL Light proof combines:
1. A direct proof for large values ($n \geq 2400$)
2. Explicit verification using a carefully chosen set of primes for smaller values

This is a typical example of how many number-theoretic results are formalized, combining theoretical arguments with computational verification.

### Dependencies
- `BIG_BERTRAND`: Proves Bertrand's postulate for $n \geq 2400$
- `LANDAU_TRICK`: Provides a disjunction of cases covering all $n < 2400$
- `PRIME_CONV`: Used to verify that specific numbers are prime

### Porting notes
When porting this theorem:
1. You'll need a mechanism similar to `PRIME_CONV` that can computationally verify primality of specific numbers
2. The large-number case and small-number case may need different approaches in other systems
3. The specific number 2400 is the cutoff for the analytical proof - this is determined by the specific constants in the theta function estimates used in the original proof

---

## pii

### Name of formal statement
pii

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pii = new_definition
  `pii(n) = sum(1,n) (\p. if prime(p) then &1 else &0)`;;
```

### Informal statement
The function $\pi(n)$ is defined as the sum over integers $p$ from $1$ to $n$ such that
$$\pi(n) = \sum_{p=1}^{n} \begin{cases} 1 & \text{if } p \text{ is prime} \\ 0 & \text{otherwise} \end{cases}$$

This is the standard prime counting function, which gives the number of prime numbers less than or equal to $n$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The prime counting function $\pi(n)$ is a fundamental object in number theory. It counts the number of prime numbers less than or equal to a given integer $n$. The behavior of this function is described by the Prime Number Theorem, which states that $\pi(n)$ is asymptotically equal to $\frac{n}{\ln(n)}$. 

In the formalization, the definition uses the characteristic function approach, summing $1$ for each prime number in the range and $0$ for composite numbers, which provides a clean way to count primes.

This definition serves as a foundation for proving many important results in analytic number theory, including Bertrand's postulate (which states that for every $n > 1$, there is always at least one prime $p$ such that $n < p < 2n$) and eventually the Prime Number Theorem itself.

### Dependencies
- Theorems:
  - `sum`: Recursive definition of the summation operation
- Definitions:
  - `prime`: (implicit) Primality predicate used in the definition

### Porting notes
When porting this definition to other proof assistants, consider:
- The representation of natural numbers and integers (HOL Light uses `&1` to represent the integer 1)
- How summation is defined in the target system
- Whether the primality predicate is already available
- How conditional expressions are handled

Most theorem provers have built-in notions of primality and summation, so this definition should translate relatively straightforwardly.

---

## PII_LIST

### PII_LIST

### Type of the formal statement
- Implementation/Function definition

### Formal Content
```ocaml
let PII_LIST =
  let PII_0 = prove
   (`pii(0) = &0`,
    REWRITE_TAC[pii; sum])
  and PII_SUC = prove
   (`pii(SUC n) = pii(n) + (if prime(SUC n) then &1 else &0)`,
    REWRITE_TAC[pii; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [COND_CLAUSES] THENC
    REAL_RAT_REDUCE_CONV in
  let rec PII_LIST n =
    if n = 0 then [PII_0] else
    let ths = PII_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PII_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  PII_LIST;;
```

### Informal statement
`PII_LIST` is a function that, given a natural number N, returns a list of theorems stating the values of the prime-counting function π(n) for all n from 0 to N. Specifically, it produces a list of theorems of the form:
- `pii(0) = 0`
- `pii(1) = 0` 
- `pii(2) = 1`
- `pii(3) = 2`
- etc., up to `pii(N)`

The list is ordered in reverse, with `pii(N)` at the head and `pii(0)` at the tail.

### Informal proof
This is an implementation consisting of a function that builds a list of theorems rather than a mathematical theorem with a proof. The implementation:

1. Defines two core theorems:
   - `PII_0`: Establishes that `pii(0) = 0`
   - `PII_SUC`: Provides the recurrence relation: `pii(SUC n) = pii(n) + (if prime(SUC n) then 1 else 0)`

2. Sets up a conversion pipeline (`SIMPER_CONV`) that:
   - Reduces numeric expressions
   - Evaluates primality for specific numbers
   - Simplifies conditional expressions
   - Reduces rational expressions

3. Implements a recursive function `PII_LIST` that:
   - Returns `[PII_0]` (base case) when n = 0
   - For n > 0:
     - Recursively computes the list for n-1
     - Instantiates the successor theorem with n-1
     - Rewrites using the previously computed value of `pii(n-1)`
     - Simplifies the resulting theorem
     - Adds this theorem to the head of the list

The implementation efficiently builds theorems for all values of `pii` up to n by reusing previously computed results.

### Mathematical insight
This function serves as an optimized computational tool for calculating values of the prime-counting function π(n) within HOL Light. The prime-counting function π(n) counts the number of primes less than or equal to n.

The implementation uses a recurrence relation approach which is more efficient than recomputing each value from scratch. Each new value π(n+1) is derived from π(n) by simply checking if n+1 is prime or not.

This function is particularly useful for formalizations and proofs involving distributions of prime numbers, such as Bertrand's postulate or the Prime Number Theorem, where having concrete values of π(n) for specific ranges is necessary.

### Dependencies
- Theorems:
  - `sum`: Defines properties of summation
  - `PII_0`: States that `pii(0) = 0`
  - `PII_SUC`: Provides the recurrence relation for `pii`
- Definitions:
  - `pii`: Prime counting function defined as `pii(n) = sum(1,n) (λp. if prime(p) then 1 else 0)`

### Porting notes
When porting this to another system:
1. Ensure the prime-counting function `pii` is already defined
2. The implementation requires primality testing functionality (equivalent to `PRIME_CONV`)
3. The function relies on rewriting and conversion techniques that may have different implementations in other systems
4. Consider implementing this as a computable function that returns the actual values rather than theorems if the target system has better computational capabilities

---

## PRIMES_FINITE

### PRIMES_FINITE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PRIMES_FINITE = prove
 (`!n. FINITE {p | p <= n /\ prime(p)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p | p < SUC n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC);;
```

### Informal statement
The theorem states that for any natural number $n$, the set of all prime numbers less than or equal to $n$ is finite.

Formally: $\forall n. \text{FINITE} \{p \mid p \leq n \land \text{prime}(p)\}$

### Informal proof
The proof uses the fact that any subset of a finite set is finite.

1. For any natural number $n$, we want to show that $\{p \mid p \leq n \land \text{prime}(p)\}$ is finite.
2. We know that $\{p \mid p < \text{SUC}(n)\}$ (i.e., the set of all numbers less than $n+1$) is finite.
3. Note that $\{p \mid p \leq n \land \text{prime}(p)\} \subseteq \{p \mid p < \text{SUC}(n)\}$ because:
   - If $p \leq n$ and $p$ is prime, then $p < \text{SUC}(n)$ (which means $p < n+1$).
4. Since any subset of a finite set is finite, we conclude that $\{p \mid p \leq n \land \text{prime}(p)\}$ is finite.

### Mathematical insight
This theorem establishes the fundamental fact that there are only finitely many prime numbers up to any given bound $n$. This is a basic result in number theory and is used in many contexts, such as:

- Analyzing the distribution of prime numbers
- Proving properties about prime factorizations
- Serving as a foundation for more advanced results about prime numbers

The result is intuitive (since we're bounding the primes by a finite value), but its formal verification is an important building block for developing number theory in a formal system.

### Dependencies
- Theorems:
  - `FINITE_SUBSET`: If a set is a subset of a finite set, then it is also finite
  - `FINITE_NUMSEG_LT`: The set of numbers less than a given number is finite
  - `SUBSET`: Definition of subset relation
  - `IN_ELIM_THM`: Theorem about set membership

### Porting notes
When porting this theorem:
1. Ensure that the definition of primality (`prime`) is consistent with the target system
2. Ensure that theorem names like `FINITE_SUBSET` have corresponding theorems in the target system
3. The proof uses arithmetic reasoning (`ARITH_TAC`), so appropriate arithmetic automation should be applied in the target system

---

## PII

### PII
- `PII`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let PII = prove
 (`!n. pii(n) = &(CARD {p | p <= n /\ prime(p)})`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{p | p <= 0 /\ prime p} = {}`
     (fun th -> REWRITE_TAC(th::CARD_CLAUSES::PII_LIST 0)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[LE; PRIME_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | p <= SUC n /\ prime p} =
                if prime(SUC n) then (SUC n) INSERT {p | p <= n /\ prime p}
                else {p | p <= n /\ prime p}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LE];
    ALL_TAC] THEN
  REWRITE_TAC[pii; sum] THEN REWRITE_TAC[GSYM pii] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SIMP_TAC[CARD_CLAUSES; PRIMES_FINITE] THEN COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_MESON_TAC[ARITH_RULE `~(SUC n <= n)`];
    REWRITE_TAC[REAL_OF_NUM_SUC]]);;
```

### Informal statement
The theorem states that for all natural numbers $n$:
$$\pi(n) = |\{p \mid p \leq n \wedge \text{prime}(p)\}|$$

where:
- $\pi(n)$ (denoted as `pii(n)` in HOL Light) is the prime counting function, giving the number of primes less than or equal to $n$
- $|\{p \mid p \leq n \wedge \text{prime}(p)\}|$ (represented as `CARD {p | p <= n /\ prime(p)}` in HOL Light) is the cardinality of the set of prime numbers less than or equal to $n$.

### Informal proof
The proof proceeds by induction on $n$:

**Base case ($n = 0$):**
- We first show that $\{p \mid p \leq 0 \wedge \text{prime}(p)\} = \emptyset$ (the empty set)
  - This follows because:
    - No number $p$ can satisfy both $p \leq 0$ and $\text{prime}(p)$
    - Specifically, $0$ is not prime (by theorem `PRIME_0`)
  - Thus, $|\{p \mid p \leq 0 \wedge \text{prime}(p)\}| = |\emptyset| = 0$
- By the definition of $\pi(0)$ (from `PII_LIST`), we have $\pi(0) = 0$
- Therefore, $\pi(0) = |\{p \mid p \leq 0 \wedge \text{prime}(p)\}|$

**Inductive case ($n \to n+1$):**
- We need to show that $\pi(n+1) = |\{p \mid p \leq n+1 \wedge \text{prime}(p)\}|$
- We first establish that:
  $$\{p \mid p \leq n+1 \wedge \text{prime}(p)\} = \begin{cases}
  \{n+1\} \cup \{p \mid p \leq n \wedge \text{prime}(p)\} & \text{if } n+1 \text{ is prime} \\
  \{p \mid p \leq n \wedge \text{prime}(p)\} & \text{otherwise}
  \end{cases}$$
- From the definition of $\pi$ (through `pii` and `sum`), we get:
  $$\pi(n+1) = \pi(n) + \begin{cases}
  1 & \text{if } n+1 \text{ is prime} \\
  0 & \text{otherwise}
  \end{cases}$$
- By the induction hypothesis, we have $\pi(n) = |\{p \mid p \leq n \wedge \text{prime}(p)\}|$
- When $n+1$ is prime:
  $$|\{n+1\} \cup \{p \mid p \leq n \wedge \text{prime}(p)\}| = 1 + |\{p \mid p \leq n \wedge \text{prime}(p)\}|$$
  since $n+1 > n$ ensures $n+1$ is not in the set $\{p \mid p \leq n \wedge \text{prime}(p)\}$
- When $n+1$ is not prime:
  $$|\{p \mid p \leq n \wedge \text{prime}(p)\}| = |\{p \mid p \leq n \wedge \text{prime}(p)\}|$$
- Therefore, $\pi(n+1) = |\{p \mid p \leq n+1 \wedge \text{prime}(p)\}|$

### Mathematical insight
This theorem establishes the fundamental correspondence between the prime counting function $\pi(n)$ and the cardinality of the set of primes up to $n$. 

While the statement may seem obvious (as $\pi(n)$ is naturally defined as counting primes up to $n$), this theorem forms a bridge between:
1. The recursive definition of `pii(n)` using the `sum` function (which increments a counter for each prime)
2. The set-theoretic notion of counting primes using the cardinality of a set

This correspondence is important for number theory and in particular for theoretical results about the distribution of prime numbers. It allows us to shift between different perspectives when reasoning about the prime counting function.

### Dependencies
- Definitions:
  - `pii`: The prime counting function defined as a sum
- Theorems:
  - `PRIME_0`: States that 0 is not prime
  - `sum`: Gives recursive properties of the sum function
  - `PII_LIST`: List of theorems about specific values of the prime counting function
  - `PRIMES_FINITE`: States that the set of primes below any given bound is finite

### Porting notes
- The HOL Light `pii` function is defined differently from the typical mathematical definition, using a sum rather than direct counting. Ensure your target system's definition matches semantically.
- The proof heavily relies on the `CARD` operator for set cardinality, so check how your target system handles finite set cardinality.
- HOL Light's use of `&` for converting natural numbers to reals should be handled appropriately in the target system.

---

## PII_LBOUND

### Name of formal statement
PII_LBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_LBOUND = prove
 (`!n. 3 <= n ==> &1 / &2 * (&n / ln(&n)) <= pii(n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
               ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP
   (ARITH_RULE `3 <= n ==> (n = 3) \/ (n = 4) \/ 5 <= n`)) THEN
  ASM_REWRITE_TAC(PII_LIST 4) THENL
   [CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP THETA_LBOUND_1_2) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> a <= x ==> a <= y`) THEN
  REWRITE_TAC[theta; pii; GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL] THEN
  SUBGOAL_THEN `&0 < &r /\ &r <= &n`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 <= r` THEN UNDISCH_TAC `r < n + 1` THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$ such that $n \geq 3$, we have:
$$\frac{1}{2} \cdot \frac{n}{\ln(n)} \leq \pi(n)$$

where $\pi(n)$ counts the number of primes less than or equal to $n$.

### Informal proof
To prove this bound on the prime counting function $\pi(n)$, we proceed as follows:

* First, we rewrite the division expressions in terms of multiplication, which gives us the goal $\frac{1}{2} \cdot \frac{n}{\ln(n)} \leq \pi(n)$.

* We apply division properties to transform it to $\frac{1}{2} \cdot n \leq \pi(n) \cdot \ln(n)$, noting that $\ln(n) > 0$ when $n > 1$.

* For the cases $n = 3$ and $n = 4$, we handle them directly by computation:
  - For $n = 3$: $\pi(3) = 2$ (counting primes 2 and 3)
  - For $n = 4$: $\pi(4) = 2$ (counting primes 2 and 3)
  - In both cases, we verify the inequality using numerical computation.

* For $n \geq 5$, we use the previously established bound $\frac{1}{2} \cdot n \leq \theta(n)$ where $\theta(n) = \sum_{p \leq n, p \text{ prime}} \ln(p)$.

* We relate $\theta(n)$ to $\pi(n)$ by observing that $\theta(n) = \sum_{r=1}^n [\text{if $r$ is prime then $\ln(r)$ else 0}]$.

* Similarly, $\pi(n) = \sum_{r=1}^n [\text{if $r$ is prime then 1 else 0}]$.

* Using the relationship between these sums, we establish that $\theta(n) \leq \pi(n) \cdot \ln(n)$ by showing that for each prime $p \leq n$, we have $\ln(p) \leq \ln(n)$.

* This follows from the monotonicity of the logarithm function, since for any prime $p \leq n$, we have $\ln(p) \leq \ln(n)$.

* Combining these results gives us $\frac{1}{2} \cdot n \leq \theta(n) \leq \pi(n) \cdot \ln(n)$, which yields the desired inequality.

### Mathematical insight
This theorem establishes a lower bound for the prime counting function $\pi(n)$. The result $\pi(n) \geq \frac{n}{2\ln(n)}$ for $n \geq 3$ is a significant step in proving results about the distribution of primes.

The bound relates to the Prime Number Theorem, which states that $\pi(n) \sim \frac{n}{\ln(n)}$ as $n \to \infty$. This lower bound shows that $\pi(n)$ is at least half of this asymptotic estimate even for relatively small values of $n$.

The proof technique leverages the relationship between $\pi(n)$ and the Chebyshev function $\theta(n)$, which sums the logarithms of primes up to $n$. This connection is a fundamental tool in analytic number theory.

### Dependencies
- Definitions:
  - `ln`: Natural logarithm function
  - `theta`: Chebyshev's theta function, summing logarithms of primes up to n
  - `pii`: Prime counting function

- Theorems:
  - `REAL_MUL_RID`: Multiplication by 1 is identity
  - `REAL_MUL_RZERO`: Multiplication by 0 yields 0
  - `REAL_LE_REFL`: Reflexivity of the ≤ relation on reals
  - `REAL_LTE_TRANS`: Transitivity involving < and ≤ for reals
  - `SUM_LE`: Monotonicity of summation
  - `SUM_CMUL`: Distributivity of constant multiplication over summation
  - `LN_MONO_LE`: Monotonicity of logarithm function
  - `LN_POS_LT`: Positivity of logarithm for values > 1
  - `THETA_LBOUND_1_2`: Lower bound for theta function: $\frac{1}{2}n \leq \theta(n)$ for $n \geq 5$
  - `PII_LIST`: List of values of $\pi(n)$ for small $n$

### Porting notes
When implementing this in another system:
1. Make sure the logarithm function is defined and has appropriate monotonicity properties.
2. The prime counting function and Chebyshev theta function need proper definitions.
3. For small values of $n$ (3 and 4), explicit calculation is used, which might require specific tactics or computation abilities in the target system.
4. The handling of sums over conditional expressions might need special treatment depending on the system's support for such constructs.

---

## PII_UBOUND_CASES_50

### Name of formal statement
PII_UBOUND_CASES_50

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_UBOUND_CASES_50 = prove
 (`!n. n < 50 ==> 3 <= n ==> ln(&n) * pii(n) <= &5 * &n`,
  let tac = CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV) in
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC(PII_LIST 49) THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC]) THEN tac);;
```

### Informal statement
For all natural numbers $n$ such that $n < 50$ and $3 \leq n$, we have:
$$\ln(n) \cdot \pi(n) \leq 5n$$

where $\pi(n)$ is the prime counting function (the number of primes less than or equal to $n$).

### Informal proof
This theorem is proven by a case-by-case analysis of all natural numbers $n$ satisfying $3 \leq n < 50$. The proof follows these steps:

- First, we expand the cases for all $n$ in the range $[3,49]$.
- We compute the value of the prime-counting function $\pi(n)$ for each value of $n$ up to 49 using `PII_LIST 49`.
- For each case, we divide both sides by $n$ to get an equivalent inequality: $\ln(n) \cdot \pi(n) / n \leq 5$.
- Then for each specific value of $n$ in the range, we:
  - Compute $\ln(n)$ using the `LN_N2_CONV` conversion which expresses the logarithm in a form suitable for numeric calculation.
  - Use `REALCALC_REL_CONV` to numerically verify the resulting inequality.

The proof is essentially an exhaustive verification that for each value of $n$ from 3 to 49, the inequality $\ln(n) \cdot \pi(n) \leq 5n$ holds by direct numerical computation.

### Mathematical insight
This theorem establishes an upper bound for the product of the natural logarithm of $n$ and the prime counting function $\pi(n)$ for small values of $n$ (specifically, for $3 \leq n < 50$). 

This result is part of a larger effort related to Bertrand's Postulate or Chebyshev's Theorem, which states that for every $n > 1$, there is always a prime $p$ such that $n < p < 2n$. The bound $\ln(n) \cdot \pi(n) \leq 5n$ establishes a specific growth rate relationship between these functions for small values.

The Prime Number Theorem asymptotically gives $\pi(n) \sim n/\ln(n)$, which would make $\ln(n) \cdot \pi(n) \sim n$. This theorem shows that for small $n$, the product is bounded by $5n$, providing a concrete numerical bound rather than an asymptotic one.

### Dependencies
- **Definitions**:
  - `ln`: Natural logarithm defined as `ln x = @u. exp(u) = x`
  - `pii`: Prime counting function defined as `pii(n) = sum(1,n) (λp. if prime(p) then &1 else &0)`

- **Theorems**:
  - `LN_N2_CONV`: A conversion for exact computation of logarithms
  - `PII_LIST`: Precomputed values of the prime counting function

### Porting notes
When porting this theorem to other systems:
1. You'll need implementations of the prime counting function and natural logarithm.
2. The proof relies heavily on numerical calculations and case analysis, which might need different tactics in other systems.
3. The conversions like `LN_N2_CONV` and `REALCALC_REL_CONV` perform numerical calculations - you'll need equivalent tactics in the target system.
4. Consider using automation or numerical verification methods available in your target system rather than directly translating the HOL Light tactics.

---

## THETA_POS

### Name of formal statement
THETA_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_POS = prove
 (`!n. &0 <= theta n`,
  GEN_TAC THEN REWRITE_TAC[theta] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[LE_REFL; LN_POS; REAL_OF_NUM_LE]);;
```

### Informal statement
For all natural numbers $n$, the theta function is non-negative:
$$\forall n. 0 \leq \theta(n)$$

where $\theta(n) = \sum_{p=1}^n \begin{cases} \ln(p) & \text{if } p \text{ is prime} \\ 0 & \text{otherwise} \end{cases}$

### Informal proof
We need to prove that $\theta(n) \geq 0$ for all natural numbers $n$. 

By definition, $\theta(n) = \sum_{p=1}^n f(p)$ where $f(p) = \ln(p)$ if $p$ is prime and $f(p) = 0$ otherwise.

The proof follows from these observations:
- For any prime $p$, we know that $p \geq 2 > 1$, so $\ln(p) \geq 0$ by the theorem `LN_POS` which states that $1 \leq x \implies 0 \leq \ln(x)$.
- For non-prime numbers, $f(p) = 0 \geq 0$.

Thus, all terms in the summation are non-negative. By the theorem `SUM_POS_GEN`, which states that if all terms in a summation are non-negative, then the sum is also non-negative, we conclude that $\theta(n) \geq 0$.

### Mathematical insight
The theta function $\theta(n)$ is a fundamental function in number theory that sums the logarithms of all primes up to $n$. It's closely related to the prime counting function and is used extensively in the analysis of prime number distribution and in proofs of the Prime Number Theorem.

This theorem establishes the basic property that $\theta(n)$ is always non-negative, which is immediate from its definition since it's a sum of non-negative terms (logarithms of primes and zeros). While this result might seem trivial, establishing such basic properties is essential in formal mathematics.

### Dependencies
- **Definitions**:
  - `theta`: Definition of the theta function as the sum of logarithms of primes up to n
- **Theorems**:
  - `SUM_POS_GEN`: If all terms from m to n in a summation are non-negative, then the sum is non-negative
  - `LN_POS`: If $1 \leq x$ then $0 \leq \ln(x)$

### Porting notes
When porting this theorem:
- Ensure that your system has a proper definition of primality
- Verify that the logarithm function is defined for all positive reals and that the property $1 \leq x \implies 0 \leq \ln(x)$ is established
- Check that your summation operator behaves similarly to HOL Light's `sum` function

---

## PII_MONO

### Name of formal statement
PII_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_MONO = prove
 (`!m n. m <= n ==> pii(m) <= pii(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; pii] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all natural numbers $m$ and $n$, if $m \leq n$, then $\pi(m) \leq \pi(n)$.

Here, $\pi(n)$ denotes the prime-counting function, which counts the number of prime numbers less than or equal to $n$.

### Informal proof
The proof shows that the prime-counting function $\pi$ is monotonically increasing.

1. We first simplify using the lemma that if $m \leq n$, then $n = m + d$ for some $d$, converting the goal to prove that $\pi(m) \leq \pi(m+d)$.

2. Using the definition of $\pi(n)$ as a sum $\sum_{p=1}^{n} [p \text{ is prime}]$, where $[p \text{ is prime}]$ is $1$ if $p$ is prime and $0$ otherwise.

3. Applying `SUM_SPLIT`, we rewrite:
   $\pi(m+d) = \pi(m) + \sum_{p=m+1}^{m+d} [p \text{ is prime}]$

4. This gives us $\pi(m+d) = \pi(m) + \text{(sum of additional terms)}$, which directly implies $\pi(m) \leq \pi(m+d)$ by adding a non-negative term.

5. The non-negativity of the additional sum follows from `SUM_POS_GEN`, since each term in the sum is either $0$ or $1$ (non-negative).

### Mathematical insight
This theorem establishes the monotonicity of the prime-counting function $\pi(n)$, which is a fundamental property of this important function in number theory. The result is intuitive: as we consider larger integers, we can only encounter more primes, so the count cannot decrease.

The proof approach leverages the definition of $\pi(n)$ as a sum and uses standard properties of sums to decompose $\pi(n)$ into $\pi(m)$ plus additional terms, then showing these additional terms must be non-negative.

### Dependencies
- **Definitions**:
  - `pii`: Definition of the prime-counting function $\pi(n)$ as the sum of an indicator function for primes from 1 to n

- **Theorems**:
  - `SUM_POS_GEN`: A theorem stating that a sum of non-negative terms is non-negative
  - `SUM_SPLIT`: A theorem for splitting a sum at an intermediate point

---

## PII_POS

### Name of formal statement
PII_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_POS = prove
 (`!n. &0 <= pii(n)`,
  SUBGOAL_THEN `pii(0) = &0` (fun th -> MESON_TAC[th; PII_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PII_LIST 0));;
```

### Informal statement
For all natural numbers $n$, the prime counting function $\pi(n)$ is non-negative:
$$\forall n.\ 0 \leq \pi(n)$$

Here, $\pi(n)$ counts the number of prime numbers from 1 to $n$ inclusive.

### Informal proof
We prove that $\pi(n) \geq 0$ for all natural numbers $n$ by:

1. First establishing the base case: $\pi(0) = 0$
2. Then using monotonicity of $\pi$ to extend this result to all $n \geq 0$

Specifically:
- We set up a subgoal to prove that $\pi(0) = 0$
- This subgoal is solved directly using the definition of $\pi(0)$ from the `PII_LIST` theorem
- Then we apply the monotonicity theorem `PII_MONO` which states that if $m \leq n$ then $\pi(m) \leq \pi(n)$
- Since $0 \leq n$ for all natural numbers $n$, and $\pi(0) = 0$, we have $0 = \pi(0) \leq \pi(n)$ for all $n$
- Therefore $0 \leq \pi(n)$ for all natural numbers $n$

### Mathematical insight
This theorem establishes the basic property that the prime counting function is non-negative, which is evident from its definition as a counting function. While mathematically trivial, formally establishing this property is important in a theorem prover as it provides a foundation for more complex results involving the prime counting function.

The prime counting function $\pi(n)$ plays a central role in analytic number theory, particularly in the study of the distribution of prime numbers. This non-negativity property is a fundamental characteristic that enables the use of $\pi(n)$ in various inequalities and estimates.

### Dependencies
- **Theorems**:
  - `LN_1`: The natural logarithm of 1 is 0, i.e., $\ln(1) = 0$
  - `PII_LIST`: List of values of $\pi(n)$ for small values of $n$, starting with $\pi(0) = 0$
  - `PII_MONO`: Monotonicity of the prime counting function: $\forall m,n.\ m \leq n \Rightarrow \pi(m) \leq \pi(n)$

- **Definitions**:
  - `pii`: The prime counting function $\pi(n) = \sum_{p=1}^{n} [p \text{ is prime}]$, where $[p \text{ is prime}]$ is 1 if $p$ is prime and 0 otherwise

### Porting notes
When implementing this in another proof assistant:
- Ensure the prime counting function is defined first
- The proof is straightforward if you have the monotonicity property of $\pi$ and the base case $\pi(0) = 0$
- The reference to `LN_1` seems unnecessary for this proof and might be an artifact of the HOL Light implementation

---

## PII_CHANGE

### PII_CHANGE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PII_CHANGE = prove
 (`!m n. ~(m = 0) ==> ln(&m) * (pii n - pii m) <= &3 / &2 * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * (c - b) ==> a * (b - c) <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC PII_MONO THEN
    UNDISCH_TAC `~(m <= n:num)` THEN ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `theta n` THEN REWRITE_TAC[THETA_UBOUND_3_2] THEN
  MP_TAC(SPEC `m:num` THETA_POS) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= n - m ==> &0 <= m ==> a <= n`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[pii; theta; GSYM SUM_SPLIT; REAL_ADD_SUB] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL; REAL_MUL_RID] THEN
  SUBGOAL_THEN `&0 < &m /\ &m <= &r`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 + m <= r` THEN UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC);;
```

### Informal statement
For any natural numbers $m$ and $n$, if $m \neq 0$, then:

$$\ln(m) \cdot (\pi(n) - \pi(m)) \leq \frac{3}{2} \cdot n$$

where $\pi(x)$ counts the number of prime numbers less than or equal to $x$.

### Informal proof
We prove this by considering two cases.

Case 1: When $m \leq n$
- We'll show that $\theta(n) \geq \ln(m) \cdot (\pi(n) - \pi(m))$, which combined with the known bound $\theta(n) \leq \frac{3}{2} \cdot n$ will give us the desired result.
- Since $m \leq n$, we can write $n = m + d$ for some $d \geq 0$.
- Using the definitions of $\pi(n)$ and $\theta(n)$:
  - $\pi(n) - \pi(m) = \sum_{r=m+1}^{n} [r \text{ is prime}]$, where $[P]$ is 1 if $P$ is true and 0 otherwise
  - $\theta(n) - \theta(m) = \sum_{r=m+1}^{n} \ln(r) \cdot [r \text{ is prime}]$ 
- Observe that for any prime $r > m$, we have $\ln(r) \geq \ln(m)$ since $\ln$ is monotonically increasing.
- Thus, $\ln(m) \cdot (\pi(n) - \pi(m)) \leq \theta(n) - \theta(m) \leq \theta(n)$ (since $\theta(m) \geq 0$)
- We know that $\theta(n) \leq \frac{3}{2} \cdot n$ by `THETA_UBOUND_3_2`
- Therefore, $\ln(m) \cdot (\pi(n) - \pi(m)) \leq \frac{3}{2} \cdot n$

Case 2: When $m > n$
- In this case, $\pi(n) - \pi(m) \leq 0$ since $\pi$ is monotonically increasing.
- Since $m \neq 0$, we have $\ln(m) > 0$ (as $m \geq 1$).
- Thus, $\ln(m) \cdot (\pi(n) - \pi(m)) \leq 0 \leq \frac{3}{2} \cdot n$ since $\frac{3}{2} \cdot n \geq 0$.

Therefore, the inequality holds for all $m \neq 0$ and all natural numbers $n$.

### Mathematical insight
This theorem provides a bound on the difference of prime counting functions scaled by the natural logarithm. The result is important in analytic number theory and relates to the distribution of prime numbers.

The key insight is that the function $\theta(n) = \sum_{p \leq n, p \text{ prime}} \ln(p)$ serves as an effective bridge between the prime counting function $\pi(n)$ and explicit bounds in terms of $n$.

This result is part of broader work leading toward the Prime Number Theorem, which states that $\pi(n)$ is asymptotically $\frac{n}{\ln(n)}$.

### Dependencies
#### Theorems
- `REAL_MUL_RID`: $\forall x.\ x \cdot 1 = x$
- `REAL_MUL_RZERO`: $\forall x.\ x \cdot 0 = 0$
- `REAL_LE_REFL`: $\forall x.\ x \leq x$
- `REAL_LTE_TRANS`: $\forall x\ y\ z.\ x < y \wedge y \leq z \Rightarrow x < z$
- `REAL_LE_TRANS`: $\forall x\ y\ z.\ x \leq y \wedge y \leq z \Rightarrow x \leq z$
- `REAL_LE_MUL`: $\forall x\ y.\ 0 \leq x \wedge 0 \leq y \Rightarrow 0 \leq (x \cdot y)$
- `REAL_SUB_LE`: $\forall x\ y.\ 0 \leq (x - y) \Leftrightarrow y \leq x$
- `REAL_POS`: $\forall n.\ 0 \leq n$
- `SUM_LE`: $\forall f\ g\ m\ n.\ (\forall r.\ m \leq r \wedge r < n + m \Rightarrow f(r) \leq g(r)) \Rightarrow \text{sum}(m,n) f \leq \text{sum}(m,n) g$
- `SUM_CMUL`: $\forall f\ c\ m\ n.\ \text{sum}(m,n) (\lambda n.\ c \cdot f(n)) = c \cdot \text{sum}(m,n) f$
- `SUM_SPLIT`: $\forall f\ n\ p.\ \text{sum}(m,n) f + \text{sum}(m + n,p) f = \text{sum}(m,n + p) f$
- `LN_MONO_LE`: $\forall x\ y.\ 0 < x \wedge 0 < y \Rightarrow (\ln(x) \leq \ln(y) \Leftrightarrow x \leq y)$
- `LN_POS`: $\forall x.\ 1 \leq x \Rightarrow 0 \leq \ln(x)$
- `THETA_UBOUND_3_2`: $\forall n.\ \theta(n) \leq \frac{3}{2} \cdot n$
- `THETA_POS`: $\forall n.\ 0 \leq \theta(n)$
- `PII_MONO`: $\forall m\ n.\ m \leq n \Rightarrow \pi(m) \leq \pi(n)$

#### Definitions
- `ln`: $\ln(x) = \epsilon u.\ \exp(u) = x$
- `theta`: $\theta(n) = \sum_{i=1}^{n} (\text{if prime}(i) \text{ then } \ln(i) \text{ else } 0)$
- `pii`: $\pi(n) = \sum_{i=1}^{n} (\text{if prime}(i) \text{ then } 1 \text{ else } 0)$

### Porting notes
When porting this theorem:
1. Ensure that your system has proper definitions for the prime counting function $\pi$ and the Chebyshev function $\theta$.
2. Be careful with the handling of indexed summations and their associated theorems.
3. The proof uses case analysis on whether $m \leq n$ or $m > n$, which should be straightforward to implement in most systems.
4. The proof relies on the monotonicity of the logarithm function, so ensure that the necessary properties of $\ln$ are available.

---

## PII_ISQRT_INDUCT

### PII_ISQRT_INDUCT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PII_ISQRT_INDUCT = prove
 (`!n. 50 <= n
       ==> ln(&n) * pii(n)
           <= &9 / &4 * (&3 / &2 * &n + ln(&(ISQRT(n))) * pii(ISQRT(n)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(SPECL [`ISQRT n`; `n:num`] PII_CHANGE) THEN
  SUBGOAL_THEN `~(ISQRT n = 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[ARITH] THEN
    DISCH_TAC THEN UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `a * p <= ls * p ==> ls * (p - ps) <= an ==> a * p <= an + ls * ps`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PII_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ln((&(ISQRT n) + &1) pow 2)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &n /\ &n <= (&(ISQRT n) + &1) pow 2`
     (fun th -> MESON_TAC[th; REAL_LTE_TRANS; LN_MONO_LE]) THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE;
                REAL_OF_NUM_LT] THEN
    SIMP_TAC[ISQRT_WORKS; LT_IMP_LE] THEN
    UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LN_POW; REAL_POS; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `a - b <= b * (d - &1) ==> a <= b * d`) THEN
  ASM_SIMP_TAC[GSYM LN_DIV; REAL_ARITH `&0 < x ==> &0 < x + &1`;
               REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&(ISQRT n))` THEN
  ASM_SIMP_TAC[LN_LE; REAL_POS; REAL_LE_INV_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  SUBGOAL_THEN `&7 <= &(ISQRT n)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`&(ISQRT n)`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  SIMP_TAC[LN_POS; REAL_LE_ADD; REAL_POS; REAL_ARITH `&7 <= x ==> &1 <= x`]);;
```

### Informal statement
For any natural number $n$ such that $n \geq 50$, the following inequality holds:
$$\ln(n) \cdot \pi(n) \leq \frac{9}{4} \cdot \left(\frac{3}{2} \cdot n + \ln(ISQRT(n)) \cdot \pi(ISQRT(n))\right)$$

where:
- $\ln(n)$ is the natural logarithm of $n$
- $\pi(n)$ (denoted as `pii(n)` in HOL Light) is the prime counting function that gives the number of primes less than or equal to $n$
- $ISQRT(n)$ is the integer square root of $n$ (the largest integer $m$ such that $m^2 \leq n$)

### Informal proof
This theorem establishes an inductive bound on the prime counting function.

The proof proceeds through several algebraic manipulations and inequalities:

- First, we rearrange the inequality by dividing both sides by $\ln(n)$ (which is positive since $n \geq 50$).

- We apply the theorem `PII_CHANGE` to bound $\ln(ISQRT(n)) \cdot (\pi(n) - \pi(ISQRT(n)))$.
  * We verify that $ISQRT(n) \neq 0$ for $n \geq 50$ using `ISQRT_WORKS`.

- For the logarithm terms, we establish that:
  * $\ln(n) \leq \ln((ISQRT(n) + 1)^2)$ because $n \leq (ISQRT(n) + 1)^2$ by the definition of $ISQRT$.
  * $\ln((ISQRT(n) + 1)^2) = 2 \cdot \ln(ISQRT(n) + 1)$ using the properties of logarithms.

- We show that $\ln(ISQRT(n) + 1) - \ln(ISQRT(n)) \leq \frac{1}{ISQRT(n)}$ using the inequality $\ln(1+x) \leq x$ for $x \geq 0$.

- The proof uses the fact that $ISQRT(n) \geq 7$ when $n \geq 50$, which allows us to apply various inequalities.

- Finally, we apply `OVERPOWER_LEMMA` to establish an appropriate bound for the difference between the two sides of the inequality, completing the proof.

### Mathematical insight
This theorem provides an important inductive bound for the prime counting function $\pi(n)$. It establishes a relationship between $\pi(n)$ and $\pi(ISQRT(n))$, which is crucial for obtaining asymptotic estimates of the distribution of prime numbers.

The bound is part of a larger program leading to results like Chebyshev's bounds or even the Prime Number Theorem. By relating $\pi(n)$ to $\pi(ISQRT(n))$, it enables recursive estimates that eventually lead to asymptotic bounds.

The constant factors ($\frac{9}{4}$ and $\frac{3}{2}$) are carefully chosen to make the inductive argument work. This theorem is likely used in a proof of Bertrand's postulate or related results about prime number distribution.

### Dependencies
- **Definitions:**
  - `pii`: The prime counting function
  - `ISQRT`: Integer square root function
  - `ln`: Natural logarithm function

- **Theorems:**
  - `PII_CHANGE`: Bounds the change in the prime counting function
  - `ISQRT_WORKS`: Properties of the integer square root function
  - `PII_POS`: Positivity of the prime counting function
  - `LN_POW`: Logarithm of a power
  - `LN_DIV`: Logarithm of a quotient
  - `LN_LE`: Upper bound for ln(1+x)
  - `LN_POS`: Positivity of logarithm for arguments ≥ 1
  - `OVERPOWER_LEMMA`: A key inequality for establishing bounds
  - Other supporting theorems on real numbers and logarithms

### Porting notes
- The integer square root function might be implemented differently in other systems.
- The prime counting function may already exist in standard libraries of other proof assistants, possibly with different notation.
- The proof makes heavy use of HOL Light's automation for real arithmetic (REALCALC_REL_CONV), which may need to be replaced with appropriate tactics in the target system.
- The `OVERPOWER_LEMMA` used in this proof is an important utility theorem that may need to be ported first.

---

## PII_UBOUND_5

### Name of formal statement
PII_UBOUND_5

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_UBOUND_5 = prove
 (`!n. 3 <= n ==> pii(n) <= &5 * (&n / ln(&n))`,
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < 50` THEN ASM_SIMP_TAC[PII_UBOUND_CASES_50] THEN
  DISCH_THEN(MP_TAC o SPEC `ISQRT n`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  SUBGOAL_THEN `7 <= ISQRT n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `7 <= n ==> 3 <= n`;
               ARITH_RULE `50 <= n ==> 3 <= n`] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `(ISQRT n) EXP 2 < n EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN REWRITE_TAC[EXP_2] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * n < m ==> n < m`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PII_ISQRT_INDUCT) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&9 / &4 * (&3 / &2 * &n + &5 * &(ISQRT n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[REAL_LE_LADD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i * (a * c) <= n * (d - a * b) ==> a * (b * n + c * i) <= d * n`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(ISQRT n) * &7` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `ISQRT n * ISQRT n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS]]);;
```

### Informal statement
For all natural numbers $n \geq 3$, we have:
$$\pi(n) \leq 5 \cdot \frac{n}{\ln(n)}$$

where $\pi(n)$ is the prime counting function (the number of primes less than or equal to $n$), and $\ln(n)$ is the natural logarithm of $n$.

### Informal proof
This theorem is proven using well-founded induction on $n$.

- Base case: For $n < 50$, we apply the theorem `PII_UBOUND_CASES_50` which directly establishes that $\ln(n) \cdot \pi(n) \leq 5 \cdot n$ for $3 \leq n < 50$, which is equivalent to our goal $\pi(n) \leq 5 \cdot \frac{n}{\ln(n)}$.

- Inductive case: For $n \geq 50$, we proceed as follows:
  1. We apply the induction hypothesis to $\text{ISQRT}(n)$ (the integer square root of $n$).
  2. We verify that $\text{ISQRT}(n) \geq 7$, which ensures the induction hypothesis is applicable (as we need $\text{ISQRT}(n) \geq 3$).
  3. Use `PII_ISQRT_INDUCT` to establish the relationship between $\pi(n)$ and $\pi(\text{ISQRT}(n))$.
  4. Through a series of algebraic manipulations, we show that:
     $$\ln(n) \cdot \pi(n) \leq \frac{9}{4} \cdot \left(\frac{3}{2} \cdot n + \ln(\text{ISQRT}(n)) \cdot \pi(\text{ISQRT}(n))\right)$$
  5. Apply the induction hypothesis to substitute $\pi(\text{ISQRT}(n)) \leq 5 \cdot \frac{\text{ISQRT}(n)}{\ln(\text{ISQRT}(n))}$.
  6. Simplify to show $\ln(n) \cdot \pi(n) \leq 5 \cdot n$, which is equivalent to our goal.
  7. The final step involves showing that $\text{ISQRT}(n) \cdot 7 \leq n$, which follows from the fact that $\text{ISQRT}(n)^2 \leq n$ (a property of the integer square root).

### Mathematical insight
This theorem establishes a significant upper bound on the prime counting function $\pi(n)$, stating that the density of primes is at most proportional to $\frac{n}{\ln(n)}$. This is a weaker version of the Prime Number Theorem, which states that $\pi(n) \sim \frac{n}{\ln(n)}$ as $n \to \infty$.

The proof uses a recursive approach, relating the value of the prime counting function at $n$ to its value at $\text{ISQRT}(n)$. This technique is powerful for establishing bounds of number-theoretic functions.

The constant 5 in this upper bound is not optimal, but sufficient for applications like Bertrand's postulate. The prime number theorem would eventually show that the optimal constant approaches 1 as $n$ increases.

### Dependencies
- **Theorems:**
  - `REAL_LE_TRANS`: Transitivity of less-than-or-equal relation on reals
  - `REAL_LE_LADD`: Cancellation property for addition with inequality
  - `REAL_POS`: Non-negativity of real numbers corresponding to natural numbers
  - `LN_POS_LT`: Positivity of natural logarithm for values greater than 1
  - `ISQRT_WORKS`: Properties of the integer square root function
  - `PII_UBOUND_CASES_50`: Base cases for n < 50
  - `PII_ISQRT_INDUCT`: Induction step relating π(n) to π(ISQRT(n))

- **Definitions:**
  - `ln`: Natural logarithm function
  - `ISQRT`: Integer square root function
  - `pii`: Prime counting function

### Porting notes
When porting this theorem:
1. First ensure all dependencies, especially properties of the integer square root function and the prime counting function, are properly defined.
2. The proof uses well-founded induction, which might need to be implemented differently in other systems.
3. The base cases for n < 50 are handled separately, which suggests a significant computational component that may need optimization in other systems.
4. The algebraic manipulations involve several real number identities and inequalities that will need careful verification.

---

