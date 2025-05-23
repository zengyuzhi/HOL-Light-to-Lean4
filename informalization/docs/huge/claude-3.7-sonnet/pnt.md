# pnt.ml

## Overview

Number of statements: 89

This file contains a formalization of the "second proof" of the Prime Number Theorem following Newman's approach. It builds upon complex analysis (via Cauchy's theorem), number theory primitives from Pocklington's work, and the Mangoldt function to establish the asymptotic distribution of prime numbers. The proof likely connects analytic properties of the Riemann zeta function with the counting function of primes through careful application of complex analysis techniques.

## LT_NORM_CPOW_NUM

### LT_NORM_CPOW_NUM
- `LT_NORM_CPOW_NUM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LT_NORM_CPOW_NUM = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> &1 < norm(Cx(&n) cpow s)`,
  SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 0 < n`] THEN
  REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
  SIMP_TAC[REAL_LT_MUL; LOG_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 1 < n`]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$ where $\text{Re}(s) > 0$ and $n \geq 2$, we have:
$$\|n^s\| > 1$$

In other words, the norm of $n$ raised to the complex power $s$ is greater than 1 when the real part of $s$ is positive and $n \geq 2$.

### Informal proof
The proof proceeds as follows:

- First, we simplify the expression using `NORM_CPOW_REAL`, which states that for a positive real number $a$ and complex number $s$, $\|a^s\| = a^{\text{Re}(s)}$.
- Since $n$ is a natural number with $n \geq 2$, we convert it to a complex number using `Cx`, then use `REAL_CX` and `RE_CX` to extract its real part.
- We establish that $n > 0$ when $n \geq 2$ using a simple arithmetic rule.
- Next, we rewrite the goal using the exponential form: $1 = e^0$, and apply the monotonicity of exponential function.
- Since $\text{Re}(s) > 0$ and $n > 1$ (which follows from $n \geq 2$), we have $\text{Re}(s) \cdot \ln(n) > 0$.
- Therefore, $e^{\text{Re}(s) \cdot \ln(n)} > e^0 = 1$, which gives us $\|n^s\| > 1$.

### Mathematical insight
This theorem establishes a key property of complex powers of integers that is used in analytic number theory, particularly in the proof of the Prime Number Theorem. When working with Dirichlet series and zeta functions, understanding the behavior of terms like $n^s$ for complex $s$ is essential.

The result provides a lower bound on the norm of $n^s$ when $\text{Re}(s) > 0$ and $n \geq 2$, showing that these terms are bounded away from zero. This is significant for convergence properties of series involving these terms and for analyzing the behavior of related functions in the complex plane.

### Dependencies
- `NORM_CPOW_REAL`: Relates the norm of a real number raised to complex power to the real part of the exponent
- `REAL_CX`: Conversion between real and complex numbers
- `RE_CX`: Extracts the real part of a complex number
- `REAL_OF_NUM_LT`: Inequality for real numbers converted from natural numbers
- `REAL_EXP_0`: Property that $e^0 = 1$
- `REAL_EXP_MONO_LT`: Monotonicity of the exponential function
- `REAL_LT_MUL`: Multiplication preserves strict inequality under positive values
- `LOG_POS_LT`: Natural logarithm of values greater than 1 is positive

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the definition of complex power `cpow` matches HOL Light's definition
- Check how the target system handles the real part of complex numbers
- Verify that the target system has appropriate libraries for working with complex exponentials and logarithms

---

## CPOW_NUM_NE_1

### Name of formal statement
CPOW_NUM_NE_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CPOW_NUM_NE_1 = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> ~(Cx(&n) cpow s = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SYM o AP_TERM `norm:complex->real`) THEN
  ASM_SIMP_TAC[LT_NORM_CPOW_NUM; COMPLEX_NORM_CX; REAL_ABS_NUM;
               REAL_LT_IMP_NE]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$, if the real part of $s$ is positive (i.e., $\text{Re}(s) > 0$) and $n \geq 2$, then $n^s \neq 1$.

Here, $n^s$ is represented as $\text{Cx}(n) \text{ cpow } s$, where $\text{Cx}(n)$ is the complex number with real part $n$ and imaginary part 0.

### Informal proof
The proof proceeds by contradiction. Assume that $n^s = 1$.

1. We start by applying the complex norm function to both sides of the assumed equality $n^s = 1$.

2. By the theorem `LT_NORM_CPOW_NUM`, we know that when $\text{Re}(s) > 0$ and $n \geq 2$, we have $|n^s| > 1$.

3. However, $|1| = 1$, which would mean $|n^s| = 1$.

4. This contradiction shows that $n^s \neq 1$.

More specifically, the proof uses:
* The fact that if $a = b$, then $|a| = |b|$ (applying the norm function)
* That $|n^s| > 1$ when $\text{Re}(s) > 0$ and $n \geq 2$
* That $|\text{Cx}(n)| = |n| = n$ for natural numbers $n$
* The principle that if $a > b$, then $a \neq b$ (`REAL_LT_IMP_NE`)

### Mathematical insight
This theorem establishes a fundamental property of complex powers of integers. It states that when raising an integer greater than or equal to 2 to a complex power with positive real part, the result is never 1. 

This result is important in complex analysis and number theory. It can be seen as a generalization of the fact that for real $s > 0$, if $n \geq 2$ then $n^s > 1$, extending this to the complex domain. The result is useful in contexts involving complex exponentiation, particularly in analytic number theory and the study of Dirichlet series.

### Dependencies
- **Theorems**:
  - `LT_NORM_CPOW_NUM`: States that for natural number $n \geq 2$ and complex $s$ with positive real part, the norm of $n^s$ is greater than 1.
- **Functions and Operations**:
  - `Cx`: Converts a real number to a complex number with zero imaginary part
  - `cpow`: Complex exponentiation
  - `norm`: Complex norm/absolute value
  - `Re`: Real part of a complex number

### Porting notes
When porting this theorem to another system:
1. Ensure the complex exponentiation operation is properly defined
2. Check that the representation of real numbers as complex numbers is consistent
3. The proof relies on properties of complex norms and inequalities, which should be available in most proof assistants
4. The dependency `LT_NORM_CPOW_NUM` should be ported first

---

## FINITE_ATMOST

### Name of formal statement
FINITE_ATMOST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_ATMOST = prove
 (`!P n. FINITE {m:num | P m /\ m <= n}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  SIMP_TAC[LE_0; FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG]);;
```

### Informal statement
For any predicate $P$ on natural numbers and any natural number $n$, the set $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is finite.

### Informal proof
To prove that $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is finite, we use the fact that any subset of a finite set is finite.

- We show that $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is a subset of $\{0, 1, 2, \ldots, n\}$ (denoted as $[0..n]$ in HOL Light).
- The set $[0..n]$ is finite, as it is a closed interval of natural numbers.
- For any $m$ in our target set, we have $P(m)$ and $m \leq n$, which immediately implies that $m \in [0..n]$.
- Therefore, $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is a subset of $[0..n]$.
- Since $[0..n]$ is finite, any subset of it, including our target set, must also be finite.

### Mathematical insight
This theorem establishes that any set of natural numbers that are bounded above and satisfy a predicate is finite. This is a fundamental result for reasoning about finite sets in number theory and computational contexts. The key insight is that we don't need to know anything about the specific predicate $P$ - the upper bound alone guarantees finiteness.

The result is particularly useful when working with algorithms, complexity analysis, or any context where we need to establish that certain sets of natural numbers are finite.

### Dependencies
- `FINITE_SUBSET`: If a set is a subset of a finite set, then it is finite
- `LE_0`: For any natural number $n$, $0 \leq n$
- `FINITE_NUMSEG`: The set of natural numbers in a closed interval $[a..b]$ is finite
- `SUBSET`: Set inclusion relation
- `IN_ELIM_THM`: Used for manipulating set comprehensions
- `IN_NUMSEG`: Membership condition for a closed interval of natural numbers

### Porting notes
When porting this theorem to other systems:
- This is a straightforward result that should be easily provable in any system with a good library for natural numbers and finite sets.
- The proof relies on basic set operations and the notion that any bounded set of natural numbers is finite.
- In some systems, you might need to first establish that the set of naturals up to $n$ is finite, but this is a standard library result in most proof assistants.

---

## PRIME_ATMOST_ALT

### Name of formal statement
PRIME_ATMOST_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_ATMOST_ALT = prove
 (`{p | prime p /\ p <= n} = {p | p IN 1..n /\ prime p}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC);;
```

### Informal statement
The theorem states that the set of prime numbers less than or equal to $n$ can be expressed as:
$$\{p \mid \text{prime}(p) \land p \leq n\} = \{p \mid p \in \{1,2,\ldots,n\} \land \text{prime}(p)\}$$

This theorem establishes the equivalence between two ways of describing the set of primes up to $n$: directly using the condition $p \leq n$, or by filtering the primes from the set of natural numbers from 1 to $n$.

### Informal proof
We prove that the two sets are equal by showing they have the same elements.

For any number $p$, we need to show:
$p \in \{p \mid \text{prime}(p) \land p \leq n\}$ if and only if $p \in \{p \mid p \in \{1,2,\ldots,n\} \land \text{prime}(p)\}$

The proof proceeds as follows:
* We consider whether $p$ is prime or not:
  * If $p$ is prime, we need to show that $p \leq n$ is equivalent to $p \in \{1,2,\ldots,n\}$.
  * We use the fact that all primes are non-zero (from `PRIME_IMP_NZ`).
  * Since $p$ is a positive number (as it's prime), the condition $p \in \{1,2,\ldots,n\}$ is precisely equivalent to $p \leq n$ and $1 \leq p$, which simplifies to just $p \leq n$ since all primes are at least 2.
  * Therefore, the membership conditions for both sets are equivalent when $p$ is prime.
  * If $p$ is not prime, it belongs to neither set, so the equivalence trivially holds.

The result follows by arithmetic reasoning.

### Mathematical insight
This theorem provides an alternative characterization of the set of primes up to a given bound $n$. While the result might seem trivial, it's useful in contexts where one needs to switch between different representations of the set of primes.

The theorem shows that we can either directly filter the set of all prime numbers by the condition $p \leq n$, or we can first restrict our attention to the finite set $\{1,2,\ldots,n\}$ and then filter for primality.

This equivalence is particularly useful in computational contexts where working with the finite set of numbers up to $n$ is more tractable than working with the infinite set of all primes.

### Dependencies
- **Theorems**:
  - `EXTENSION`: For proving equality of sets by showing they contain the same elements
  - `IN_ELIM_THM`: For expanding set membership notation
  - `IN_NUMSEG`: For interpreting membership in an integer range
  - `PRIME_IMP_NZ`: For using the fact that prime numbers are non-zero

### Porting notes
When porting this theorem:
- The proof relies on arithmetic reasoning that might need explicit steps in some proof assistants.
- The representation of number ranges like `1..n` might differ between systems.
- Make sure the primality definition you're working with also implies that prime numbers are at least 2.

---

## nearzeta

### Name of formal statement
nearzeta

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let nearzeta = new_definition
 `nearzeta n s = infsum (from n)
                        (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                               Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))`;;
```

### Informal statement
The near zeta function is defined as:

$$\text{nearzeta}(n, s) = \sum_{m=n}^{\infty} \left[ \frac{s-1}{m^s} - \left( \frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}} \right) \right]$$

where:
- $n$ is a positive integer that serves as the starting index for the infinite sum
- $s$ is a complex number
- $\text{infsum}$ represents the infinite sum operation
- $\text{from}(n)$ represents the set of integers starting from $n$
- $\text{Cx}$ converts real numbers to complex numbers
- $\text{cpow}$ denotes complex exponentiation

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The nearzeta function serves as an auxiliary function related to the Riemann zeta function. Its name suggests it's "near" to the zeta function but with some important differences. The key features of this definition are:

1. Unlike the standard zeta function, this function is analytic in the right half-plane (as mentioned in the comment).
2. The definition uses a telescoping series component $\left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)$ that helps control convergence behavior.
3. The starting index $n$ allows flexibility in where the summation begins, which can be useful for various analytical purposes.

This function is likely used in the context of analytic continuation of the Riemann zeta function or in proofs about its properties. By structuring the function this way, it avoids some of the convergence issues that the standard zeta function faces in certain regions of the complex plane.

### Dependencies
#### Definitions
- `infsum`: Infinite sum operation
- `from`: Function that generates the set of integers starting from a given number
- `cpow`: Complex exponentiation operation

### Porting notes
When porting this definition:
1. Ensure the target system has a comparable notion of infinite summation or series convergence
2. Verify that complex exponentiation is properly defined in the target system
3. Pay attention to the handling of type conversions between reals and complex numbers (the `Cx` function in HOL Light)
4. The definition relies on a specific formulation that ensures analyticity in the right half-plane, so maintain this precise structure

---

## genzeta

### genzeta

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let genzeta = new_definition
 `genzeta n s = if s = Cx(&1) then complex_derivative (nearzeta n) (Cx(&1))
                else (nearzeta n s + Cx(&1) / Cx(&n) cpow (s - Cx(&1))) /
                     (s - Cx(&1))`;;
```

### Informal statement
The `genzeta` function is defined as:

$$\text{genzeta}(n, s) = \begin{cases} 
\frac{d}{ds}\text{nearzeta}(n, s)\big|_{s=1} & \text{if } s = 1 \\
\frac{\text{nearzeta}(n, s) + \frac{1}{n^{s-1}}}{s-1} & \text{if } s \neq 1
\end{cases}$$

where:
- $n$ is a natural number
- $s$ is a complex number
- $\text{nearzeta}(n, s)$ is an auxiliary function in the construction of the zeta function
- $\frac{d}{ds}\text{nearzeta}(n, s)\big|_{s=1}$ represents the complex derivative of $\text{nearzeta}(n, s)$ with respect to $s$, evaluated at $s=1$

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
The `genzeta` function is part of the formal construction of the Riemann zeta function in HOL Light. This definition is designed to handle the singularity at $s = 1$, where the zeta function has a simple pole.

The definition splits into two cases:
1. At $s = 1$, where a direct calculation would encounter a division by zero, it uses the complex derivative of the `nearzeta` function.
2. For all other values of $s$, it uses an algebraic expression involving `nearzeta` and a correction term $\frac{1}{n^{s-1}}$.

This construction helps establish the analytic continuation of the zeta function to the complex plane except at $s = 1$. The parameter $n$ allows for controlling the convergence properties of the approximation to the zeta function.

The function is structured this way to capture the behavior that $\zeta_n(s) - \frac{1}{(s-1)^{n-1}}$ is analytic, which is an important property in the theory of the Riemann zeta function.

### Dependencies
#### Definitions
- `nearzeta`: An auxiliary function used in the construction of the zeta function, defined as:
  ```
  nearzeta n s = infsum (from n)
                 (λm. (s - Cx(&1)) / Cx(&m) cpow s -
                     (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                      Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))
  ```

### Porting notes
When porting this definition, special care should be taken with:
1. The complex derivative at $s = 1$
2. The handling of the complex power function `cpow`
3. Ensuring the definition correctly handles the singularity at $s = 1$

Different proof assistants may have different ways of representing complex derivatives and functions with removable singularities, so appropriate adaptations might be needed.

---

## zeta

### Name of formal statement
zeta

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zeta = new_definition
 `zeta s = genzeta 1 s`;;
```

### Informal statement
The Riemann zeta function, denoted as $\zeta(s)$, is defined as:

$$\zeta(s) = \text{genzeta}(1, s)$$

where $\text{genzeta}$ is a generalized zeta function.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The Riemann zeta function is a fundamental function in number theory and complex analysis. This definition defines $\zeta(s)$ as a special case of the generalized zeta function $\text{genzeta}(n, s)$ with $n=1$.

From the dependency provided, we can see that $\text{genzeta}(n, s)$ is defined as:
- When $s = 1$: $\text{genzeta}(n, s) = \frac{d}{ds}\text{nearzeta}(n, s)$ evaluated at $s = 1$
- When $s \neq 1$: $\text{genzeta}(n, s) = \frac{\text{nearzeta}(n, s) + \frac{1}{n^{s-1}}}{s-1}$

The Riemann zeta function is typically defined for $\Re(s) > 1$ as:
$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$$

However, the definition used here provides an analytic continuation of the Riemann zeta function to the entire complex plane except for a simple pole at $s = 1$.

### Dependencies
- Definitions:
  - `genzeta`: Defines a generalized zeta function that provides analytic continuation
  - `zeta`: The Riemann zeta function definition itself (current item)

### Porting notes
When porting this definition:
1. Ensure the underlying `nearzeta` and `genzeta` functions are properly defined first
2. Pay attention to the analytic continuation at $s = 1$ which involves a complex derivative
3. In some proof assistants, you might need to separately define the Riemann zeta function for the convergent case ($\Re(s) > 1$) and then establish the analytic continuation

---

## NEARZETA_BOUND_LEMMA

### NEARZETA_BOUND_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NEARZETA_BOUND_LEMMA = prove
 (`!s n. ~(n = 0) /\ &0 <= Re s + &1
         ==> norm((s - Cx(&1)) / Cx(&n) cpow s -
                  (Cx(&1) / Cx(&n) cpow (s - Cx(&1)) -
                   Cx(&1) / Cx(&(n + 1)) cpow (s - Cx(&1)))) <=
             norm(s * (s - Cx(&1)) / Cx(&n) cpow (s + Cx(&1)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then Cx(&1) / z cpow (s - Cx(&1))
           else if n = 1 then (Cx(&1) - s) / z cpow s
           else s * (s - Cx(&1)) / z cpow (s + Cx(&1))`;
    `1`; `segment[Cx(&n),Cx(&n) + Cx(&1)]`;
    `norm(s * (s - Cx (&1)) / Cx(&n) cpow (s + Cx(&1)))`] COMPLEX_TAYLOR) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_SEGMENT] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `z:complex`] THEN STRIP_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC] THEN
    (SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
      [MATCH_MP_TAC RE_POS_SEGMENT THEN
       MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
       ASM_REWRITE_TAC[RE_ADD; RE_CX; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
       ASM_ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[RE_CX; REAL_LT_REFL];
       ALL_TAC])
    THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
        (ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`)) THEN
      ASM_REWRITE_TAC[ARITH] THEN COMPLEX_DIFF_TAC THEN
      ASM_REWRITE_TAC[CPOW_EQ_0] THEN
      SIMP_TAC[COMPLEX_POW_2; CPOW_ADD; CPOW_SUB; CPOW_N; COMPLEX_POW_1] THEN
      (SUBGOAL_THEN `~(z cpow s = Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[CPOW_EQ_0]; UNDISCH_TAC `~(z = Cx(&0))`]) THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `real z` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
      ASM_SIMP_TAC[REAL_CX; REAL_ADD];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[RE_ADD; RE_CX] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    UNDISCH_TAC `z IN segment[Cx (&n),Cx (&n) + Cx (&1)]` THEN
    REWRITE_TAC[segment; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE_CX] THEN
    UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CONV `0..1`] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; COMPLEX_MUL_RID] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx(&n)`; `Cx(&n) + Cx(&1)`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; COMPLEX_NORM_CX; COMPLEX_ADD_SUB] THEN
  REWRITE_TAC[VECTOR_ADD_RID; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_RID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; complex_div] THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement

For all complex numbers $s$ and natural numbers $n$ where $n \neq 0$ and $\text{Re}(s) + 1 \geq 0$, the following inequality holds:

$$\left\lVert \frac{s - 1}{n^s} - \left(\frac{1}{n^{s-1}} - \frac{1}{(n+1)^{s-1}}\right) \right\rVert \leq \left\lVert \frac{s(s-1)}{n^{s+1}} \right\rVert$$

where $\lVert \cdot \rVert$ denotes the complex norm, and $z^s$ denotes complex exponentiation.

### Informal proof

The proof uses the Complex Taylor theorem to establish the bound. The key strategy is to consider the function:

$$f(z) = \begin{cases}
\frac{1}{z^{s-1}} & \text{if } n = 0 \\
\frac{1-s}{z^s} & \text{if } n = 1 \\
\frac{s(s-1)}{z^{s+1}} & \text{otherwise}
\end{cases}$$

We apply the Complex Taylor theorem over the line segment from $n$ to $n+1$ and show that the remainder term provides our desired bound.

The proof proceeds as follows:

* We verify that $f(z)$ is holomorphic on the segment $[n,n+1]$ by checking that each case is differentiable, using the fact that $\text{Re}(z) > 0$ for all points in this segment.

* We ensure that $z^s$ is non-zero for all $z$ in the segment since $\text{Re}(z) > 0$.

* We establish that for any $z$ in the segment $[n,n+1]$, the norm of the second derivative satisfies:
  $$\|f''(z)\| \leq \left\|\frac{s(s-1)}{n^{s+1}}\right\|$$
  
  This uses the fact that $z$ being real and in the segment implies $|z| \geq n$, and therefore $|z|^{-(s+1)} \leq n^{-(s+1)}$ when $\text{Re}(s) + 1 \geq 0$.

* By the Complex Taylor theorem, the difference between the original expression and its first-order approximation is bounded by the maximum of the second derivative, which gives us our result.

* After applying the theorem, we simplify the expressions appropriately and verify that the resulting inequality matches our claim.

### Mathematical insight

This lemma provides a bound for the error when approximating a term related to the Riemann zeta function. It's specifically useful when analyzing the behavior of the zeta function near $s=1$, which is a critical point in its analysis.

The key insight is using complex Taylor expansion with a carefully chosen remainder bound. The bound established is tight enough to be useful in convergence proofs for zeta-related series, yet simple enough to work with in subsequent proofs.

This lemma is part of a wider framework for analyzing the analytic properties of the Riemann zeta function, particularly near its pole at $s=1$.

### Dependencies

**Theorems:**
- `COMPLEX_TAYLOR`: Taylor's theorem for complex functions
- `CONVEX_SEGMENT`: The line segment is convex
- `RE_POS_SEGMENT`: Real part is positive on a segment between points with positive real parts
- `REAL_SEGMENT`: Points on a segment between real points are real
- `NORM_CPOW_REAL`: Norm of complex power of a real number
- `CPOW_EQ_0`: Conditions for complex power to equal zero
- `COMPLEX_NORM_MUL`, `COMPLEX_NORM_DIV`, `COMPLEX_NORM_POW`: Properties of complex norms
- `COMPLEX_DIFF_TAC`: Tactic for differentiating complex functions

### Porting notes
- This proof extensively uses complex analysis, particularly complex differentiation and Taylor's theorem.
- The implementation should handle complex exponentiation ($z^s$ for complex $s$) correctly.
- Careful attention to the complex norm and the real part extraction operation is needed.
- The proof uses a piecewise function definition inside the theorem statement, which may need special handling in systems that don't support such direct definitions within proofs.

---

## NORM_CPOW_LOWERBOUND

### NORM_CPOW_LOWERBOUND
- NORM_CPOW_LOWERBOUND

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NORM_CPOW_LOWERBOUND = prove
 (`!m s n. &m <= Re s /\ ~(n = 0) ==> &n pow m <= norm(Cx(&n) cpow s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&m * log(&n))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_LE_REFL];
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_EXP_0; EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    SIMP_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;
```

### Informal statement
For all natural numbers $m$ and $n$ where $n \neq 0$, and for any complex number $s$ with real part $\text{Re}(s) \geq m$, the following inequality holds:
$$n^m \leq |\mathbb{C}(n)^s|$$

where $\mathbb{C}(n)$ represents the complex number corresponding to the natural number $n$, and $\mathbb{C}(n)^s$ denotes complex exponentiation.

### Informal proof
We prove that for all $m$, $s$, and non-zero $n$, if $m \leq \text{Re}(s)$, then $n^m \leq |\mathbb{C}(n)^s|$.

The proof proceeds as follows:
- First, we simplify the norm of the complex power using the `NORM_CPOW_REAL` theorem, since $n$ is a real number.
- For a real number $n$ and complex exponent $s$, we have $|\mathbb{C}(n)^s| = n^{\text{Re}(s)} \cdot e^{-\text{Im}(s) \cdot \arg(n)}$
- Since $n > 0$, we have $\arg(n) = 0$, so $|\mathbb{C}(n)^s| = n^{\text{Re}(s)}$
- We establish a transitive inequality chain:
  * We show $n^m \leq e^{m \cdot \log(n)}$ using the property of exponentiation of natural numbers
  * We then show $e^{m \cdot \log(n)} \leq e^{\text{Re}(s) \cdot \log(n)} = n^{\text{Re}(s)}$ 
  * This second inequality follows because:
    - $m \leq \text{Re}(s)$ (given in our assumptions)
    - $\log(n) \geq 0$ (since $n > 0$)
    - Therefore $m \cdot \log(n) \leq \text{Re}(s) \cdot \log(n)$
    - The exponential function is monotonically increasing, so $e^{m \cdot \log(n)} \leq e^{\text{Re}(s) \cdot \log(n)}$
  * By transitivity, $n^m \leq |\mathbb{C}(n)^s|$, which proves our claim.

### Mathematical insight
This theorem establishes a lower bound for the norm of complex powers. It shows that when raising a natural number to a complex power, the resulting magnitude is at least as large as the natural number raised to the power of the real part's floor.

This result is useful in analytic number theory, particularly when dealing with complex analysis techniques applied to number-theoretic problems. The inequality provides bounds when working with complex powers, which appear frequently in the study of various zeta functions and related topics.

### Dependencies
- `NORM_CPOW_REAL`: Formula for the norm of a real number raised to a complex power
- `REAL_CX`: Converting a real number to a complex number
- `RE_CX`: Real part of a complex number
- `REAL_OF_NUM_LT`: Ordering of real numbers
- `LT_NZ`: Positive numbers are non-zero
- `REAL_EXP_N`: Exponential of natural numbers
- `EXP_LOG`: The identity $e^{\log(x)} = x$
- `REAL_EXP_MONO_LE`: Monotonicity of the exponential function
- `REAL_LE_RMUL`: Multiplication preserves inequality

### Porting notes
When implementing this in another system:
- Ensure the complex exponentiation operation is properly defined
- Check how the target system handles complex numbers and their operations
- Verify the definition of argument (arg) for real numbers, particularly that arg(n) = 0 for positive reals
- The proof relies on properties of the exponential and logarithm functions, so these need to be available in the target system

---

## ZETATERM_BOUND

### ZETATERM_BOUND
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZETATERM_BOUND = prove
 (`!s n m. &m <= Re s /\ ~(n = 0)
           ==> norm(Cx(&1) / Cx(&n) cpow s) <= inv(&n pow m)`,
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_CPOW_LOWERBOUND; REAL_OF_NUM_LT; LT_NZ]);;
```

### Informal statement
For all complex numbers $s$ and natural numbers $n$ and $m$, if $m \leq \text{Re}(s)$ and $n \neq 0$, then:

$$\left|\frac{1}{n^s}\right| \leq \frac{1}{n^m}$$

where $n^s$ denotes the complex power operation, and $|\cdot|$ denotes the complex norm.

### Informal proof
The proof establishes a bound on the term $\frac{1}{n^s}$ that appears in the Riemann zeta function.

First, we rewrite the norm of a complex quotient:
$$\left|\frac{1}{n^s}\right| = \frac{|1|}{|n^s|} = \frac{1}{|n^s|}$$

Since we know from `NORM_CPOW_LOWERBOUND` that $n^m \leq |n^s|$ when $m \leq \text{Re}(s)$ and $n \neq 0$, we can apply the property that $\frac{1}{a} \leq \frac{1}{b}$ when $b \leq a$ and $a,b > 0$.

Therefore:
$$\frac{1}{|n^s|} \leq \frac{1}{n^m}$$

This gives us the desired inequality.

### Mathematical insight
This theorem provides an upper bound for the magnitude of terms in the Riemann zeta function expansion. It shows that when the real part of $s$ is at least $m$, the magnitude of $\frac{1}{n^s}$ is bounded by $\frac{1}{n^m}$. This is crucial for proving convergence properties of the zeta function in regions of the complex plane.

The bound becomes tighter as the real part of $s$ increases, reflecting the improved convergence of the zeta function as we move further to the right in the complex plane.

### Dependencies
- Theorems:
  - `NORM_CPOW_LOWERBOUND`: Establishes that $n^m \leq |n^s|$ when $m \leq \text{Re}(s)$ and $n \neq 0$

### Porting notes
When porting this theorem to other systems:
- Ensure the definition of complex power operation is compatible
- Make sure the system has a proper handling of complex norms
- The inequality manipulation relies on properties of real numbers that should be available in most systems

---

## ZETA_CONVERGES_LEMMA

### Name of formal statement
ZETA_CONVERGES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_CONVERGES_LEMMA = prove
 (`!n s. &2 <= Re s ==> summable (from n) (\m. Cx(&1) / Cx(&m) cpow s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
  MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n - &1) - inv(&(n + 1) - &1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `lift(inv(&n - &1))` THEN
    MP_TAC(ISPECL [`\n. lift(inv(&n - &1))`; `n:num`] SERIES_DIFFS) THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    REWRITE_TAC[SEQ_HARMONIC];
    ALL_TAC] THEN
  EXISTS_TAC `2` THEN REWRITE_TAC[GE; IN_FROM] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_FIELD
   `&2 <= x ==> inv(x - &1) - inv((x + &1) - &1) = inv(x * (x - &1))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&n pow 2 <= x ==> &n * (&n - &1) <= x`) THEN
  MATCH_MP_TAC NORM_CPOW_LOWERBOUND THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$ where $\text{Re}(s) \geq 2$, the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges.

This is formally expressed as: for all $n$ and $s$, if $\text{Re}(s) \geq 2$, then the function $m \mapsto \frac{1}{m^s}$ is summable from $n$ onwards.

### Informal proof
We prove that the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges when $\text{Re}(s) \geq 2$ using comparison with a telescoping series.

1. We use the comparison test for series convergence, comparing our series with the telescoping series $\sum_{n} \left(\frac{1}{n-1} - \frac{1}{n+1-1}\right) = \sum_{n} \left(\frac{1}{n-1} - \frac{1}{n}\right)$

2. First, we show that this telescoping series converges:
   - We identify it as the series of differences $\frac{1}{n-1} - \frac{1}{n}$
   - This is a difference of consecutive terms in the sequence $\{\frac{1}{n-1}\}$
   - The sequence $\{\frac{1}{n-1}\}$ converges to 0 (as it's a shifted harmonic sequence)
   - Therefore, the series of differences converges to $\frac{1}{n-1} - \lim_{k\to\infty} \frac{1}{k-1} = \frac{1}{n-1} - 0 = \frac{1}{n-1}$

3. Then, we show that our original series terms are dominated by the telescoping series terms for $m \geq 2$:
   - When $m \geq 2$, the telescoping term simplifies to $\frac{1}{m-1} - \frac{1}{m} = \frac{1}{m(m-1)}$
   
4. To show the comparison inequality:
   - We need to prove that $\left|\frac{1}{m^s}\right| \leq \frac{1}{m(m-1)}$ for $m \geq 2$
   - This is equivalent to showing $m(m-1) \leq |m^s| = |m|^{\text{Re}(s)}$ when $\text{Re}(s) \geq 2$
   
5. We use the fact that $m^2 \leq |m^s|$ when $\text{Re}(s) \geq 2$ (from `NORM_CPOW_LOWERBOUND`)
   - Since $m(m-1) \leq m^2$ for $m \geq 2$, we have $m(m-1) \leq |m^s|$
   
6. Therefore, by the comparison test, our original series converges when $\text{Re}(s) \geq 2$.

### Mathematical insight
This lemma proves a basic convergence property of the zeta function tail series. The Riemann zeta function $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$ is known to converge absolutely for all complex $s$ with $\text{Re}(s) > 1$. This lemma establishes convergence for the stronger condition $\text{Re}(s) \geq 2$, which is useful for fundamental properties and computations.

The proof uses a comparison with a telescoping series, which is a standard analytical technique. The key insight is identifying a suitable comparison series that both converges and dominates the zeta function terms. The telescoping series was chosen because it simplifies to $\frac{1}{m(m-1)}$, which is comparable to $\frac{1}{m^2}$ when $m \geq 2$, making it ideal for comparison with $\frac{1}{m^s}$ when $\text{Re}(s) \geq 2$.

### Dependencies
#### Theorems
- `NORM_CPOW_LOWERBOUND`: Establishes a lower bound for the norm of complex powers, specifically that $n^m \leq |n^s|$ when $m \leq \text{Re}(s)$ and $n \neq 0$.
- `SERIES_COMPARISON`: The comparison test for series convergence.
- `SERIES_DIFFS`: Relates the sum of differences of consecutive terms to the difference of the first term and the limit.
- `SEQ_OFFSET_REV`: Allows shifting the index in a sequence.
- `SEQ_HARMONIC`: States that the harmonic sequence converges to 0.

### Porting notes
When porting this theorem:
- Ensure your system has a solid foundation for complex analysis, particularly for complex powers and norms.
- The proof relies heavily on the comparison test for series convergence, which should be available in most proof assistants.
- The telescoping series argument is standard but requires careful handling of indices.
- The inequality $m(m-1) \leq m^2$ for $m \geq 2$ is used implicitly and might need to be proved explicitly in some systems.

---

## ZETADIFF_CONVERGES

### ZETADIFF_CONVERGES
- ZETADIFF_CONVERGES

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZETADIFF_CONVERGES = prove
 (`!n s. &0 < Re(s)
         ==> ((\m. Cx(&1) / Cx(&m) cpow s - Cx(&1) / Cx(&(m + 1)) cpow s)
              sums Cx(&1) / Cx(&n) cpow s) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. Cx(&1) / Cx(&m) cpow s`; `n:num`] SERIES_DIFFS) THEN
  REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\n. lift(&1 / exp (Re s * log (&n)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 VECTOR_SUB_REFL; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &1 / (Re s * log(&n))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_EXP; real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < x /\ (&0 <= x ==> &1 + u <= v) ==> &0 < x /\ u <= v`) THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= n ==> 1 < n`];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `exp(inv(Re s * e))` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 2` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN
  SUBGOAL_THEN `&0 < log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `N + 2 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL;
               REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n` THEN ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 2 <= n ==> N <= n`] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EXP_LOG THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
The theorem states that for all natural numbers $n$ and complex numbers $s$ with $\text{Re}(s) > 0$, the series:

$$\sum_{m=n}^{\infty} \left(\frac{1}{m^s} - \frac{1}{(m+1)^s}\right) = \frac{1}{n^s}$$

Here, $m^s$ is interpreted as complex exponentiation (denoted as `cpow` in HOL Light), and the summation starts from index $n$ and continues to infinity.

### Informal proof
The proof follows these main steps:

* First, we apply `SERIES_DIFFS` to recognize this as a telescoping series. This theorem states that if we have differences of consecutive terms of a sequence, the sum equals the first term if the sequence tends to zero.

* We then need to prove that $\lim_{m \to \infty} \frac{1}{m^s} = 0$ when $\text{Re}(s) > 0$.

* We transform the limit by showing that $\|\frac{1}{m^s}\| = \frac{1}{m^{\text{Re}(s)}}$ for sufficiently large $m$.

* Using comparison with the sequence $\frac{1}{\text{Re}(s) \cdot \log(m)}$, we establish that:
  - For $m \geq 2$, we have $\frac{1}{m^{\text{Re}(s)}} \leq \frac{1}{\text{Re}(s) \cdot \log(m)}$
  - The sequence $\frac{1}{\text{Re}(s) \cdot \log(m)}$ converges to 0 as $m \to \infty$

* For the second part, given any $\varepsilon > 0$, we apply the Archimedean property to find an $N$ such that $N > e^{\frac{1}{\text{Re}(s) \cdot \varepsilon}}$.

* We then show that for all $n \geq N+2$, $\frac{1}{\text{Re}(s) \cdot \log(n)} < \varepsilon$, completing the proof that the original sequence converges to 0.

* Since the sequence $\frac{1}{m^s}$ converges to 0 as $m \to \infty$, the telescoping series sums to $\frac{1}{n^s}$.

### Mathematical insight
This theorem establishes a basic identity for the differences of consecutive terms in the Riemann zeta function. The result is essentially showing that a telescoping series involving complex powers converges to the expected value.

The identity is particularly useful for studying analytic properties of the Riemann zeta function and related functions. The condition $\text{Re}(s) > 0$ is important as it ensures the convergence of the series, linking to the domain where the Riemann zeta function is defined by direct summation.

The proof technique demonstrates how to handle convergence of series with complex exponents by reducing to real-valued estimates and using comparison tests.

### Dependencies
The proof relies on several key theorems:
- `SERIES_DIFFS`: Used to recognize the telescoping nature of the series
- `LIM_NULL_NORM`: For converting limit to zero to a limit of norms
- `LIM_TRANSFORM`: To work with an equivalent expression for the limit
- `LIM_EVENTUALLY`: To simplify the limit by considering behavior for sufficiently large indices
- `LIM_NULL_COMPARISON`: For applying comparison test with a simpler sequence
- `REAL_ARCH`: Application of the Archimedean property
- Various theorems about complex and real arithmetic, norms, and exponentiation

### Porting notes
When porting this theorem:
1. Ensure your system has a well-developed theory of complex exponentiation (`cpow` in HOL Light)
2. The proof makes heavy use of real and complex analysis results, particularly for limits and series
3. The telescoping series property (`SERIES_DIFFS`) is critical and should be established before attempting this proof
4. The handling of sequences and limits might differ across systems, so adjust the proof accordingly

---

## NEARZETA_CONVERGES_LEMMA

### Name of formal statement
NEARZETA_CONVERGES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_CONVERGES_LEMMA = prove
 (`!n s. &1 <= Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  REWRITE_TAC[summable] THEN MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\m. norm(s * (s - Cx(&1)) / Cx(&m) cpow (s + Cx(&1)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[IN_FROM; GE; LE_1; NEARZETA_BOUND_LEMMA;
                 REAL_ARITH `&1 <= s ==> &0 <= s + &1`]] THEN
  SUBGOAL_THEN
   `summable (from n)
     (\m. lift(((Cx (norm s) * Cx (norm (s - Cx (&1)))) *
                Cx (&1) / Cx (&m) cpow Cx (Re s + &1))$1))`
  MP_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPONENT THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC ZETA_CONVERGES_LEMMA THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM summable] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_FROM; o_THM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM RE_DEF] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; complex_div] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID; COMPLEX_NORM_INV] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LE_1] THEN
  REWRITE_TAC[GSYM CX_INV; RE_CX; RE_ADD]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$ where $\text{Re}(s) \geq 1$, the series
$$\sum_{m=n}^{\infty} \left[\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right]$$
converges to $\text{nearzeta}(n,s)$.

Here, we use the notation $m^s$ to represent complex exponentiation (denoted as `cpow` in HOL Light).

### Informal proof
The proof establishes that the series defining `nearzeta n s` is summable by comparing it with another series known to be summable.

- First, we rewrite the goal using the definition of `nearzeta` and the fact that a series sums to `infsum` if and only if it is summable.

- We use the comparison test for series convergence, comparing our series term-by-term with 
  $$\left\|\frac{s \cdot (s-1)}{m^{s+1}}\right\|$$
  
  We prove that each term in our series has a norm less than or equal to the corresponding term in this comparison series, using the previously proven `NEARZETA_BOUND_LEMMA`.

- Next, we show that the comparison series is summable by:
  1. Rewriting it in terms of the Riemann zeta function for $\text{Re}(s+1) \geq 2$
  2. Using `ZETA_CONVERGES_LEMMA` which states that $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges when $\text{Re}(s) \geq 2$
  3. Applying properties of complex multiplication and normalization

- Finally, we complete the proof by showing that our comparison series can be expressed as:
  $$\|s\| \cdot \|s-1\| \cdot \frac{1}{m^{\text{Re}(s)+1}}$$
  which converges by `ZETA_CONVERGES_LEMMA` since $\text{Re}(s)+1 \geq 2$ when $\text{Re}(s) \geq 1$.

### Mathematical insight
This lemma establishes the convergence of a modified zeta-like function (`nearzeta`) for complex arguments with real part at least 1. The standard Riemann zeta function converges only for $\text{Re}(s) > 1$, but by cleverly rewriting the terms through telescoping series techniques, this `nearzeta` function achieves convergence in the critical strip where $\text{Re}(s) \geq 1$.

The key insight is expressing each term as a difference between two components:
1. The term $\frac{s-1}{m^s}$ 
2. A telescoping term $\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}$

This construction is part of a strategy to extend analytic results about the zeta function to its critical strip, which is crucial for applications such as the study of prime number distribution.

### Dependencies
- **Theorems**:
  - `NEARZETA_BOUND_LEMMA`: Provides a bound on the norm of each term in the `nearzeta` series
  - `ZETA_CONVERGES_LEMMA`: Establishes convergence of the standard zeta series for $\text{Re}(s) \geq 2$

- **Definitions**:
  - `nearzeta`: Defines the function as an infinite sum with the specified terms

### Porting notes
When porting this theorem:
1. Ensure your target system has a proper definition of complex exponentiation analogous to HOL Light's `cpow`.
2. The handling of infinite series and `infsum` might differ between proof assistants.
3. Pay attention to how complex norms and real parts are defined in the target system.
4. The comparison test for series will likely be a standard library result, but its exact statement may vary.

---

## GENZETA_CONVERGES

### Name of formal statement
GENZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_CONVERGES = prove
 (`!n s. &1 < Re s
         ==> ((\m. Cx(&1) / Cx(&m) cpow s) sums genzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES_LEMMA o
        MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL [`n:num`; `s - Cx(&1)`] ZETADIFF_CONVERGES) THEN ANTS_TAC THENL
   [REWRITE_TAC[RE_SUB; RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[COMPLEX_RING `a + (b - a) = b:complex`; genzeta] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `&1 < Re s` THEN ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(s - Cx(&1))` o
     MATCH_MP SERIES_COMPLEX_LMUL) THEN
  SUBGOAL_THEN `~(s - Cx(&1) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV] THEN
  REWRITE_TAC[COMPLEX_MUL_AC; COMPLEX_ADD_AC]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$ with real part $\text{Re}(s) > 1$, the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges to $\text{genzeta}(n,s)$.

In mathematical notation:
$$\forall n \in \mathbb{N}, \forall s \in \mathbb{C} \text{ with } \text{Re}(s) > 1, \sum_{m=n}^{\infty} \frac{1}{m^s} = \text{genzeta}(n,s)$$

where the summation starts from index $m = n$.

### Informal proof
The proof demonstrates that the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges to $\text{genzeta}(n,s)$ for $\text{Re}(s) > 1$:

- First, we use that $\text{Re}(s) > 1$ implies $\text{Re}(s) \geq 1$, and apply `NEARZETA_CONVERGES_LEMMA` to show that the series
$$\sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$
converges to $\text{nearzeta}(n,s)$.

- Since $\text{Re}(s) > 1$, we know $\text{Re}(s-1) > 0$, so by `ZETADIFF_CONVERGES`, the series
$$\sum_{m=n}^{\infty} \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)$$
converges to $\frac{1}{n^{s-1}}$.

- We then use the theorem about adding two convergent series to combine these results. This gives that
$$\sum_{m=n}^{\infty} \frac{s-1}{m^s}$$
converges to $\text{nearzeta}(n,s) + \frac{1}{n^{s-1}}$.

- Since $s \neq 1$ (as $\text{Re}(s) > 1$), we can use the definition of $\text{genzeta}$:
$$\text{genzeta}(n,s) = \frac{\text{nearzeta}(n,s) + \frac{1}{n^{s-1}}}{s-1}$$

- Finally, by multiplying the series by $\frac{1}{s-1}$, we get that
$$\sum_{m=n}^{\infty} \frac{1}{m^s}$$
converges to $\text{genzeta}(n,s)$.

### Mathematical insight
This theorem establishes a fundamental convergence property of the generalized zeta function (genzeta). While the Riemann zeta function is traditionally defined for Re(s) > 1 as $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$, this theorem shows a similar convergence property for the generalized version starting from any natural number n.

The genzeta function is defined to handle both the case where s = 1 (using the complex derivative) and where s ≠ 1 (using the formula with nearzeta). This theorem focuses on the case where Re(s) > 1, establishing that in this region, genzeta(n,s) can be represented as the infinite sum of reciprocal powers.

This convergence property is essential for establishing analytical properties of the generalized zeta function and relates to important results in analytic number theory, particularly concerning the distribution of prime numbers.

### Dependencies
- **Definitions**
  - `genzeta`: Defines the generalized zeta function

- **Theorems**
  - `NEARZETA_CONVERGES_LEMMA`: Shows convergence properties of the nearzeta function
  - `ZETADIFF_CONVERGES`: Shows convergence of differences of reciprocal powers

### Porting notes
When porting this theorem, special attention should be paid to:
- The handling of complex powers in the target system
- The definition of series convergence and 'sums' relation
- How the target system represents sequences starting from an arbitrary index (the 'from n' construct in HOL Light)
- Ensure that the complex derivative at s=1 case in the genzeta definition is correctly implemented

---

## ZETA_CONVERGES

### Name of formal statement
ZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums zeta(s)) (from 1)`,
  REWRITE_TAC[zeta; GENZETA_CONVERGES]);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, the series $\sum_{n=1}^{\infty} \frac{1}{n^s}$ converges to $\zeta(s)$, where $\zeta$ is the Riemann zeta function.

More formally, for all complex numbers $s$ such that $1 < \text{Re}(s)$, the sequence of partial sums $(\sum_{n=1}^{m} \frac{1}{n^s})_{m=1}^{\infty}$ converges to $\zeta(s)$.

### Informal proof
The proof is straightforward and relies directly on the more general result `GENZETA_CONVERGES`. 

The Riemann zeta function $\zeta(s)$ is defined in terms of the generalized zeta function as $\zeta(s) = \text{genzeta}(1,s)$. The theorem `GENZETA_CONVERGES` states that for any integer $n$ and complex number $s$ with $\text{Re}(s) > 1$, the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges to $\text{genzeta}(n,s)$.

By applying this result with $n = 1$, we immediately obtain that $\sum_{m=1}^{\infty} \frac{1}{m^s}$ converges to $\text{genzeta}(1,s) = \zeta(s)$ whenever $\text{Re}(s) > 1$.

### Mathematical insight
This theorem establishes the classic representation of the Riemann zeta function as an infinite series, valid in the half-plane $\text{Re}(s) > 1$. The Riemann zeta function is a fundamental object in analytic number theory, connecting complex analysis to the distribution of prime numbers.

The condition $\text{Re}(s) > 1$ is necessary for the absolute convergence of the series. For values of $s$ with $\text{Re}(s) \leq 1$, the series diverges, but the zeta function can still be defined through analytic continuation.

This specific convergence result serves as a foundational building block for more advanced properties of the zeta function, including its functional equation, special values, and connections to prime numbers via the Euler product formula.

### Dependencies
- **Definitions**:
  - `zeta`: Defines the Riemann zeta function as a special case of the generalized zeta function
  
- **Theorems**:
  - `GENZETA_CONVERGES`: Proves that the generalized zeta function series converges when the real part of s is greater than 1

### Porting notes
When porting this theorem, note that different proof assistants may have different representations of complex numbers, summation, and convergence. The key aspects to match include:
1. The definition of the Riemann zeta function as an infinite series
2. The convergence condition $\text{Re}(s) > 1$
3. The relationship between the Riemann zeta function and the generalized zeta function

In systems with strong automation for convergence results, the proof might be even simpler than in HOL Light.

---

## COMPLEX_DERIVATIVE_ZETA_CONVERGES

### Name of formal statement
COMPLEX_DERIVATIVE_ZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. --clog(Cx(&n)) / Cx(&n) cpow s) sums
            complex_derivative zeta s) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n z. Cx(&1) / Cx(&n) cpow z`;
    `\n z. --clog(Cx(&n)) / Cx(&n) cpow z`;
    `{s | Re s > &1}`;
    `from 1`]
   SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX) THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; LE_1];
      ALL_TAC] THEN
    POP_ASSUM(K ALL_TAC) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(Re z - &1) / &2`;
      `\n. Cx(&1) / Cx(&n) cpow (Cx(&1 + (Re z - &1) / &2))`;
      `42`] THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_SUB_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `Cx(&1 + (Re z - &1) / &2)` ZETA_CONVERGES) THEN
      ANTS_TAC THENL [REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[summable];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_FROM; CPOW_REAL_REAL; REAL_OF_NUM_LT; RE_CX; REAL_CX;
                 LE_1; COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_CX; RE_CX;
                real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[REAL_ABS_EXP; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--(a * x) <= --(b * x) <=> b * x <= a * x`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MP_TAC(SPEC `z - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_gt] THEN
  MAP_EVERY X_GEN_TAC [`f:complex->complex`; `g:complex->complex`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `b /\ c /\ d ==> e <=> b /\ c ==> d ==> e`]
                HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT) THEN
  EXISTS_TAC `Re s - &1` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. Cx(&1) / Cx(&n) cpow z`; `from 1`] THEN
  SUBGOAL_THEN `&1 < Re z` (fun th -> ASM_SIMP_TAC[th; ZETA_CONVERGES]) THEN
  MP_TAC(SPEC `z - s:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC);;
```

### Informal statement
For all complex numbers $s$ with real part $\operatorname{Re}(s) > 1$, the series $\sum_{n=1}^{\infty} \frac{-\log(n)}{n^s}$ converges to the complex derivative of the Riemann zeta function at $s$, i.e.,
$$\sum_{n=1}^{\infty} \frac{-\log(n)}{n^s} = \zeta'(s)$$

### Informal proof
We show this by applying the theorem `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` to the series that defines the zeta function.

Let's apply `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` with:
- $f(n,z) = \frac{1}{n^z}$
- $f'(n,z) = \frac{-\log(n)}{n^z}$ (the derivative with respect to $z$)
- The domain $S = \{s \mid \operatorname{Re}(s) > 1\}$
- The index set $k = \{n \in \mathbb{N} \mid n \geq 1\}$

First, we need to verify the hypotheses:

1. $S$ is open, which is true as it's a half-plane.

2. For each $n \geq 1$ and $z$ with $\operatorname{Re}(z) > 1$, $f(n,z)$ is complex differentiable with derivative $f'(n,z)$. 
   This is verified using complex differentiation rules, noting that $n^z \neq 0$ for $n \geq 1$.

3. For each $z$ with $\operatorname{Re}(z) > 1$, we need to find bounds for the functions.
   We choose:
   - $d = \frac{\operatorname{Re}(z) - 1}{2} > 0$
   - $h(n) = \frac{1}{n^{1+d}}$
   
   We show that $h$ is summable by using `ZETA_CONVERGES` with the argument $1+d$.
   
   Then for $y$ in the ball $B(z,d)$, we need to show $|f(n,y)| \leq |h(n)|$. This follows because:
   - If $y$ is in $B(z,d)$, then $\operatorname{Re}(y) > \operatorname{Re}(z) - d = 1+d$
   - Therefore $|n^{-y}| = n^{-\operatorname{Re}(y)} < n^{-(1+d)} = |h(n)|$

The theorem now gives us functions $g$ and $g'$ such that:
1. $\sum_{n=1}^{\infty} f(n,s) = g(s)$
2. $\sum_{n=1}^{\infty} f'(n,s) = g'(s)$
3. $g$ is complex differentiable at $s$ with derivative $g'(s)$

From `ZETA_CONVERGES`, we know that $\sum_{n=1}^{\infty} \frac{1}{n^s} = \zeta(s)$, so $g = \zeta$.

Finally, by applying `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`, we conclude that $g'(s) = \zeta'(s)$, which means $\sum_{n=1}^{\infty} \frac{-\log(n)}{n^s} = \zeta'(s)$.

### Mathematical insight
This theorem gives an explicit series representation for the derivative of the Riemann zeta function in the region of absolute convergence ($\operatorname{Re}(s) > 1$). The result is obtained by differentiating the defining series for $\zeta(s)$ term by term, which yields $\zeta'(s) = -\sum_{n=1}^{\infty} \frac{\log(n)}{n^s}$. This is possible because the conditions for term-by-term differentiation are satisfied in this region.

The result is important for studying the analytic properties of the zeta function, including its functional equation and zeros. It serves as a stepping stone for extending the definition of $\zeta(s)$ to a larger domain through analytic continuation.

### Dependencies
- **Theorems**:
  - `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`: Provides conditions under which term-by-term differentiation of a complex series is valid
  - `ZETA_CONVERGES`: States that the series $\sum_{n=1}^{\infty} \frac{1}{n^s}$ converges to $\zeta(s)$ for $\operatorname{Re}(s) > 1$
- **Definitions**:
  - `zeta`: Defines the Riemann zeta function as `zeta s = genzeta 1 s`

### Porting notes
When porting this theorem:
1. Ensure that your system has a suitable definition of complex power (`cpow` in HOL Light), particularly for complex exponents.
2. The proof relies on term-by-term differentiation of complex series, so make sure your system has the appropriate theorems for this.
3. Be careful with the handling of complex logarithms (`clog` in HOL Light) and their properties.
4. Note that the Riemann zeta function might be defined differently in other systems, so verify the exact definition before porting.

---

## HOLOMORPHIC_NEARZETA_LEMMA

### Name of formal statement
HOLOMORPHIC_NEARZETA_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA_LEMMA = prove
 (`!n. 1 <= n
       ==> ?g g'. !s. s IN {s | Re(s) > &0}
                      ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                           (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                            Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
                           sums g s) (from n) /\
                           ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                                 Cx(&m) cpow s -
                                 (clog(Cx(&(m + 1))) /
                                  Cx(&(m + 1)) cpow (s - Cx(&1)) -
                                  clog(Cx(&m)) /
                                  Cx(&m) cpow (s - Cx(&1))))
                            sums g' s) (from n) /\
                       (g has_complex_derivative g' s) (at s)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `s:complex`] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt; from] THEN STRIP_TAC THEN
    COMPLEX_DIFF_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
  DISCH_TAC THEN EXISTS_TAC `min (Re s / &2) (&1)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; REAL_HALF] THEN
  EXISTS_TAC `\n. Cx(norm(s) + &2) pow 2 /
                  Cx(&n) cpow Cx((Re s / &2 + &1))` THEN
  EXISTS_TAC `1` THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MP_TAC(SPECL [`n:num`; `Cx(Re s / &2 + &1)`] GENZETA_CONVERGES) THEN
    REWRITE_TAC[RE_CX] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN MESON_TAC[summable];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN REWRITE_TAC[from; IN_ELIM_THM] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
                 GSYM CX_DIV; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND_LEMMA o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(w) = &1 /\ norm(z) <= x + &1
      ==> norm z <= abs(x + &2) /\ norm(z - w) <=  abs(x + &2)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
               REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_ADD; RE_CX] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $n \geq 1$, there exist functions $g$ and $g'$ such that for all complex numbers $s$ with $\text{Re}(s) > 0$, the following holds:

1. The series $\sum_{m=n}^{\infty} \left[ \frac{s-1}{m^s} - \left( \frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}} \right) \right]$ converges to $g(s)$.

2. The series $\sum_{m=n}^{\infty} \left[ \frac{1-(s-1)\log(m)}{m^s} - \left( \frac{\log(m+1)}{(m+1)^{s-1}} - \frac{\log(m)}{m^{s-1}} \right) \right]$ converges to $g'(s)$.

3. The function $g$ is complex-differentiable at $s$ with derivative $g'(s)$, i.e., $(g \text{ has\_complex\_derivative } g'(s)) \text{ (at } s)$.

### Informal proof
The proof uses the theorem `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` which allows us to establish convergence of a series and its term-by-term derivative simultaneously, provided certain bounds hold. We need to verify the necessary conditions for this theorem:

1. First, we show that for every $m \geq n$ and every $s$ with $\text{Re}(s) > 0$, the term function is complex-differentiable at $s$. This is done using complex differentiation rules and algebraic manipulation.

2. Next, for any $s$ with $\text{Re}(s) > 0$, we need to find appropriate bounds. We set:
   - $d = \min(\frac{\text{Re}(s)}{2}, 1)$, which is positive since $\text{Re}(s) > 0$.
   - We choose the bounding sequence $h(n) = \frac{(|s|+2)^2}{n^{\text{Re}(s)/2+1}}$
   - We show that this sequence is summable by relating it to the convergent generalized zeta function (using `GENZETA_CONVERGES`).

3. For any $m \geq n$ and any $z$ in the ball of radius $d$ around $s$, we need to show that the norm of our term is bounded by $h(m)$. This is demonstrated using:
   - The `NEARZETA_BOUND_LEMMA` to establish a key inequality
   - Complex norm properties and careful analysis to show that our bound holds for all complex numbers $z$ close enough to $s$.

The result follows from `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`, establishing that $g$ is holomorphic on the right half-plane with derivative $g'$.

### Mathematical insight
This lemma is a key step in extending the domain of the Riemann zeta function. It establishes the holomorphicity of a related function (sometimes called "near zeta") on the half-plane $\text{Re}(s) > 0$, which is larger than the half-plane $\text{Re}(s) > 1$ where the standard zeta series $\sum_{n=1}^{\infty} \frac{1}{n^s}$ converges.

The technique used here is an example of analytic continuation. The expression 
$\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)$ 
is carefully constructed to have better convergence properties than the original zeta terms.

This approach allows us to extend the Riemann zeta function to a larger domain while preserving its analytic properties, which is crucial for studying its zeros and connections to prime number theory.

### Dependencies
- Theorems:
  - `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`: Provides conditions for when a series and its term-by-term derivative both converge and the resulting function is holomorphic.
  - `NEARZETA_BOUND_LEMMA`: Provides a crucial inequality for bounding the terms in our series.
  - `GENZETA_CONVERGES`: Establishes convergence of the generalized zeta function.

### Porting notes
When porting this theorem:
1. The proof requires a good library for complex analysis, especially for handling complex differentiation and series convergence.
2. The technique of finding a suitable bounding sequence for the terms is crucial and requires careful construction.
3. Be aware that the notation `cpow` in HOL Light represents complex exponentiation, which may have different syntax in other systems.
4. The proof relies heavily on algebraic manipulation of complex expressions, so automated simplification of complex expressions would be helpful.

---

## HOLOMORPHIC_NEARZETA_STRONG

### Name of formal statement
HOLOMORPHIC_NEARZETA_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA_STRONG = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
               Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums (nearzeta n s)) (from n) /\
              ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                    Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) /
                     Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) /
                     Cx(&m) cpow (s - Cx(&1))))
               sums (complex_derivative(nearzeta n) s)) (from n) /\
          ((nearzeta n) has_complex_derivative
           complex_derivative(nearzeta n) s) (at s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_LEMMA) THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:complex->complex`; `g':complex->complex`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [FORALL_AND_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < Re s
        ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
    ASM_MESON_TAC[summable];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 < Re z ==> nearzeta n z = g z` ASSUME_TAC THENL
   [ASM_MESON_TAC[SERIES_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!z. &0 < Re z ==> ((nearzeta n) has_complex_derivative g' z) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:complex->complex`; `Re z`] THEN
    ASM_SIMP_TAC[dist] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `w - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DERIVATIVE]);;
```

### Informal statement
For all natural numbers $n \geq 1$ and complex numbers $s$ with $\text{Re}(s) > 0$, the following statements hold:

1. The series $\sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$ converges to $\text{nearzeta}(n, s)$.

2. The series $\sum_{m=n}^{\infty} \left(\frac{1-(s-1)\log(m)}{m^s} - \left(\frac{\log(m+1)}{(m+1)^{s-1}} - \frac{\log(m)}{m^{s-1}}\right)\right)$ converges to the complex derivative $\frac{d}{ds}(\text{nearzeta}(n, s))$.

3. The function $\text{nearzeta}(n, \cdot)$ is complex differentiable at $s$ with derivative $\frac{d}{ds}(\text{nearzeta}(n, s))$.

### Informal proof
This theorem proves the convergence of the series defining the $\text{nearzeta}$ function, and establishes its holomorphicity by showing that its derivative exists and can be computed term-by-term.

The proof proceeds as follows:

- We begin by applying `HOLOMORPHIC_NEARZETA_LEMMA`, which guarantees the existence of functions $g$ and $g'$ such that:
  - For any $s$ with $\text{Re}(s) > 0$, the series defining $g$ and $g'$ converge
  - $g$ is complex differentiable at $s$ with derivative $g'$
  
- We then show that for all $s$ with $\text{Re}(s) > 0$, the series defining $\text{nearzeta}(n, s)$ converges by using the definition of $\text{nearzeta}$ and the fact that the corresponding series for $g$ is summable.

- We establish that $\text{nearzeta}(n, z) = g(z)$ for all $z$ with $\text{Re}(z) > 0$ using the uniqueness of series limits.

- Next, we prove that $\text{nearzeta}(n, \cdot)$ is complex differentiable at any $z$ with $\text{Re}(z) > 0$, with derivative $g'(z)$, by applying the principle of differentiability under transformation.

- Finally, we conclude that $g'$ must be the complex derivative of $\text{nearzeta}(n, \cdot)$, completing the proof.

### Mathematical insight
This theorem strengthens the understanding of the $\text{nearzeta}$ function, which is a variant of the Riemann zeta function with behavior controlled near a specified point $n$. The result establishes:

1. The precise definition of $\text{nearzeta}$ as an infinite series
2. The convergence of this series in the right half-plane
3. The holomorphicity (complex differentiability) of $\text{nearzeta}$ 
4. An explicit formula for its derivative

The $\text{nearzeta}$ function plays a role in studying the analytic properties of the Riemann zeta function. This theorem is particularly valuable because it provides the analytical foundation needed to work with $\text{nearzeta}$ in complex analysis, especially when studying properties near the critical strip.

The convergence and differentiability properties established here allow for further analysis of the function's behavior in the complex plane, which is essential for applications in number theory and the study of the Riemann zeta function.

### Dependencies
- **Theorems**:
  - `HOLOMORPHIC_NEARZETA_LEMMA`: Provides the existence of functions with properties needed for this theorem
  - (Implicitly) `SERIES_UNIQUE`: Used to establish uniqueness of series limits
  - (Implicitly) `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT`: Used for transformation of complex differentiability
  - (Implicitly) `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`: Relates complex derivative to differentiability

- **Definitions**:
  - `nearzeta`: Defined as the infinite sum of terms $\frac{s-1}{m^s} - (\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}})$ from $n$ to infinity

### Porting notes
When implementing this in other proof assistants:
1. Ensure that the `nearzeta` function is properly defined using an appropriate infinite sum construct
2. The complex differentiability might need to be handled differently depending on how complex analysis is formalized in the target system
3. Be careful with the treatment of bounds in the summation - note that the sum starts from index $n$ (rather than 0 or 1)
4. Pay attention to the representation of complex numbers and operations like complex power, which might differ between systems

---

## NEARZETA_CONVERGES

### Name of formal statement
NEARZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_CONVERGES = prove
 (`!n s. &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  MATCH_MP_TAC SUMMABLE_EQ_COFINITE THEN EXISTS_TAC `from(n + 1)` THEN
  SUBGOAL_THEN
   `from(n + 1) DIFF from n UNION from n DIFF from(n + 1) = {n}`
   (fun th -> REWRITE_TAC[th; FINITE_INSERT; FINITE_RULES])
  THENL
   [SIMP_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_SING] THEN ARITH_TAC;
    MP_TAC(SPECL [`n + 1`; `s:complex`] HOLOMORPHIC_NEARZETA_STRONG) THEN
    ASM_REWRITE_TAC[summable] THEN ANTS_TAC THENL [ARITH_TAC; MESON_TAC[]]]);;
```

### Informal statement
For any natural number $n$ and complex number $s$ with positive real part ($\Re(s) > 0$), the series
$$\sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$
converges to $\text{nearzeta}(n, s)$.

Here, $\text{nearzeta}(n, s)$ is defined as the infinite sum of this same series.

### Informal proof
The proof proceeds as follows:

- We begin by unwrapping the definition of `nearzeta` and using the theorem `SUMS_INFSUM`, which states that if a series is summable, then it sums to its infimum.

- To establish summability, we apply `SUMMABLE_EQ_COFINITE`, which states that if two series differ on only finitely many terms, then one is summable if and only if the other is.

- We choose `from(n+1)` as our cofinite set to compare with `from n`, and prove that their symmetric difference is exactly the singleton set `{n}`. This is done by showing:
  $$(\text{from}(n+1) \setminus \text{from}(n)) \cup (\text{from}(n) \setminus \text{from}(n+1)) = \{n\}$$

- Finally, we apply the theorem `HOLOMORPHIC_NEARZETA_STRONG` with parameters `n+1` and `s`. Since `n+1 ≥ 1` (which follows from arithmetic) and we already know that $\Re(s) > 0$ (from our assumptions), we can extract the needed summability property from this theorem.

### Mathematical insight
The `nearzeta` function is designed to compute a regularized version of the Riemann zeta function, focusing specifically on the behavior near $s=1$ where the standard zeta function has a simple pole.

The series representation used here employs a transformation technique that enhances convergence and enables analytic continuation. The term being subtracted:
$$\left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)$$
creates a telescoping effect that improves the convergence properties.

This theorem establishes that the `nearzeta` function is well-defined for all $s$ with positive real part, which is a prerequisite for further analysis of its analytic properties, including holomorphicity and its relationship to the standard zeta function.

### Dependencies
- Definitions:
  - `nearzeta`: Defines the near-zeta function as an infinite sum
  
- Theorems:
  - `HOLOMORPHIC_NEARZETA_STRONG`: Provides the strong holomorphic properties of the near-zeta function
  - `SUMS_INFSUM`: Relates infinite sums to the `infsum` operator
  - `SUMMABLE_EQ_COFINITE`: Allows transfer of summability between series differing on finite sets

### Porting notes
When implementing this in another proof assistant:
- Ensure that the concept of complex power (`cpow`) and complex logarithm (`clog`) are properly defined with the same branch cuts as in HOL Light
- The theorem relies on set operations and the concept of "from n" (the set of natural numbers greater than or equal to n), which may need explicit construction in other systems
- Pay attention to how infinite sums and convergence are formalized in the target system, as the proof relies on these concepts

---

## SUMS_COMPLEX_DERIVATIVE_NEARZETA

### SUMS_COMPLEX_DERIVATIVE_NEARZETA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUMS_COMPLEX_DERIVATIVE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) / Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) / Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) / Cx(&m) cpow (s - Cx(&1)))) sums
            (complex_derivative (nearzeta n) s)) (from n)`,
  SIMP_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$, if $1 \leq n$ and $\text{Re}(s) > 0$, then the series
$$\sum_{m=n}^{\infty} \left[ \frac{1 - (s-1)\log(m)}{m^s} - \left( \frac{\log(m+1)}{(m+1)^{s-1}} - \frac{\log(m)}{m^{s-1}} \right) \right]$$
converges to the complex derivative of the function $\text{nearzeta}(n, s)$, denoted as $\frac{d}{ds}\text{nearzeta}(n, s)$.

### Informal proof
This theorem follows directly from the stronger result `HOLOMORPHIC_NEARZETA_STRONG`, which states three properties about the `nearzeta` function. The second part of that theorem exactly matches our claim about the series representation of the complex derivative of `nearzeta`. The proof simply applies simplification using this stronger theorem.

### Mathematical insight
This theorem gives an explicit series representation for the complex derivative of the `nearzeta` function with respect to its second argument. The `nearzeta` function is related to the Riemann zeta function, and understanding its derivative is important for analytic number theory.

The series representation allows for numerical approximation and analytic study of the derivative's behavior. This is particularly valuable for investigating the properties of zeta-like functions in complex analysis and number theory.

The structure of this series involves logarithmic terms that arise from differentiating power functions in the definition of `nearzeta`.

### Dependencies
- Theorems:
  - `HOLOMORPHIC_NEARZETA_STRONG`: A stronger theorem that establishes three properties of the `nearzeta` function, including the series representation of its derivative.

- Definitions:
  - `nearzeta n s = infsum (from n) (λm. (s - Cx(&1)) / Cx(&m) cpow s - (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) - Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))`: The definition of the near-zeta function.

### Porting notes
When porting this theorem, note that it relies on complex analysis fundamentals, particularly around series convergence, complex differentiation, and logarithmic functions. The proof is straightforward, but the porting system must have comparable theorems about holomorphic functions and series representations of derivatives.

---

## HOLOMORPHIC_NEARZETA

### HOLOMORPHIC_NEARZETA
- HOLOMORPHIC_NEARZETA

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HOLOMORPHIC_NEARZETA = prove
 (`!n. 1 <= n ==> (nearzeta n) holomorphic_on {s | Re(s) > &0}`,
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
  REWRITE_TAC[real_gt] THEN MESON_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;
```

### Informal statement
For all natural numbers $n$ such that $1 \leq n$, the function $\text{nearzeta}_n$ is holomorphic on the right half-plane $\{s \in \mathbb{C} : \text{Re}(s) > 0\}$.

Where $\text{nearzeta}_n(s)$ is defined as:
$$\text{nearzeta}_n(s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$

### Informal proof
The proof proceeds as follows:

1. We first simplify the goal by applying the theorem `HOLOMORPHIC_ON_OPEN`, which reduces the problem to showing that the function is holomorphic at each point in the open set.
   
2. We then apply `OPEN_HALFSPACE_RE_GT` to establish that $\{s \in \mathbb{C} : \text{Re}(s) > 0\}$ is indeed an open set.

3. After simplifying the set membership condition using `IN_ELIM_THM` and rewriting with `real_gt`, we've reduced the goal to proving that for each point $s$ with $\text{Re}(s) > 0$, the function $\text{nearzeta}_n$ is holomorphic at $s$.

4. Finally, we use the stronger theorem `HOLOMORPHIC_NEARZETA_STRONG` which establishes that for each point $s$ with $\text{Re}(s) > 0$, the function $\text{nearzeta}_n(s)$ can be expressed as a convergent series and has a complex derivative at $s$, which implies it is holomorphic at $s$.

### Mathematical insight
This theorem establishes the holomorphicity of the $\text{nearzeta}_n$ function on the right half-plane. The $\text{nearzeta}_n$ function is related to the Riemann zeta function, but modified to ensure convergence in the critical strip. The holomorphicity is important for analytical properties like complex differentiation and contour integration.

The function $\text{nearzeta}_n$ serves as an analytical continuation of a modified zeta function. The holomorphicity property proven here is fundamental for further analysis of its behavior, including location of zeros and its role in number theory.

### Dependencies
- Theorems:
  - `HOLOMORPHIC_NEARZETA_STRONG`: Establishes the series representation and complex differentiability of nearzeta
  - `HOLOMORPHIC_ON_OPEN`: Relates holomorphicity on an open set to point-wise holomorphicity
  - `OPEN_HALFSPACE_RE_GT`: States that the right half-plane is an open set

- Definitions:
  - `nearzeta`: The definition of the nearzeta function as an infinite sum

### Porting notes
When porting this theorem, ensure that:
1. The complex analysis library in the target system has appropriate concepts for holomorphicity and complex differentiation
2. The target system can handle infinite sums with the appropriate convergence criteria
3. The notion of open sets in the complex plane is properly established
4. Series manipulations and convergence theorems needed for `HOLOMORPHIC_NEARZETA_STRONG` are available

---

## COMPLEX_DIFFERENTIABLE_NEARZETA

### Name of formal statement
COMPLEX_DIFFERENTIABLE_NEARZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DIFFERENTIABLE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s ==> (nearzeta n) complex_differentiable (at s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_STRONG) THEN
  MESON_TAC[complex_differentiable]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$, if $1 \leq n$ and $\operatorname{Re}(s) > 0$, then the function $\operatorname{nearzeta}_n$ is complex differentiable at $s$.

Here $\operatorname{nearzeta}_n(s)$ is defined as:
$$\operatorname{nearzeta}_n(s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$

### Informal proof
The proof follows from the stronger result `HOLOMORPHIC_NEARZETA_STRONG` which establishes that:
1. The series defining $\operatorname{nearzeta}_n(s)$ converges for $\operatorname{Re}(s) > 0$
2. A specific series converges to the complex derivative of $\operatorname{nearzeta}_n$ at $s$
3. $\operatorname{nearzeta}_n$ has a complex derivative at $s$ equal to $\operatorname{complex\_derivative}(\operatorname{nearzeta}_n)(s)$

From this stronger result, we immediately deduce that $\operatorname{nearzeta}_n$ is complex differentiable at $s$ by using the definition of complex differentiability.

### Mathematical insight
This theorem establishes an important analytical property of the $\operatorname{nearzeta}$ function, which is a variant of the Riemann zeta function. The complex differentiability of this function is crucial for understanding its behavior in the complex plane.

The $\operatorname{nearzeta}$ function is constructed to study properties near the Riemann zeta function, particularly in regions where the standard zeta function has analytical challenges. By confirming that this function is complex differentiable in the right half-plane, we establish that it is well-behaved analytically in this region.

This allows for further analysis using complex analysis techniques, which are essential for studying properties related to the Riemann hypothesis and other questions in analytic number theory.

### Dependencies
- Definitions:
  - `nearzeta`: Defines the near zeta function as an infinite sum
  
- Theorems:
  - `HOLOMORPHIC_NEARZETA_STRONG`: Provides a stronger result about the holomorphicity of the near zeta function, explicitly giving its derivative
  - `complex_differentiable`: Relates the existence of a complex derivative to complex differentiability

### Porting notes
When porting this result:
1. First implement the definition of the `nearzeta` function
2. Port the stronger theorem `HOLOMORPHIC_NEARZETA_STRONG` which requires machinery for complex power functions, logarithms, and series convergence
3. The main result is then a simple corollary, provided the system has a formalized connection between having a complex derivative and being complex differentiable

---

## NEARZETA_1

### Name of formal statement
NEARZETA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_1 = prove
 (`!n. 1 <= n ==> nearzeta n (Cx(&1)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; COMPLEX_SUB_REFL] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC `\n:num. (vec 0:complex)` THEN
  REWRITE_TAC[SERIES_0; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; IN_FROM; complex_div] THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[complex_pow] THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For any natural number $n$ where $n \geq 1$, we have:
$$\text{nearzeta}(n, 1) = 0$$

where $\text{nearzeta}$ is defined as:
$$\text{nearzeta}(n, s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$

### Informal proof
We need to prove that $\text{nearzeta}(n, 1) = 0$ for any $n \geq 1$.

First, we substitute $s = 1$ into the definition of $\text{nearzeta}$:
$$\text{nearzeta}(n, 1) = \sum_{m=n}^{\infty} \left(\frac{1-1}{m^1} - \left(\frac{1}{m^{1-1}} - \frac{1}{(m+1)^{1-1}}\right)\right)$$
$$= \sum_{m=n}^{\infty} \left(\frac{0}{m} - \left(\frac{1}{m^0} - \frac{1}{(m+1)^0}\right)\right)$$

Since $m^0 = (m+1)^0 = 1$ for any $m \geq n \geq 1$, and $\frac{0}{m} = 0$, we get:
$$= \sum_{m=n}^{\infty} \left(0 - (1 - 1)\right) = \sum_{m=n}^{\infty} 0 = 0$$

Therefore, $\text{nearzeta}(n, 1) = 0$.

### Mathematical insight
This theorem establishes a special case of the $\text{nearzeta}$ function when the complex parameter $s$ equals 1. The $\text{nearzeta}$ function appears to be related to the Riemann zeta function, likely representing a modified version or approximation of it.

When $s = 1$, the theorem shows that $\text{nearzeta}(n, 1)$ becomes zero for any starting index $n \geq 1$. This happens because the terms in the summation simplify to zero when $s = 1$.

This result is likely important in analytic number theory, particularly in studies related to zeta functions and their behavior at special values.

### Dependencies
- **Definitions**:
  - `nearzeta`: Defines the near-zeta function as an infinite sum with specific terms.

### Porting notes
When porting this theorem:
1. Ensure the target system has a suitable library for complex analysis and infinite sums.
2. The definition of `nearzeta` involves complex exponentiation (`cpow`), so the target system should have an equivalent operation.
3. Pay attention to the handling of complex numbers represented as `Cx(&n)` in HOL Light, which represents the complex number corresponding to the real number `n`.

---

## HOLOMORPHIC_ZETA

### Name of formal statement
HOLOMORPHIC_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOLOMORPHIC_ZETA = prove
 (`zeta holomorphic_on {s | Re(s) > &0 /\ ~(s = Cx(&1))}`,
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[zeta; genzeta] THEN
  MATCH_MP_TAC HOLOMORPHIC_TRANSFORM THEN
  EXISTS_TAC `\z. (nearzeta 1 z + Cx(&1) / Cx(&1) cpow (z - Cx(&1))) /
                  (z - Cx(&1))` THEN
  SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  SIMP_TAC[IN_ELIM_THM; COMPLEX_SUB_0; HOLOMORPHIC_ON_SUB;
           HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `{s | Re s > &0}` THEN
    SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; ETA_AX] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
    REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ]]);;
```

### Informal statement
The Riemann zeta function $\zeta$ is holomorphic on the set $\{s \in \mathbb{C} \mid \text{Re}(s) > 0 \land s \neq 1\}$.

### Informal proof
The proof shows that the Riemann zeta function is holomorphic on the specified domain by:

- First rewriting using the definition of `zeta` as `genzeta 1` and expanding the definition of `genzeta`
- Applying `HOLOMORPHIC_TRANSFORM` to rewrite the goal in terms of the equivalent expression:
  $\zeta(z) = \frac{\text{nearzeta}(1)(z) + \frac{1}{1^{z-1}}}{z-1}$
- Using the theorem for holomorphicity of division (`HOLOMORPHIC_ON_DIV`)
- Showing the denominator $(z-1)$ is holomorphic and non-zero on the domain
- Proving the numerator is holomorphic by:
  * Showing `nearzeta 1` is holomorphic on $\{s \mid \text{Re}(s) > 0\}$ using `HOLOMORPHIC_NEARZETA`
  * Proving $\frac{1}{1^{z-1}}$ is holomorphic by using complex differentiability

The proof exploits the fact that the zeta function is defined using `nearzeta` and `genzeta`, and uses their holomorphicity properties to establish the holomorphicity of the Riemann zeta function itself on the specified domain.

### Mathematical insight
This theorem establishes the holomorphicity of the Riemann zeta function in the half-plane $\text{Re}(s) > 0$ except at $s = 1$ where it has a simple pole. The zeta function is defined in HOL Light using a construction that relates it to `nearzeta` and `genzeta` functions, which provide a way to handle the singularity at $s = 1$.

The Riemann zeta function is a fundamental function in analytic number theory, with connections to the distribution of prime numbers through the Riemann hypothesis. This result confirms one of its basic analytical properties - that it's holomorphic everywhere in the half-plane $\text{Re}(s) > 0$ except at the pole at $s = 1$.

The construction of the zeta function via `nearzeta` and `genzeta` is designed to enable its analytic continuation beyond its original region of convergence of the Dirichlet series.

### Dependencies
#### Theorems
- `HOLOMORPHIC_NEARZETA`: States that the `nearzeta n` function is holomorphic on the set $\{s \mid \text{Re}(s) > 0\}$ for $n \geq 1$

#### Definitions
- `nearzeta`: Defined as an infinite sum that helps construct the zeta function
- `genzeta`: Defined in terms of `nearzeta` and handles the special case at $s = 1$
- `zeta`: Defined as `genzeta 1`

#### Other HOL Light theorems used
- `HOLOMORPHIC_TRANSFORM`
- `HOLOMORPHIC_ON_DIV`
- `HOLOMORPHIC_ON_ADD`
- `HOLOMORPHIC_ON_SUBSET`

### Porting notes
When porting this theorem:
1. Ensure you have appropriate definitions for the complex zeta function that match HOL Light's construction using `nearzeta` and `genzeta`
2. Pay attention to how the singularity at $s = 1$ is handled in your system
3. The proof relies on theorems about holomorphicity of functions constructed from basic operations (addition, division, etc.), which should be available in most proof assistants, but the specific form might differ
4. If your system has a built-in zeta function, you may need to prove equivalence to this construction

---

## COMPLEX_DIFFERENTIABLE_AT_ZETA

### Name of formal statement
COMPLEX_DIFFERENTIABLE_AT_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DIFFERENTIABLE_AT_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> zeta complex_differentiable at s`,
  MP_TAC HOLOMORPHIC_ZETA THEN
  REWRITE_TAC[SET_RULE `{s | P s /\ ~(s = a)} = {s | P s} DELETE a`] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DELETE; OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[complex_differentiable; IN_ELIM_THM; IN_DELETE; real_gt]);;
```

### Informal statement
For any complex number $s$ such that $\operatorname{Re}(s) > 0$ and $s \neq 1$, the Riemann zeta function $\zeta$ is complex differentiable at $s$.

### Informal proof
This theorem directly follows from the holomorphicity of the Riemann zeta function.

- We start with the theorem `HOLOMORPHIC_ZETA` which states that $\zeta$ is holomorphic on the set $\{s \mid \operatorname{Re}(s) > 0 \land s \neq 1\}$.
- We first rewrite this set as $\{s \mid \operatorname{Re}(s) > 0\} \setminus \{1\}$ using set theory.
- We know that a function is holomorphic on an open set if and only if it is complex differentiable at each point of that set.
- We then apply the theorem that states the set $\{s \mid \operatorname{Re}(s) > 0\}$ is open and that removing a point from an open set results in an open set.
- Finally, we simplify the conditions and conclude that the zeta function is complex differentiable at any point $s$ with $\operatorname{Re}(s) > 0$ and $s \neq 1$.

### Mathematical insight
This theorem establishes the complex differentiability of the Riemann zeta function at each point in its domain of holomorphicity. Complex differentiability is a key property in complex analysis, being much stronger than real differentiability - it implies that the function is analytic and can be represented by a power series.

The Riemann zeta function has a simple pole at $s = 1$, which is why this point is excluded from the domain. The result is important because it confirms that $\zeta(s)$ behaves well analytically in the half-plane $\operatorname{Re}(s) > 0$ except at the point $s = 1$.

### Dependencies
- Theorems:
  - `HOLOMORPHIC_ZETA`: The Riemann zeta function is holomorphic on $\{s \mid \operatorname{Re}(s) > 0 \land s \neq 1\}$
  - `HOLOMORPHIC_ON_OPEN`: A function is holomorphic on an open set if and only if it is complex differentiable at each point of that set
  - `OPEN_DELETE`: Removing a point from an open set results in an open set
  - `OPEN_HALFSPACE_RE_GT`: The half-plane $\{s \mid \operatorname{Re}(s) > 0\}$ is an open set
  - Various set theory and rewriting rules

- Definitions:
  - `zeta`: The Riemann zeta function defined as `zeta s = genzeta 1 s`

### Porting notes
When porting this theorem to other systems, ensure that:
1. The definition of complex differentiability matches
2. The Riemann zeta function is properly defined with its domain restrictions
3. The connection between holomorphicity and complex differentiability is established
4. Basic topological theorems about openness of half-planes and deleted sets are available

---

## SERIES_DIVISORS_LEMMA

### Name of formal statement
SERIES_DIVISORS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SERIES_DIVISORS_LEMMA = prove
 (`!x p l k.
      ((\n. x(p * n)) sums l) k
      ==> ~(p = 0) /\
          (!n. (p * n) IN k <=> n IN k)
          ==> (x sums l) {n | n IN k /\ p divides n}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `p * N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV p`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (rand o rand) VSUM_IMAGE (lhand w))) THEN
  ASM_SIMP_TAC[FINITE_INTER_NUMSEG; EQ_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_NUMSEG] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; divides; LE_0] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any function $x$, nonzero integer $p$, real number $l$, and set $k$, if the series $\sum_{n \in k} x(p \cdot n)$ converges to $l$, and if $p \neq 0$ and the membership condition $p \cdot n \in k \iff n \in k$ holds for all $n$, then the series $\sum_{n \in k \text{ and } p \text{ divides } n} x(n)$ also converges to $l$.

### Informal proof
We need to show that the series $\sum_{n \in k \text{ and } p \text{ divides } n} x(n)$ converges to $l$, given that $\sum_{n \in k} x(p \cdot n)$ converges to $l$.

* First, we use the definition of series convergence: for any $\varepsilon > 0$, there exists some $N$ such that for all $n \geq N$, the partial sum approximation is within $\varepsilon$ of $l$.

* Given $\varepsilon > 0$, we know there exists an $N$ such that for all $n \geq N$:
  $$\left|\sum_{i \in k \cap [1,n]} x(p \cdot i) - l\right| < \varepsilon$$

* We choose $p \cdot N$ as our threshold for the target series and consider any $n \geq p \cdot N$.

* For the series $\sum_{n \in k \text{ and } p \text{ divides } n} x(n)$, we examine the partial sum up to $n$:
  $$\sum_{i \in k \cap [1,n] \cap \{j | p \text{ divides } j\}} x(i)$$

* This sum can be rewritten as:
  $$\sum_{i \in k \cap [1,n/p]} x(p \cdot i)$$
  using the substitution $i = p \cdot j$ where $j \in [1,n/p]$. This is valid because:
  1. The condition $p \cdot j \in k \iff j \in k$ is given
  2. The integer division $n \text{ DIV } p$ equals $\lfloor n/p \rfloor$

* Since $n \geq p \cdot N$, we have $n/p \geq N$, and therefore:
  $$\left|\sum_{i \in k \cap [1,n/p]} x(p \cdot i) - l\right| < \varepsilon$$

* This proves that the series $\sum_{n \in k \text{ and } p \text{ divides } n} x(n)$ converges to $l$.

### Mathematical insight
This lemma is a key component in proving the Euler product formula for the Riemann zeta function and similar series. It establishes a relationship between a series summed over all divisible-by-p terms and a series where the index is multiplied by p. 

The lemma shows that if we have convergence for the sequence with multiplied indices, we also have convergence for the original sequence when restricted to multiples of p. This is particularly useful in number theory for manipulating Dirichlet series and establishing connections between sums over integers and sums over primes.

The proof uses a clever reindexing technique that allows us to relate partial sums of different series, which is a common approach in analytic number theory.

### Dependencies
No explicit dependencies were provided in the input.

### Porting notes
When implementing this in other proof assistants:
- Ensure proper handling of the division operation - it must be integer division
- The concept of "divides" may need to be defined explicitly depending on the system
- The `sums` operation represents series convergence and would need a corresponding definition
- The reindexing argument using `VSUM_IMAGE` is a key step that may require specific attention in other systems

---

## EULER_PRODUCT_LEMMA

### Name of formal statement
EULER_PRODUCT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_PRODUCT_LEMMA = prove
 (`!s ps. &1 < Re s /\ FINITE ps /\ (!p. p IN ps ==> prime p)
          ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums
               (cproduct ps (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s))
       {n | 1 <= n /\ !p. prime p /\ p divides n ==> ~(p IN ps)}`,
  let lemma = prove
   (`(x sums (k + l)) (s UNION t) /\ s INTER t = {}
     ==> (x sums k) s ==> (x sums l) t`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[sums] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN REWRITE_TAC[VECTOR_ADD_SUB] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ABS_TAC THEN ASM_SIMP_TAC[SET_RULE
     `s INTER t = {}
      ==> t INTER u = (((s UNION t) INTER u) DIFF (s INTER u))`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_DIFF THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG] THEN SET_TAC[]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ZETA_CONVERGES; COMPLEX_MUL_LID; NOT_IN_EMPTY; GSYM from] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `ps:num->bool`] THEN
  REWRITE_TAC[IN_INSERT; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(Cx(&p) cpow s)` o MATCH_MP
    SERIES_COMPLEX_LMUL) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `x * Cx(&1) * y = Cx(&1) * x * y`] THEN
  REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN REWRITE_TAC[GSYM complex_div] THEN
  ASM_SIMP_TAC[GSYM CPOW_MUL_REAL; REAL_CX; RE_CX; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_OF_NUM_MUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[]
   (ISPEC `\n. Cx(&1) / Cx(&n) cpow s` SERIES_DIVISORS_LEMMA))) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    ASM_REWRITE_TAC[MULT_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_PRIME_FACTOR; PRIME_1];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `a * x + (Cx(&1) - a) * x = x`] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN FIRST_X_ASSUM(fun th ->
    MP_TAC th THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC) THEN
  SET_TAC[]);;
```

### Informal statement
For any complex number $s$ with $\text{Re}(s) > 1$ and any finite set $ps$ of prime numbers, we have:

$$\sum_{n \in A} \frac{1}{n^s} = \left(\prod_{p \in ps} (1 - p^{-s})\right) \cdot \zeta(s)$$

where $A = \{n \in \mathbb{N} \mid n \geq 1 \text{ and for all primes } p \text{ that divide } n, p \notin ps\}$, and $\zeta(s)$ is the Riemann zeta function.

### Informal proof
The proof uses induction on the finite set of primes $ps$.

* **Base case**: When $ps = \emptyset$, the left side becomes $\sum_{n=1}^{\infty} \frac{1}{n^s}$ which is exactly $\zeta(s)$. The right side becomes $1 \cdot \zeta(s) = \zeta(s)$ because the empty product equals 1.

* **Induction step**: Assume the result holds for a finite set of primes $ps$. We need to show it holds for $ps \cup \{p\}$ where $p$ is a prime not in $ps$.

* We apply a lemma (`SERIES_DIVISORS_LEMMA`) which relates sums over multiples of a number to sums over the original domain.

* The key insight is that we can partition the numbers not divisible by any prime in $ps$ into two disjoint sets:
  - Those that are not divisible by $p$ either
  - Those that are divisible by $p$ but not by any prime in $ps$

* For the second set, we can factorize out the powers of $p$, which contributes a factor of $(1 - p^{-s})$ to the product.

* The proof uses complex analysis to handle the series, showing that:
  $$\sum_{n \in A'} \frac{1}{n^s} = \left(\prod_{p \in ps \cup \{p\}} (1 - p^{-s})\right) \cdot \zeta(s)$$
  
  where $A' = \{n \in \mathbb{N} \mid n \geq 1 \text{ and for all primes } p \text{ that divide } n, p \notin (ps \cup \{p\})\}$.

* This is accomplished by using properties of complex series, set manipulations, and the fact that each term in the Euler product represents removing all multiples of a specific prime from the series.

### Mathematical insight
This lemma is a partial formulation of Euler's product formula for the Riemann zeta function. The general formula states that:

$$\zeta(s) = \prod_{p \text{ prime}} \frac{1}{1 - p^{-s}}$$

for $\text{Re}(s) > 1$.

The lemma establishes that when considering only a finite set of primes $ps$, removing their contributions from the zeta function gives precisely the sum over numbers not divisible by any prime in $ps$. This step-by-step construction demonstrates the multiplicative structure underlying the zeta function and illustrates how the Euler product emerges naturally from the properties of prime numbers.

This result is central to analytic number theory, connecting multiplicative number theory with complex analysis. It reveals how the zeta function encodes information about the distribution of prime numbers and provides a foundation for the Prime Number Theorem.

### Dependencies
- Theorems:
  - `ZETA_CONVERGES`: Shows that the Riemann zeta function converges for $\text{Re}(s) > 1$ 
  - `SERIES_DIVISORS_LEMMA`: Relates sums over multiples of a number to sums over the original domain

- Definitions:
  - `zeta`: Defines the Riemann zeta function as `zeta s = genzeta 1 s`

### Porting notes
When porting this theorem:
1. Ensure your system has a proper definition of the Riemann zeta function and its convergence properties
2. The proof relies on manipulating complex series and products, so the target system should have good support for complex analysis
3. The set-theoretic manipulations might need a different approach in systems with different set theory foundations
4. The induction on finite sets should be available in the target system

---

## SUMMABLE_SUBZETA

### Name of formal statement
SUMMABLE_SUBZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_SUBZETA = prove
 (`!s t. &1 < Re s /\ ~(0 IN t)
         ==> summable t (\n. Cx (&1) / Cx (&n) cpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_SUBSET THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_FROM] THEN ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
  MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(&1) / Cx(&n) cpow (Cx(Re s))` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[summable] THEN EXISTS_TAC `zeta (Cx(Re s))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN ASM_REWRITE_TAC[RE_CX];
    SIMP_TAC[IN_FROM; LE_1; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             GSYM CX_DIV; REAL_LE_DIV; REAL_POS; REAL_EXP_POS_LE];
    EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0; IN_FROM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_0; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_LE_REFL; REAL_OF_NUM_LT; LE_1]]);;
```

### Informal statement
For all complex numbers $s$ and sets $t$ of natural numbers, if $\text{Re}(s) > 1$ and $0 \notin t$, then the series $\sum_{n \in t} \frac{1}{n^s}$ is summable.

### Informal proof
The goal is to show that for any set $t$ of positive integers (since $0 \notin t$), the series $\sum_{n \in t} \frac{1}{n^s}$ converges when $\text{Re}(s) > 1$.

The proof uses the following approach:
- We apply the fact that if a series is summable on a larger set, then it is summable on any subset.
- Since $t \subseteq \{1, 2, 3, ...\}$, we need to show that $\sum_{n=1}^{\infty} \frac{1}{n^s}$ is summable.
- We use a comparison test with the real series $\sum_{n=1}^{\infty} \frac{1}{n^{\text{Re}(s)}}$.

Step by step:
1. Apply `SUMMABLE_SUBSET` to reduce the problem to showing summability on the set $\{n \in \mathbb{N} : n \geq 1\}$.
2. Verify that $t$ is indeed a subset of $\{n \in \mathbb{N} : n \geq 1\}$, which follows from the assumptions.
3. Apply the complex series comparison test (`SERIES_COMPARISON_COMPLEX`) with the majorizing series $\sum_{n=1}^{\infty} \frac{1}{n^{\text{Re}(s)}}$.
4. Show that this majorizing series is summable, which follows from the fact that it equals $\zeta(\text{Re}(s))$, and $\zeta$ converges for real arguments greater than 1 (using `ZETA_CONVERGES`).
5. Verify the required inequality: $|\frac{1}{n^s}| \leq \frac{1}{n^{\text{Re}(s)}}$ for all $n \geq 1$, which is true because $|n^s| = n^{\text{Re}(s)}$ for $n > 0$.

### Mathematical insight
This theorem extends the convergence property of the Riemann zeta function to arbitrary subsets of positive integers. The Riemann zeta function $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$ is known to converge absolutely when $\text{Re}(s) > 1$.

The key insight is that any subseries of an absolutely convergent series remains summable. This allows us to conclude that not just the full zeta function, but any "partial zeta function" summing over a subset of positive integers will also converge in the half-plane $\text{Re}(s) > 1$.

This result is useful for analyzing various Dirichlet series and related functions in analytic number theory, particularly when working with subseries of the zeta function.

### Dependencies
- Theorems:
  - `ZETA_CONVERGES`: Shows that $\sum_{n=1}^{\infty} \frac{1}{n^s}$ converges to $\zeta(s)$ when $\text{Re}(s) > 1$
  - `SUMMABLE_SUBSET`: If a series is summable on a set $A$, it's summable on any subset of $A$
  - `SERIES_COMPARISON_COMPLEX`: Comparison test for complex series

- Definitions:
  - `zeta`: The Riemann zeta function, defined as `zeta s = genzeta 1 s`

### Porting notes
When implementing this theorem in other systems:
1. Ensure that the complex analysis library includes a proper definition of the Riemann zeta function.
2. The proof relies on comparison tests for series, which should be available in most systems with complex analysis libraries.
3. Pay attention to how sets of naturals are represented in the target system, as this might differ from HOL Light's implementation.

---

## EULER_PRODUCT_MULTIPLY

### EULER_PRODUCT_MULTIPLY
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EULER_PRODUCT_MULTIPLY = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)
            --> Cx(&1)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
    `\n. infsum {m | 1 <= m /\ !p. prime p /\ p divides m
                                   ==> ~(p IN {p | prime p /\ p <= n})}
                (\n. Cx (&1) / Cx (&n) cpow s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC EULER_PRODUCT_LEMMA THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..n` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; LE_0; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l. ((\n. Cx (&1) / Cx (&n) cpow Cx(Re s)) sums l) (from 1)`
  MP_TAC THENL
   [MP_TAC(SPEC `Cx(Re s)` ZETA_CONVERGES) THEN
    ASM_SIMP_TAC[RE_CX] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SERIES_CAUCHY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF; GE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`s:complex`;
                 `{m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)}`]
                SUMMABLE_SUBZETA) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; ARITH] THEN
  REWRITE_TAC[GSYM SUMS_INFSUM] THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (MP_TAC o SPEC `N1 + N2 + 1`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN SIMP_TAC[NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `dist(x,z) < e / &2 /\ dist(y,z) <= dist(x,y) + dist(x,z)
    ==> dist(x,y) < e / &2 ==> dist(y,z) < e`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2 + 1`) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  REWRITE_TAC[dist] THEN SUBGOAL_THEN
   `vsum
     ({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
      (0..N1 + N2 + 1))
     (\n. Cx (&1) / Cx (&n) cpow s) - Cx(&1) =
    vsum
     (({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
       (0..N1 + N2 + 1)) DELETE 1)
     (\n. Cx (&1) / Cx (&n) cpow s)`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_DELETE_CASES; FINITE_INTER_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_ONE; IN_INTER] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    REWRITE_TAC[MESON[] `(!x. P x /\ x = 1 ==> Q x) <=> P 1 ==> Q 1`] THEN
    REWRITE_TAC[PRIME_1; IN_NUMSEG; ARITH; ARITH_RULE `1 <= a + b + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_NORM_VSUM_BOUND_SUBSET THEN
  REWRITE_TAC[FINITE_INTER_NUMSEG] THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_DELETE; IN_INTER; IN_ELIM_THM; IN_NUMSEG; IN_FROM] THEN
    ASM_MESON_TAC[PRIME_FACTOR; DIVIDES_LE; NUM_REDUCE_CONV `1 <= 0`;
                  LT_IMP_LE; LE_TRANS];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_INTER; IN_FROM] THEN STRIP_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_NORM_INV] THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
               NORM_CPOW_REAL] THEN
  SIMP_TAC[REAL_INV; REAL_CX; GSYM CX_INV; RE_CX; REAL_LE_REFL]);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, we have:

$$\lim_{n \to \infty} \left(\prod_{p \leq n, p \text{ prime}} (1 - p^{-s}) \cdot \zeta(s)\right) = 1$$

where $\zeta(s)$ is the Riemann zeta function.

### Informal proof
This theorem establishes Euler's product formula for the Riemann zeta function. The proof proceeds as follows:

- We begin by using `LIM_TRANSFORM_EVENTUALLY` to show that the sequence we're studying converges to the same limit as 
  $$\sum_{m \geq 1: \forall p \text{ prime}, p|m \Rightarrow p \not\in \{p : \text{prime}(p) \land p \leq n\}} \frac{1}{m^s}$$

- For each $n$, we use `EULER_PRODUCT_LEMMA` to establish that this sum equals the product in our theorem statement. 
  This lemma shows that for a finite set of primes, the product of $(1-p^{-s})$ times $\zeta(s)$ equals the sum of $m^{-s}$ over all $m$ not divisible by any prime in that set.

- We then need to show this sum approaches 1 as $n$ grows. To do this:
  * We use the fact that the zeta function converges (via `ZETA_CONVERGES`), which means the sum $\sum_{m=1}^{\infty} m^{-s}$ (with $\text{Re}(s) > 1$) is convergent.
  * We apply the Cauchy criterion for convergence, choosing an $N$ such that for all $n \geq N$, the tail of the zeta function sum is small.
  * We show that as $n$ grows, the only numbers not divisible by any prime $p \leq n$ are those with all prime factors larger than $n$.
  * Using `SUMMABLE_SUBZETA`, we establish that the sum over such numbers approaches 0 as $n$ approaches infinity.
  * Through careful estimation of bounds and triangle inequality, we show the distance between our product and 1 becomes arbitrarily small.

- The core insight is that as $n$ increases, the set of numbers not divisible by any prime $p \leq n$ shrinks to just {1}, so the sum approaches 1.

### Mathematical insight
This theorem proves Euler's product formula, which expresses the Riemann zeta function as an infinite product over all primes:

$$\zeta(s) = \prod_{p \text{ prime}} \frac{1}{1-p^{-s}}$$

or equivalently:

$$\zeta(s) \cdot \prod_{p \text{ prime}} (1-p^{-s}) = 1$$

This is a profound connection between the Riemann zeta function and prime numbers, showing how the distribution of primes is encoded in the analytic properties of $\zeta(s)$. This result is fundamental in analytic number theory as it connects the multiplicative structure of the integers (via prime factorization) to the additive structure captured by the zeta function (as a sum). This connection allows analytic methods to be applied to problems in number theory, particularly those concerning prime numbers.

### Dependencies
- Theorems:
  - `ZETA_CONVERGES`: Shows that the Riemann zeta function converges for $\text{Re}(s) > 1$
  - `EULER_PRODUCT_LEMMA`: Shows the relationship between products of $(1-p^{-s})$ and sums over integers not divisible by certain primes
  - `SUMMABLE_SUBZETA`: Establishes summability of $\sum_{n \in t} n^{-s}$ for arbitrary sets $t$ of positive integers when $\text{Re}(s) > 1$
- Definitions:
  - `zeta`: The Riemann zeta function defined as $\zeta(s) = \text{genzeta}(1, s)$

### Porting notes
- This proof requires a well-developed complex analysis library, including complex powers, infinite sums, products, and limits.
- The Riemann zeta function needs to be formally defined as in HOL Light.
- The proof relies on careful manipulation of sets of integers based on their prime factorization - implementers should ensure their system has good support for handling such sets and reasoning about divisibility.
- The epsilon-delta reasoning in the proof may require careful attention in systems with different approaches to limits and convergence.

---

## ZETA_NONZERO_LEMMA

### Name of formal statement
ZETA_NONZERO_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_NONZERO_LEMMA = prove
 (`!s. &1 < Re s ==> ~(zeta s = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; LE_REFL] THEN
  REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_CX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, the Riemann zeta function $\zeta(s)$ is nonzero.

### Informal proof
The proof uses the Euler product formula for the Riemann zeta function.

Let $s$ be a complex number with $\text{Re}(s) > 1$. We proceed by contradiction.

Applying the `EULER_PRODUCT_MULTIPLY` theorem to our assumption $\text{Re}(s) > 1$, we obtain that:
$$\lim_{n \to \infty} \left(\prod_{p \leq n, \, p \text{ prime}} (1 - p^{-s}) \cdot \zeta(s)\right) = 1$$

Suppose for contradiction that $\zeta(s) = 0$. Then:
$$\lim_{n \to \infty} \left(\prod_{p \leq n, \, p \text{ prime}} (1 - p^{-s}) \cdot \zeta(s)\right) = \lim_{n \to \infty} \left(\prod_{p \leq n, \, p \text{ prime}} (1 - p^{-s}) \cdot 0\right) = 0$$

This contradicts the fact that the limit equals 1. The contradiction shows that $\zeta(s) \neq 0$ when $\text{Re}(s) > 1$.

### Mathematical insight
This lemma establishes a fundamental property of the Riemann zeta function: it has no zeros in the region where $\text{Re}(s) > 1$. This result is crucial for several reasons:

1. It forms part of the foundation for studying the distribution of prime numbers using analytic methods.
2. It provides a basis for the analytic continuation of the zeta function into the critical strip.
3. The zeros of the zeta function are central to the Riemann Hypothesis, one of the most famous unsolved problems in mathematics.

The proof elegantly uses the Euler product formula, which connects the zeta function to prime numbers through the equation:
$$\zeta(s) = \prod_{p \text{ prime}} \frac{1}{1-p^{-s}}$$

This connection between the zeta function and prime numbers is what makes it so important in analytic number theory.

### Dependencies
- **Theorems**:
  - `EULER_PRODUCT_MULTIPLY`: Establishes that for any complex $s$ with $\text{Re}(s) > 1$, the product of the Euler product and the zeta function converges to 1.

- **Definitions**:
  - `zeta`: The Riemann zeta function, defined as `zeta s = genzeta 1 s`.

### Porting notes
When porting this theorem to other systems:
- The proof relies on the Euler product formula for the zeta function, which should be established first.
- The theorem uses convergence in the complex plane, so ensure your target system has appropriate machinery for complex analysis.
- The statement is quite straightforward but depends on proper definitions of the Riemann zeta function and complex analysis concepts.

---

## EULER_PRODUCT

### EULER_PRODUCT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EULER_PRODUCT = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. inv(Cx(&1) - inv(Cx(&p) cpow s))))
            --> zeta(s)) sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (PAT_CONV `\x. ((\n. x) --> x) sq`)
   [GSYM COMPLEX_INV_INV] THEN
  MATCH_MP_TAC LIM_COMPLEX_INV THEN
  ASM_SIMP_TAC[COMPLEX_INV_EQ_0; ZETA_NONZERO_LEMMA] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(zeta(s))` o MATCH_MP LIM_COMPLEX_RMUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_MUL_RINV; COMPLEX_MUL_RID] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_INV; FINITE_ATMOST; COMPLEX_INV_INV]);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, the Euler product formula for the Riemann zeta function holds:

$$\lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} \frac{1}{1 - p^{-s}} = \zeta(s)$$

where the limit is taken in the sequential sense (i.e., with respect to the standard topology on the complex plane).

### Informal proof
This proof establishes the Euler product formula for the Riemann zeta function by manipulating the product form.

- First, we rewrite the goal using the identity $\frac{1}{1-p^{-s}} = \frac{1}{\frac{1}{z}}$ where $z = 1-p^{-s}$, which is equivalent to applying a double inversion.

- We then apply the theorem about limits of complex inverses (`LIM_COMPLEX_INV`).

- For this to work, we need to establish that $\zeta(s) \neq 0$ when $\text{Re}(s) > 1$, which is provided by `ZETA_NONZERO_LEMMA`.

- Next, we use `EULER_PRODUCT_MULTIPLY`, which states that 
  $$\lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} (1 - p^{-s}) \cdot \zeta(s) = 1$$

- By multiplying both sides by $\frac{1}{\zeta(s)}$ (which is valid since $\zeta(s) \neq 0$), we get
  $$\lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} (1 - p^{-s}) = \frac{1}{\zeta(s)}$$

- Finally, taking the reciprocal of both sides and using the property that the reciprocal of a product is the product of reciprocals, we obtain
  $$\lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} \frac{1}{1 - p^{-s}} = \zeta(s)$$

### Mathematical insight
The Euler product formula is a fundamental result connecting the Riemann zeta function to the distribution of prime numbers. It expresses that $\zeta(s)$ can be written as an infinite product over all primes, providing a direct link between the zeta function and prime numbers. This connection is crucial in analytic number theory and forms the basis for many important results about the distribution of primes.

The formula illustrates how the properties of the zeta function relate to multiplicative number theory. Each prime contributes a factor to the infinite product, revealing how the zeta function encodes information about the fundamental theorem of arithmetic (unique prime factorization).

This result is particularly important because it allows techniques from complex analysis to be applied to questions about prime numbers, which is the essence of analytic number theory.

### Dependencies
#### Theorems
- `FINITE_ATMOST`: States that for any predicate $P$ and natural number $n$, the set $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is finite.
- `EULER_PRODUCT_MULTIPLY`: Proves that for $\text{Re}(s) > 1$, the sequence $\prod_{p \leq n, p \text{ prime}} (1 - p^{-s}) \cdot \zeta(s)$ converges to 1.
- `ZETA_NONZERO_LEMMA`: States that for $\text{Re}(s) > 1$, the zeta function $\zeta(s)$ is non-zero.

#### Definitions
- `zeta`: Defined as `zeta s = genzeta 1 s`, where `genzeta` is presumably a generalized version of the zeta function.

### Porting notes
When porting this theorem:
1. Ensure your system has a good representation of complex numbers and convergence in the complex plane.
2. Verify that your system has libraries for working with products over sets and limits of sequences.
3. The proof relies heavily on manipulating limits and complex-valued functions, so ensure your target system has strong support for these operations.
4. The definition of the zeta function might need to be adjusted based on the conventions used in the target system.

---

## SUMS_GAMMA

### Name of formal statement
SUMS_GAMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMS_GAMMA = prove
 (`((\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))) -->
    complex_derivative (nearzeta 1) (Cx(&1))) sequentially`,
  MP_TAC(SPECL [`1`; `Cx(&1)`] SUMS_COMPLEX_DERIVATIVE_NEARZETA) THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG; RE_CX; REAL_LT_01; LE_REFL] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; CPOW_N; sums] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC[IN_NUMSEG; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH; REAL_OF_NUM_LT;
           ARITH_RULE `1 <= i ==> 0 < i /\ ~(i = 0)`; GSYM CX_LOG;
           ARITH_RULE `0 < i + 1`] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; REAL_DIV_1]);;
```

### Informal statement
The sequence $((\sum_{i=1}^n \frac{1}{i} - (\log(i+1) - \log(i))))_{n=1}^{\infty}$ converges to the complex derivative of the function `nearzeta` evaluated at $s=1$, where `nearzeta` is defined as:

$\text{nearzeta}(n, s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right) \right)$

### Informal proof
We begin by applying the theorem `SUMS_COMPLEX_DERIVATIVE_NEARZETA` with parameters $n=1$ and $s=1$, which tells us about the sum representation of the complex derivative of `nearzeta`.

When we set $s=1$, several simplifications occur:
- $s-1 = 0$, making the term $(s-1) \cdot \log(m)$ vanish
- $m^s = m^1 = m$

After these simplifications and converting the real numbers to their complex representations (using `GSYM VSUM_CX`), we need to show that the sequence we're interested in matches the simplified sum from `SUMS_COMPLEX_DERIVATIVE_NEARZETA`.

We use `LIM_TRANSFORM_EVENTUALLY` to establish that our sequence is eventually equal to the sum representing the derivative. The key step is showing that for every term in the sum, when $s=1$:

$\frac{1 - (s-1) \cdot \log(m)}{m^s} - \left(\frac{\log(m+1)}{(m+1)^{s-1}} - \frac{\log(m)}{m^{s-1}}\right)$ 

simplifies to:

$\frac{1}{i} - (\log(i+1) - \log(i))$

This establishes the equality between the terms in our sequence and the terms in the sum representation of the complex derivative of `nearzeta` at $s=1$.

### Mathematical insight
This theorem establishes a connection between a specific sequence involving harmonic sums and logarithmic differences, and the derivative of the `nearzeta` function at $s=1$.

The `nearzeta` function is related to the Riemann zeta function, particularly near $s=1$ where the standard zeta function has a pole. The theorem helps characterize the behavior of `nearzeta` at this critical point.

The sequence $\sum_{i=1}^n \frac{1}{i} - (\log(i+1) - \log(i))$ converges to the Euler-Mascheroni constant $\gamma$ as $n$ approaches infinity, which explains why this theorem is named `SUMS_GAMMA`. This constant appears in many areas of analysis and number theory.

### Dependencies
- **Theorems**:
  - `SUMS_COMPLEX_DERIVATIVE_NEARZETA`: Provides the sum representation of the complex derivative of the `nearzeta` function.
  
- **Definitions**:
  - `nearzeta`: Defines the function whose derivative we're computing.

### Porting notes
When porting this theorem:
1. Ensure your target system has a good representation of complex numbers and their operations.
2. The definition of `nearzeta` and the handling of infinite sums will be critical.
3. The proof relies on complex analysis concepts like derivatives and limits, so ensure the target system has these fundamentals established.
4. The simplification steps involving complex powers when $s=1$ may require special attention depending on how the target system handles complex exponentiation.

---

## ZETA_1_NZ

### Name of formal statement
ZETA_1_NZ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZETA_1_NZ = prove
 (`~(zeta(Cx(&1)) = Cx(&0))`,
  REWRITE_TAC[zeta; genzeta] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 - log(&2) <= Re(complex_derivative (nearzeta 1) (Cx(&1)))`
  MP_TAC THENL
   [REWRITE_TAC[RE_DEF] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_LBOUND) THEN
    EXISTS_TAC `\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))` THEN
    REWRITE_TAC[SUMS_GAMMA; TRIVIAL_LIMIT_SEQUENTIALLY; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM RE_DEF; RE_CX] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH; REAL_DIV_1; LOG_1] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a - (b - &0) + c <=> &0 <= c`] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    SIMP_TAC[REAL_SUB_LE; GSYM LOG_DIV; REAL_OF_NUM_LT;
             ARITH_RULE `2 <= x ==> 0 < x /\ 0 < x + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SIMP_TAC[REAL_FIELD `&0 < x ==> (x + &1) / x = &1 + &1 / x`;
             REAL_OF_NUM_LT; ARITH_RULE `2 <= x ==> 0 < x`] THEN
    SIMP_TAC[LOG_LE; REAL_LE_DIV; REAL_POS];
    ASM_REWRITE_TAC[RE_CX; REAL_NOT_LE; REAL_SUB_LT] THEN
    GEN_REWRITE_TAC I [GSYM REAL_EXP_MONO_LT] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH] THEN
    SUBGOAL_THEN `(&1 + &1 / &2) pow 2 <= exp(&1 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_LE_X];
      ALL_TAC] THEN
    SIMP_TAC[GSYM REAL_EXP_N; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
The statement asserts that $\zeta(1) \neq 0$, where $\zeta$ is the Riemann zeta function.

In detail, it states that $\zeta(1)$ is not equal to $0$ in the complex plane, where $\zeta$ is the Riemann zeta function and $1$ is represented as a complex number $\mathbb{C}(1)$.

### Informal proof
We prove that $\zeta(1) \neq 0$ by contradiction. Assume that $\zeta(1) = 0$.

First, we recall that $\zeta(s) = \text{genzeta}(1,s)$ and $\text{genzeta}(n,s)$ at $s = 1$ is defined as the complex derivative of $\text{nearzeta}(n)$ at $s = 1$.

We prove that $1 - \log(2) \leq \text{Re}(\text{complex\_derivative}(\text{nearzeta}(1), 1))$:
- We use the fact that the sequence $\left(\sum_{i=1}^{n} \left(\frac{1}{i} - (\log(i+1) - \log(i))\right)\right)$ converges to $\text{complex\_derivative}(\text{nearzeta}(1), 1)$ (from SUMS_GAMMA)
- For any $n \geq 1$, we have 
  $\sum_{i=1}^{n} \left(\frac{1}{i} - (\log(i+1) - \log(i))\right) = 1 - \log(n+1) + \sum_{i=2}^{n} \left(\frac{1}{i} - (\log(i+1) - \log(i))\right)$
- Since $\log\left(\frac{i+1}{i}\right) = \log\left(1 + \frac{1}{i}\right) \leq \frac{1}{i}$ for $i \geq 2$, we have 
  $\frac{1}{i} - (\log(i+1) - \log(i)) \geq 0$
- Thus, $\sum_{i=1}^{n} \left(\frac{1}{i} - (\log(i+1) - \log(i))\right) \geq 1 - \log(n+1)$
- Taking the limit as $n \to \infty$, we get $\text{Re}(\text{complex\_derivative}(\text{nearzeta}(1), 1)) \geq 1 - \log(2)$

But by our assumption $\zeta(1) = 0$, we have $\text{Re}(\text{complex\_derivative}(\text{nearzeta}(1), 1)) = 0$, which implies $0 \geq 1 - \log(2)$, or $\log(2) \geq 1$.

We derive a contradiction by showing that $\log(2) < 1$:
- We use $\left(1 + \frac{1}{2}\right)^2 \leq e^{1/2} \cdot e^{1/2} = e^1$
- This gives us $(\frac{3}{2})^2 \leq e^1$
- Simplifying, $\frac{9}{4} \leq e$
- Taking logarithms, $\log(2) < \log(\frac{9}{4}) < 1$

This contradicts our earlier inequality, so our assumption that $\zeta(1) = 0$ must be false.

### Mathematical insight
This theorem establishes an important property of the Riemann zeta function - namely that $\zeta(1)$ is not zero. 

The Riemann zeta function is traditionally defined for $\text{Re}(s) > 1$ as $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$, which diverges at $s = 1$. However, the function can be analytically continued to the entire complex plane except for a simple pole at $s = 1$. The theorem uses a regularized version of the zeta function that handles this pole.

The proof uses estimates involving the logarithmic function and employs a common technique in analytic number theory - finding bounds for the real part of complex functions. The fact that $\zeta(1) \neq 0$ is crucial for various results in number theory and analysis.

### Dependencies
- `nearzeta`: Definition of a regularized version of the zeta function 
- `genzeta`: Definition that extends the regularized zeta function
- `zeta`: Definition of the Riemann zeta function in terms of genzeta
- `SUMS_GAMMA`: Theorem relating a specific series to the complex derivative of nearzeta at 1

### Porting notes
When porting this proof to another system:
1. You'll need to carefully handle the analytic continuation of the zeta function
2. The proof relies on estimates for logarithmic functions, so ensure your system has appropriate libraries for real analysis
3. Note that HOL Light's `nearzeta` and `genzeta` represent specific constructions for handling the zeta function, which might need to be reimplemented in your target system

---

## ZETA_MULTIPLE_BOUND

### ZETA_MULTIPLE_BOUND
- `ZETA_MULTIPLE_BOUND`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZETA_MULTIPLE_BOUND = prove
 (`!x y. real x /\ real y /\ &1 < Re x
       ==> &1 <= norm(zeta(x) pow 3 *
                      zeta(x + ii * y) pow 4 *
                      zeta(x + Cx(&2) * ii * y) pow 2)`,
  let lemma1 = prove
   (`&0 <= a /\ &0 <= b /\ &0 <= c /\
     c * (&2 * a + b) pow 3 / &27 <= x
     ==> c * a pow 2 * b <= x`,
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH
     `a pow 2 * b <= (&2 * a + b) pow 3 / &27 <=>
      &0 <= (&8 / &27 * a + &1 / &27 * b) * (a - b) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC)
  and lemma2 = prove
   (`-- &1 <= t /\ t <= &1
     ==> &0 <= &1 + r pow 2 - &2 * r * t`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= (&1 - t) * (&1 + t) /\ &0 <= (r - t) pow 2
      ==> &0 <= &1 + r pow 2 - &2 * r * t`) THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\n. cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow x))) pow 3 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow (x + ii * y)))) pow 4 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) -
                      inv(Cx(&p) cpow (x + Cx(&2) * ii * y)))) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    MATCH_MP_TAC EULER_PRODUCT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[LE_0] THEN X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_INV; COMPLEX_NORM_NZ; COMPLEX_INV_EQ_0] THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; ARITH; COMPLEX_INV_EQ_0;
               CPRODUCT_EQ_0; IN_ELIM_THM; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&1) - x = Cx(&0) <=> x = Cx(&1)`] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[TAUT `(~p \/ ~q) \/ ~r <=> p /\ q ==> ~r`] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `(norm:complex->real) o inv`) THEN
    REWRITE_TAC[COMPLEX_NORM_INV; o_THM; COMPLEX_NORM_CX; REAL_ABS_NUM;
                REAL_INV_INV; REAL_INV_1] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
                 REAL_EXP_EQ_1; REAL_CX; RE_CX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x /\ &0 < y ==> ~(x = &0 \/ y = &0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_POW; FINITE_ATMOST; GSYM CPRODUCT_MUL] THEN
  SIMP_TAC[GSYM CPRODUCT_INV; COMPLEX_INV_INV; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; GSYM COMPLEX_POW_INV; COMPLEX_INV_INV] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_ATMOST; REAL_INV_1] THEN
  MATCH_MP_TAC PRODUCT_LE_1 THEN SIMP_TAC[NORM_POS_LE; FINITE_ATMOST] THEN
  X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[CPOW_ADD; COMPLEX_MUL_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_INV_MUL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ASM_REWRITE_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
  REWRITE_TAC[GSYM CEXP_NEG; GSYM CEXP_N] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o CONV_RULE(REWR_CONV REAL))) THEN
  SIMP_TAC[GSYM CX_MUL; GSYM CX_NEG; GSYM CX_EXP; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `--(ii * x) = ii * --x`] THEN
  REWRITE_TAC[COMPLEX_RING `--(Cx(&2) * ii * x) = ii * Cx(&2) * --x`] THEN
  REWRITE_TAC[CEXP_EULER] THEN
  REWRITE_TAC[CCOS_NEG; CSIN_NEG; GSYM CX_SIN; GSYM CX_COS; GSYM CX_NEG;
              GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  SIMP_TAC[REAL_RING `(z:real) pow 4 = (z pow 2) pow 2`; COMPLEX_SQNORM] THEN
  REWRITE_TAC[COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RE_MUL_CX; RE_ADD; RE_MUL_II;
              IM_SUB; IM_CX; IM_MUL_CX; IM_ADD; IM_MUL_II] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_SUB_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_RING
   `(&1 - r * c) pow 2 + --(r * s) pow 2 =
    &1 + r pow 2 * (s pow 2 + c pow 2) - &2 * r * c`] THEN
  REWRITE_TAC[SIN_CIRCLE; REAL_POW_NEG; ARITH] THEN
  ABBREV_TAC `r = exp(--(Re x * log(&p)))` THEN
  REWRITE_TAC[COS_DOUBLE_COS; COS_NEG; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ABBREV_TAC `t = cos(Re y * log(&p))` THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ARITH
   `x - &2 * r * (&2 * y - &1) = x + &2 * r - &4 * r * y`] THEN
  MP_TAC(SPEC `Re y * log(&p)` COS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` MP_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SUBST1_TAC(GSYM REAL_EXP_0) THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < t <=> 2 <= t`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `r < &1 ==> abs(&1 - r) = (&1 - r)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  MATCH_MP_TAC lemma1 THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_SUB_LE; lemma2] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `&1 + s + &2 * r - &4 * r * t = &1 + s - &2 * r * (&2 * t - &1)`] THEN
    MATCH_MP_TAC lemma2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `-- &1 <= &2 * x pow 2 - &1 <=> &0 <= x * x`;
                REAL_ARITH `&2 * t pow 2 - &1 <= &1 <=> t pow 2 <= &1 pow 2`;
                REAL_LE_SQUARE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `x pow 3 * y pow 3 / &27 <= &1 <=> (x * y) pow 3 <= &3 pow 3`] THEN
  MATCH_MP_TAC REAL_POW_LE2_ODD THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (&1 + r pow 2 - &2 * r * t) + &1 + r pow 2 +
    &2 * r - &4 * r * t pow 2 =
    (&3 + &3 * r pow 2) - &2 * r * (&2 * t pow 2 + &2 * t - &1)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - r) * ((&3 + &3 * r pow 2) + &3 * r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH
     `c - &2 * r * y <= c + &3 * r <=> &0 <= r * (&2 * y + &3)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &2 * (&2 * t pow 2 + &2 * t - &1) + &3 <=>
                            &0 <= (t + &1 / &2) pow 2`] THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r pow 3` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE]; REAL_ARITH_TAC]);;
```

### Informal statement
For all complex numbers $x$ and $y$ where both $x$ and $y$ are real and $\mathrm{Re}(x) > 1$, the following inequality holds:
$$1 \leq \left|\zeta(x)^3 \cdot \zeta(x + iy)^4 \cdot \zeta(x + 2iy)^2\right|$$

### Informal proof
The proof establishes that the norm of this particular product of zeta functions is bounded below by 1. The strategy involves using the Euler product representation of the zeta function and proving the inequality holds for the corresponding product.

First, two key lemmas are established:

1. If $a, b, c \geq 0$ and $c \cdot (2a + b)^3 / 27 \leq x$, then $c \cdot a^2 \cdot b \leq x$
2. If $-1 \leq t \leq 1$, then $0 \leq 1 + r^2 - 2rt$

The main proof proceeds as follows:

- We use the limit of norms bound theorem (`LIM_NORM_LBOUND`) and represent each zeta function using the Euler product formula:
  $$\zeta(s) = \lim_{n\to\infty} \prod_{p \leq n, p \text{ prime}} \frac{1}{1 - p^{-s}}$$

- For each prime $p$, we analyze the contribution to the product and show that:
  $$\left|\frac{1}{(1-p^{-x})^3} \cdot \frac{1}{(1-p^{-(x+iy)})^4} \cdot \frac{1}{(1-p^{-(x+2iy)})^2}\right| \geq 1$$

- Setting $r = \exp(-\text{Re}(x) \cdot \log(p))$ and $t = \cos(\text{Re}(y) \cdot \log(p))$, we use properties of complex exponentials and trigonometric functions to express the product norm in terms of $r$ and $t$.

- Since $\text{Re}(x) > 1$, we have $0 < r < 1$, and by properties of cosine, $-1 \leq t \leq 1$.

- Using the established lemmas and careful algebraic manipulation, we arrive at the desired inequality.

### Mathematical insight
This theorem establishes an important lower bound for a specific combination of zeta function values. The particular combination $\zeta(x)^3 \cdot \zeta(x + iy)^4 \cdot \zeta(x + 2iy)^2$ is carefully chosen so that when analyzed using the Euler product representation, the contributions from each prime create a product that is always at least 1.

This result is part of a broader approach to studying the locations of zeros of the Riemann zeta function. The theorem essentially shows that this specific combination cannot vanish when $\text{Re}(x) > 1$, which aligns with the known fact that $\zeta(s)$ has no zeros in this region. The approach using such combinations of zeta values at different points is a powerful technique in analytic number theory.

The proof technique demonstrates how clever algebraic manipulations, combined with properties of the Euler product representation, can establish important analytic properties of the zeta function.

### Dependencies
- Theorems:
  - `FINITE_ATMOST`: Establishes that the set $\{m \in \mathbb{N} \mid P(m) \land m \leq n\}$ is finite.
  - `EULER_PRODUCT`: The Euler product representation of the Riemann zeta function for $\text{Re}(s) > 1$.
  - Various auxiliary theorems about limits, complex arithmetic, and analytic properties.

- Definitions:
  - `zeta`: The Riemann zeta function defined as `zeta s = genzeta 1 s`.

### Porting notes
When porting this theorem:
1. Ensure that your target system has a good representation of the Euler product for the zeta function.
2. The proof relies heavily on complex analysis, so ensure your complex analysis library has the needed theorems about limits, norms, and complex exponentials.
3. The algebraic manipulations are complex - some proof assistants might require more detailed justification for the algebraic steps.
4. Be careful with the handling of the Riemann zeta function, as different systems might define it slightly differently.

---

## ZETA_NONZERO

### ZETA_NONZERO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(zeta s = Cx(&0))`,
  REWRITE_TAC[REAL_ARITH `&1 <= x <=> &1 < x \/ x = &1`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ZETA_NONZERO_LEMMA] THEN
  SUBST1_TAC(SPEC `s:complex` COMPLEX_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `y = Im s` THEN ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; ZETA_1_NZ] THEN
  DISCH_TAC THEN SUBGOAL_THEN
  `~(&1 <= norm((Cx(&0) *
                complex_derivative (\x. zeta(x + ii * Cx y)) (Cx(&1)) pow 4) *
                zeta (Cx(&1) + Cx (&2) * ii * Cx(y)) pow 2))`
  MP_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_MUL_LZERO] THEN REAL_ARITH_TAC;
    SIMP_TAC[]] THEN
  MATCH_MP_TAC(ISPEC `at (Cx(&1)) within {s | real s /\ &1 < Re s}`
   LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\x. zeta (x) pow 3 * zeta (x + ii * Cx(y)) pow 4 *
        zeta (x + Cx (&2) * ii * Cx(y)) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; TRIVIAL_LIMIT_WITHIN] THEN
  SUBGOAL_THEN `Cx(&1) limit_point_of {s | real s /\ &1 < Re s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIMPT_APPROACHABLE_LE] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN EXISTS_TAC `Cx(&1 + e)` THEN
    REWRITE_TAC[dist; CX_INJ; IN_ELIM_THM; REAL_CX; RE_CX] THEN
    REWRITE_TAC[GSYM CX_SUB; REAL_ADD_SUB; COMPLEX_NORM_CX] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
    SIMP_TAC[ZETA_MULTIPLE_BOUND; REAL_CX]] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_POW THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II; RE_II; RE_CX] THEN
    REWRITE_TAC[COMPLEX_RING `x + y = x <=> y = Cx(&0)`] THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (zeta x pow 3 * (x - Cx(&1)) pow 4) *
                  (zeta(x + ii * Cx y) / (x - Cx(&1))) pow 4` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; GSYM DIST_NZ; COMPLEX_SUB_0; COMPLEX_FIELD
     `~(x = Cx(&0))
      ==> (y * x pow 4) * (z / x) pow 4 - y * z pow 4 = Cx(&0)`] THEN
    SIMP_TAC[dist; COMPLEX_VEC_0; COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    SUBGOAL_THEN `((\x. zeta (x + ii * Cx y)) has_complex_derivative
                   complex_derivative (\x. zeta (x + ii * Cx y)) (Cx (&1)))
                  (at (Cx (&1)) within {s | real s /\ &1 < Re s})`
    MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN; COMPLEX_SUB_RZERO]] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
    SIMP_TAC[COMPLEX_DIFFERENTIABLE_ADD; COMPLEX_DIFFERENTIABLE_CONST;
             COMPLEX_DIFFERENTIABLE_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_II; COMPLEX_RING `x + y = x <=> y = Cx(&0)`;
                    IM_CX; COMPLEX_ENTIRE; II_NZ; RE_CX; CX_INJ] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (nearzeta 1 (x) + Cx(&1)) pow 3 * (x - Cx(&1))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; CPOW_1; GSYM DIST_NZ; zeta; genzeta; COMPLEX_DIV_1;
    COMPLEX_FIELD
    `~(x:complex = a)
     ==> b * (x - a) - (c / (x - a)) pow 3 * (x - a) pow 4 =
         (b - c pow 3) * (x - a)`] THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
    SIMP_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_AT_WITHIN THEN SUBST1_TAC(COMPLEX_RING
   `Cx(&0) = (nearzeta 1 (Cx(&1)) + Cx(&1)) pow 3 * (Cx(&1) - Cx(&1))`) THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  SIMP_TAC[LIM_SUB; LIM_CONST; LIM_AT_ID] THEN
  MATCH_MP_TAC LIM_COMPLEX_POW THEN MATCH_MP_TAC LIM_ADD THEN
  REWRITE_TAC[LIM_CONST] THEN REWRITE_TAC[GSYM CONTINUOUS_AT] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_NEARZETA;
               RE_CX; REAL_OF_NUM_LT; ARITH]);;
```

### Informal statement
For all complex numbers $s$ such that $\operatorname{Re}(s) \geq 1$, the Riemann zeta function $\zeta(s)$ is non-zero: $\zeta(s) \neq 0$.

### Informal proof
This is a key property of the Riemann zeta function. The proof proceeds by cases:

* **Case 1:** $\operatorname{Re}(s) > 1$. 
  - This follows directly from `ZETA_NONZERO_LEMMA`, which shows that $\zeta(s) \neq 0$ for $\operatorname{Re}(s) > 1$.

* **Case 2:** $s = 1$.
  - If $s = 1$, we apply `ZETA_1_NZ`, which specifically proves that $\zeta(1) \neq 0$.

* **Case 3:** $s$ is complex with $\operatorname{Re}(s) = 1$ and $\operatorname{Im}(s) \neq 0$.
  - This is the most challenging case. The proof uses a subtle analytical argument involving complex analysis:
  - We first show that the function $f(x) = \zeta(x)^3 \cdot \zeta(x + iy)^4 \cdot \zeta(x + 2iy)^2$ has norm $\geq 1$ when $\operatorname{Re}(x) > 1$.
  - We then consider the limit of this function as $x$ approaches 1 from the right within the half-plane $\operatorname{Re}(s) > 1$.
  - We show by contradiction that if $\zeta(1 + iy) = 0$, this would lead to a contradiction regarding the bound on the norm.
  - The proof uses complex differentiation, properties of holomorphic functions, and careful estimate of the limits.

### Mathematical insight
This theorem establishes the non-vanishing of the Riemann zeta function in the critical region $\operatorname{Re}(s) \geq 1$. It's a fundamental property with significant implications:

1. It confirms a part of the Riemann hypothesis boundary case.
2. It ensures that $1/\zeta(s)$ is well-defined in this region.
3. It's essential for properties related to the distribution of prime numbers.
4. The fact that $\zeta(s) \neq 0$ for $\operatorname{Re}(s) = 1$ is particularly important for analytic number theory.

The proof combines both elementary arguments (for $\operatorname{Re}(s) > 1$) and sophisticated complex analysis (for the critical line $\operatorname{Re}(s) = 1$).

### Dependencies
- **Theorems**:
  - `ZETA_NONZERO_LEMMA`: Shows $\zeta(s) \neq 0$ for $\operatorname{Re}(s) > 1$
  - `ZETA_1_NZ`: Proves specifically that $\zeta(1) \neq 0$
  - `ZETA_MULTIPLE_BOUND`: Provides a crucial bound for the complex case
  - `COMPLEX_DIFFERENTIABLE_NEARZETA`: Shows differentiability of `nearzeta`
  - `COMPLEX_DIFFERENTIABLE_AT_ZETA`: Shows differentiability of `zeta`

- **Definitions**:
  - `zeta`: The Riemann zeta function
  - `genzeta`: A generalized zeta function
  - `nearzeta`: An auxiliary function used to define the zeta function

### Porting notes
When porting this theorem:
1. The proof relies heavily on complex analysis and properties of the Riemann zeta function.
2. Special attention should be given to how the zeta function is defined at $s = 1$, as this is often a special case.
3. The contradiction argument for the case on the critical line $\operatorname{Re}(s) = 1$ is intricate and may require careful adaptation.
4. Dependencies like `ZETA_MULTIPLE_BOUND` involve sophisticated estimates that may need separate careful porting.

---

## NEARZETA_NONZERO

### NEARZETA_NONZERO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NEARZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(nearzeta 1 s + Cx (&1) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_NONZERO) THEN
  REWRITE_TAC[zeta; genzeta] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NEARZETA_1; ARITH; CPOW_1] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;
```

### Informal statement
For all complex numbers $s$ where $1 \leq \text{Re}(s)$, we have $\text{nearzeta}(1, s) + 1 \neq 0$.

### Informal proof
To prove that $\text{nearzeta}(1, s) + 1 \neq 0$ when $1 \leq \text{Re}(s)$, we use the fact that the Riemann zeta function $\zeta(s)$ is nonzero in this region:

- First, apply the theorem `ZETA_NONZERO` which states that $\zeta(s) \neq 0$ when $1 \leq \text{Re}(s)$.
- Then, expand the definition of $\zeta$ as `zeta s = genzeta 1 s`.
- Next, expand the definition of `genzeta`:
  * If $s = 1$, then $\text{genzeta}(1, s) = \text{complex\_derivative}(\text{nearzeta}(1))(1)$
  * Otherwise, $\text{genzeta}(1, s) = \frac{\text{nearzeta}(1, s) + \frac{1}{1^{s-1}}}{s-1}$
- We consider two cases:
  * Case $s = 1$: By `NEARZETA_1`, we have $\text{nearzeta}(1, 1) = 0$, so $\text{nearzeta}(1, 1) + 1 = 1 \neq 0$.
  * Case $s \neq 1$: Use complex field arithmetic to show that if $\zeta(s) \neq 0$, then $\text{nearzeta}(1, s) + 1 \neq 0$.
- The result follows from complex field arithmetic, which establishes the algebraic relationship between $\zeta(s)$ and $\text{nearzeta}(1, s) + 1$.

### Mathematical insight
This theorem establishes an important non-vanishing property of the modified function $\text{nearzeta}(1, s) + 1$ in the half-plane $\text{Re}(s) \geq 1$. The result is closely related to the well-known fact that the Riemann zeta function $\zeta(s)$ has no zeros in the region $\text{Re}(s) > 1$. The relationship between $\text{nearzeta}$ and $\zeta$ is given through the `genzeta` function, where `genzeta` serves as an analytic continuation of certain series.

This non-vanishing property is important for analytic properties in complex analysis, particularly when studying the behavior of functions derived from the Riemann zeta function.

### Dependencies
- Theorems:
  - `NEARZETA_1`: States that $\text{nearzeta}(n, 1) = 0$ for $n \geq 1$
  - `ZETA_NONZERO`: States that $\zeta(s) \neq 0$ when $1 \leq \text{Re}(s)$
  
- Definitions:
  - `nearzeta`: Defines the near-zeta function through an infinite sum
  - `genzeta`: Defines a generalized zeta function using `nearzeta`
  - `zeta`: Defines the Riemann zeta function as `genzeta 1 s`

### Porting notes
When porting this theorem:
1. Ensure that the relationship between `nearzeta`, `genzeta`, and `zeta` is properly established in the target system.
2. The proof relies on complex field arithmetic, which might be handled differently in other proof assistants.
3. The case distinction (when $s = 1$ and $s \neq 1$) is crucial to handle the potential singularity at $s = 1$.
4. The proof uses the definitional equalities heavily, so make sure these are properly tracked in the target system.

---

## NORM_CLOG_BOUND

### Name of formal statement
NORM_CLOG_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_CLOG_BOUND = prove
 (`norm(z) <= &1 / &2 ==> norm(clog(Cx(&1) - z)) <= &2 * norm(z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog(Cx(&1) - z)`; `\z. inv(z - Cx(&1))`;
   `cball(Cx(&0),&1 / &2)`; `&2`] COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO; CLOG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REWRITE_TAC[IN_CBALL] THEN
    ASM_REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
   [COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_RING `(Cx(&0) - Cx(&1)) * x = --x`] THEN
    REWRITE_TAC[COMPLEX_NEG_INV; COMPLEX_NEG_SUB] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MP_TAC(SPEC `w:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&1 / &2)`)) THEN
  REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  MP_TAC(SPEC `1` COMPLEX_NORM_NUM) THEN ASM_NORM_ARITH_TAC);;
```

### Informal statement
For any complex number $z$ with $\|z\| \leq \frac{1}{2}$, we have
$$\|\log(1 - z)\| \leq 2 \|z\|$$
where $\log$ is the complex logarithm function.

### Informal proof
We apply the `COMPLEX_DIFFERENTIABLE_BOUND` theorem to the functions $f(z) = \log(1 - z)$ and $g(z) = \frac{1}{z - 1}$, with the compact ball $B(0, \frac{1}{2})$ and constant $2$.

The theorem requires us to verify several conditions:
1. The ball $B(0, \frac{1}{2})$ is convex (which is true for all balls)
2. For any $w \in B(0, \frac{1}{2})$, we need:
   - $f$ is complex-differentiable at $w$ with $f'(w) = g(w)$
   - $\|g(w)\| \leq 2$ for all $w$ in the ball

For the first condition, we verify that $f$ is complex-differentiable and its derivative is $f'(w) = -\frac{1}{1-w} = \frac{1}{w-1}$. The condition $\text{Re}(1-w) > 0$ is satisfied because $\|w\| \leq \frac{1}{2}$ implies $\text{Re}(w) < 1$.

For the second condition, we have:
$$\|g(w)\| = \left\|\frac{1}{w-1}\right\| = \frac{1}{\|w-1\|}$$

Since $\|w\| \leq \frac{1}{2}$, we can show that $\|w-1\| \geq \frac{1}{2}$. This gives us $\|g(w)\| \leq 2$.

Finally, we apply the theorem to our specific case, where $z \in B(0, \frac{1}{2})$ and $0$ is the center of the ball. Since $\log(1) = 0$, we can derive the inequality:
$$\|\log(1-z)\| \leq 2\|z\|$$

### Mathematical insight
This theorem provides a bound on the complex logarithm function in a neighborhood of 1. The logarithm function has a singularity at 0, but this result shows that near 1, the function behaves in a controlled manner - specifically, the norm of $\log(1-z)$ is bounded by twice the norm of $z$ when $z$ is close enough to 0.

This kind of bound is useful in complex analysis, particularly when studying the behavior of analytic functions. The bound is related to the logarithmic derivative of the zeta function, as indicated in the comment, which is crucial in analytic number theory.

### Dependencies
- `COMPLEX_DIFFERENTIABLE_BOUND`: Used to establish the bound based on complex differentiability properties.
- `COMPLEX_DIFF_TAC`: Used in the proof to handle complex differentiation.
- `COMPLEX_NORM_GE_RE_IM`: Used to establish inequalities involving the complex norm.
- `COMPLEX_NORM_INV`: Used for handling norms of inverses.
- `COMPLEX_NORM_NUM`: Used for the norm of a complex number representing an integer.
- `CONVEX_CBALL`: Used to establish that complex balls are convex.
- `CLOG_1`: Property that the complex logarithm of 1 is 0.
- `CENTRE_IN_CBALL`: Property that the center is in a ball.
- `IN_CBALL`: Defines membership in a complex ball.

### Porting notes
When porting this theorem to another system, pay attention to:
1. The definition of the complex logarithm, especially its branch cuts
2. The handling of complex differentiability
3. The representation of complex balls and their properties
4. The tactical structure used in HOL Light is quite specific, so you'll need to adapt the proof strategy rather than the exact tactics

---

## LOGZETA_EXISTS

### LOGZETA_EXISTS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LOGZETA_EXISTS = prove
 (`?logzeta logzeta'.
        !s. s IN {s | Re s > &1}
            ==> ((\p. clog(Cx(&1) - inv(Cx(&p) cpow s)))
                 sums logzeta(s))
                {p | prime p} /\
                ((\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1)))
                 sums logzeta'(s))
                {p | prime p} /\
                (logzeta has_complex_derivative logzeta'(s)) (at s)`,
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
      COMPLEX_SUB_LZERO; COMPLEX_MUL_LID; COMPLEX_FIELD
       `~(x = Cx(&0)) ==> --(a * x) / x pow 2 = --(a / x)`] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_INV_MUL] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ; COMPLEX_FIELD
     `~(y = Cx(&0)) ==> y * (Cx(&1) - inv(y)) = y - Cx(&1)`] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `!y. abs x <= y /\ y < w ==> x < w`) THEN
    EXISTS_TAC `norm(inv (Cx (&p) cpow s))` THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN REWRITE_TAC[RE_CX] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < p <=> 2 <= p`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `s:complex` THEN
  DISCH_TAC THEN EXISTS_TAC `(Re(s) - &1) / &2` THEN
  EXISTS_TAC `\p. Cx(&2) / Cx(&p) cpow (Cx(&1 + (Re(s) - &1) / &2))` THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT; RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             ARITH_RULE `0 < n <=> 1 <= n`; GSYM CX_INV; REAL_LE_INV_EQ;
             REAL_EXP_POS_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_FROM; PRIME_GE_2;
             ARITH_RULE `2 <= p ==> 1 <= p`] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `inv(x) = Cx(&1) * inv x`] THEN
    REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ;
             PRIME_IMP_NZ; GSYM CX_DIV; REAL_CX; REAL_LE_DIV; REAL_POS;
             REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `summable (from 1) (\n. Cx (&1) / Cx (&n) cpow (Cx(&1 + (Re s - &1) / &2)))`
  MP_TAC THENL
   [REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2` o MATCH_MP SERIES_GOESTOZERO) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[IN_FROM; PRIME_IMP_NZ; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(inv(Cx(&p) cpow y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NORM_CLOG_BOUND THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> y <= x ==> y <= a`)) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID];
    SIMP_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]] THEN
  REWRITE_TAC[GSYM CPOW_NEG] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL_MONO; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN REAL_ARITH_TAC);;
```

### Informal statement
For the Riemann zeta function, there exists functions $\text{logzeta}$ and $\text{logzeta}'$ such that for all complex numbers $s$ with real part $\text{Re}(s) > 1$:

1. The series $\sum_{p \in \mathbb{P}} \log(1 - \frac{1}{p^s})$ converges to $\text{logzeta}(s)$, where $\mathbb{P}$ is the set of prime numbers.

2. The series $\sum_{p \in \mathbb{P}} \frac{\log(p)}{p^s - 1}$ converges to $\text{logzeta}'(s)$.

3. $\text{logzeta}$ is complex differentiable at $s$ with derivative $\text{logzeta}'(s)$.

### Informal proof
The proof applies the theorem `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` to establish the existence of $\text{logzeta}$ and $\text{logzeta}'$ with the required properties. This involves showing:

1. **Domain verification**: First, we confirm that $\{s \mid \text{Re}(s) > 1\}$ is an open set.

2. **Differentiability of terms**: For each prime $p$ and $s$ with $\text{Re}(s) > 1$, we show that $\log(1 - \frac{1}{p^s})$ is differentiable with respect to $s$ with derivative $\frac{\log(p)}{p^s - 1}$.
   - We use complex differentiation and algebraic manipulations to verify that:
     $$\frac{d}{ds}\log(1 - \frac{1}{p^s}) = \frac{\log(p)}{p^s - 1}$$
   - We also verify that $\text{Re}(s) > 1$ ensures that $|\frac{1}{p^s}| < 1$, which is required for the logarithm to be well-defined.

3. **Convergence bound**: For any $s$ with $\text{Re}(s) > 1$, we establish a summable bound for the terms.
   - We choose $d = \frac{\text{Re}(s) - 1}{2} > 0$ and define a bounding function:
     $$h(p) = \frac{2}{p^{1 + \frac{\text{Re}(s) - 1}{2}}}$$
   - We show that $h(p)$ is summable over primes by relating it to the convergent zeta function with parameter $1 + \frac{\text{Re}(s) - 1}{2} > 1$.
   - For any $y$ in the ball of radius $d$ around $s$, we show that $|\log(1 - \frac{1}{p^y})| \leq 2|\frac{1}{p^y}|$.
   - We use the theorem `NORM_CLOG_BOUND` and the convergence of the zeta function to establish our bounds.

The application of `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX` then gives us the existence of $\text{logzeta}$ and $\text{logzeta}'$ with the desired properties.

### Mathematical insight
This theorem establishes the existence and differentiability of the logarithm of a version of the Euler product for the Riemann zeta function. The Euler product gives:

$$\zeta(s) = \prod_{p \text{ prime}} \frac{1}{1 - p^{-s}} \text{ for } \text{Re}(s) > 1$$

Taking logarithms gives:

$$\log(\zeta(s)) = \sum_{p \text{ prime}} \log\left(\frac{1}{1 - p^{-s}}\right) = -\sum_{p \text{ prime}} \log(1 - p^{-s})$$

This theorem establishes that $\text{logzeta}(s) = \sum_{p} \log(1 - \frac{1}{p^s})$ converges and is differentiable for $\text{Re}(s) > 1$. The $\text{logzeta}$ function defined here is the negative of the logarithm of the zeta function, which is useful in complex analysis and often in the study of the distribution of prime numbers.

The differentiability result is important for applications in analytic number theory where the behavior of the logarithmic derivative of the zeta function provides insights into the distribution of primes.

### Dependencies
- **Theorems**:
  - `SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX`: For demonstrating the existence of a sum of a series and its term-by-term derivative simultaneously
  - `ZETA_CONVERGES`: For the convergence of the Riemann zeta function for Re(s) > 1
  - `NORM_CLOG_BOUND`: For bounding the complex logarithm

- **Definitions**:
  - `zeta`: The Riemann zeta function defined as `zeta s = genzeta 1 s`

### Porting notes
When porting this to another system:
1. Ensure the target system has appropriate complex analysis libraries, particularly for complex differentiation and series convergence.
2. The proof relies heavily on properties of the Riemann zeta function, so these may need to be established first.
3. The handling of complex logarithms can differ between systems; verify how `clog` is defined and ensure that the branch cuts are consistent.
4. The bound using `NORM_CLOG_BOUND` might require explicit construction in systems with different libraries for complex analysis.

---

## LOGZETA_PROPERTIES

### LOGZETA_PROPERTIES

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let LOGZETA_PROPERTIES =
  new_specification ["logzeta"; "logzeta'"] LOGZETA_EXISTS;;
```

### Informal statement
The specification `LOGZETA_PROPERTIES` introduces two functions, `logzeta` and `logzeta'`, that satisfy the following properties:

For all complex numbers $s$ with $\text{Re}(s) > 1$:

1. $\sum_{p \text{ prime}} \log(1 - \frac{1}{p^s}) = \text{logzeta}(s)$
2. $\sum_{p \text{ prime}} \frac{\log(p)}{p^s - 1} = \text{logzeta}'(s)$
3. $\text{logzeta}$ is complex differentiable at $s$ with derivative $\text{logzeta}'(s)$

### Informal proof
This is a specification rather than a theorem with a proof. It uses the existence theorem `LOGZETA_EXISTS` to define the functions `logzeta` and `logzeta'` with the desired properties.

Using new_specification creates constants (`logzeta` and `logzeta'`) that satisfy exactly the properties established in `LOGZETA_EXISTS`.

### Mathematical insight
This specification defines two important functions related to the Riemann zeta function:

- `logzeta` is the logarithm of the inverse of the Euler product representation of the zeta function. For $\text{Re}(s) > 1$, we know that $\zeta(s) = \prod_p \frac{1}{1-p^{-s}}$, so $\log(\zeta(s)^{-1}) = \sum_p \log(1-p^{-s})$.

- `logzeta'` is the complex derivative of `logzeta` and can be represented as a series involving prime numbers.

These functions are crucial in analytic number theory, especially in the study of the distribution of prime numbers and the behavior of the zeta function. The relationship between these functions and the prime counting function is established through the logarithmic derivative of the zeta function.

### Dependencies
- Theorems:
  - `LOGZETA_EXISTS`: Establishes the existence of functions with the properties defined in the specification

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has a mechanism similar to HOL Light's `new_specification` for defining new constants based on existence theorems
2. Make sure complex analysis primitives (complex differentiation, series summation) are available in the target system
3. The underlying `LOGZETA_EXISTS` theorem is quite involved and relies on complex analysis results about uniform convergence and differentiation of series

---

## [LOGZETA_CONVERGES;

### Name of formal statement
LOGZETA_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let [LOGZETA_CONVERGES; LOGZETA'_CONVERGES; HAS_COMPLEX_DERIVATIVE_LOGZETA] =
    CONJUNCTS(REWRITE_RULE[IN_ELIM_THM; FORALL_AND_THM; real_gt; TAUT
                             `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                          LOGZETA_PROPERTIES);;
```

### Informal statement
The logarithm of the Riemann zeta function converges for all complex numbers $s$ where $\text{Re}(s) > 1$.

### Informal proof
This theorem is extracted as the first component of the conjunction `LOGZETA_PROPERTIES` using the `CONJUNCTS` function. 

The original conjunction is rewritten using several rules:
- `IN_ELIM_THM`: Eliminates set membership into its defining predicate
- `FORALL_AND_THM`: Distributes universal quantification over conjunction
- `real_gt`: Rewrites the "greater than" relation for real numbers
- A tautology that distributes implication over conjunction

These rewriting operations extract three separate theorems from `LOGZETA_PROPERTIES`:
1. `LOGZETA_CONVERGES`: States that the logarithm of the Riemann zeta function converges when the real part of s exceeds 1
2. `LOGZETA'_CONVERGES`: Related to the convergence of the derivative
3. `HAS_COMPLEX_DERIVATIVE_LOGZETA`: Related to the complex differentiability of the logarithm of zeta

This specific theorem represents the convergence property of the logarithm of the Riemann zeta function.

### Mathematical insight
The logarithm of the Riemann zeta function is an important function in analytic number theory. The convergence domain where $\text{Re}(s) > 1$ corresponds to the region where the Riemann zeta function itself is defined by its original series $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$. 

Taking the logarithm of the zeta function is a standard technique in analytic number theory, particularly in the study of prime numbers through the connection between the zeta function and the prime number theorem.

### Dependencies
The theorem is extracted from `LOGZETA_PROPERTIES` which likely contains the full statement and properties of the logarithm of the Riemann zeta function.

The extraction process uses:
- `CONJUNCTS`: Splits a conjunction into a list of its conjuncts
- `REWRITE_RULE`: Applies rewriting using the specified theorems
- `IN_ELIM_THM`: Handles set membership
- `FORALL_AND_THM`: Distributes universal quantification over conjunction
- `real_gt`: Defines the greater than relation for real numbers
- `TAUT`: Derives tautologies in propositional logic

### Porting notes
When porting this theorem to another system:
1. Ensure the Riemann zeta function is properly defined
2. Define the logarithm of the zeta function appropriately
3. Establish the convergence domain with proper complex analysis tools
4. The formal content here is mainly about extracting the theorem from a larger conjunction, so focus on the mathematical statement rather than the extraction process

---

## CEXP_LOGZETA

### Name of formal statement
CEXP_LOGZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CEXP_LOGZETA = prove
 (`!s. &1 < Re s ==> cexp(--(logzeta s)) = zeta s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. cexp(vsum({p | prime p} INTER (0..n))
                 (\p. --clog(Cx(&1) - inv(Cx(&p) cpow s))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`cexp`; `--logzeta s`] CONTINUOUS_AT_SEQUENTIALLY) THEN
    REWRITE_TAC[CONTINUOUS_AT_CEXP; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM sums] THEN
    MATCH_MP_TAC SERIES_NEG THEN ASM_SIMP_TAC[LOGZETA_CONVERGES];
    SIMP_TAC[CEXP_VSUM; FINITE_INTER_NUMSEG] THEN
    MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\n. cproduct {p | prime p /\ p <= n}
                             (\p. inv(Cx(&1) - inv(Cx(&p) cpow s)))` THEN
    ASM_SIMP_TAC[EULER_PRODUCT] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[VECTOR_SUB_EQ; numseg; LE_0] THEN
    REWRITE_TAC[SET_RULE `{x | P x} INTER {x | Q x} = {x | P x /\ Q x}`] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_ELIM_THM; CEXP_NEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CEXP_CLOG THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; REAL_OF_NUM_LT; RE_CX; REAL_ABS_NUM;
     COMPLEX_NORM_INV; PRIME_IMP_NZ; LT_NZ; COMPLEX_NORM_CX; REAL_EXP_EQ_1] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_EXP_0; GSYM REAL_EXP_NEG; REAL_EXP_INJ] THEN
    REWRITE_TAC[REAL_NEG_EQ_0; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 < s ==> ~(s = &0)`] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, we have:
$$\exp(-\log\zeta(s)) = \zeta(s)$$
where $\zeta(s)$ is the Riemann zeta function.

### Informal proof
We prove that for any complex number $s$ with $\text{Re}(s) > 1$, the equation $\exp(-\log\zeta(s)) = \zeta(s)$ holds.

The proof follows these main steps:
* We use the fact that $\lim$ is unique (with respect to the sequential topology).
* We show that both sides of our equation are limits of specific sequences.
* First, we prove that $\exp(-\log\zeta(s))$ is the limit of the sequence $\exp\left(\sum_{p \leq n, p \text{ prime}} -\log(1 - p^{-s})\right)$.
* For the left side:
  * We use continuity of the complex exponential function
  * Since $\log\zeta(s)$ converges (by `LOGZETA_CONVERGES`), so does $-\log\zeta(s)$
  * Thus $\exp(-\log\zeta(s))$ is the limit of $\exp$ applied to partial sums

* For the right side:
  * We use the Euler product formula (`EULER_PRODUCT`), which states that $\zeta(s) = \lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} \frac{1}{1-p^{-s}}$
  
* We then show that our two sequences are eventually equal:
  * We have $\exp\left(\sum_{p \leq n, p \text{ prime}} -\log(1 - p^{-s})\right) = \prod_{p \leq n, p \text{ prime}} \exp(-\log(1 - p^{-s}))$
  * For each prime $p$, we have $\exp(-\log(1 - p^{-s})) = \frac{1}{1 - p^{-s}}$
  * This follows from properties of complex exponential and logarithm, applied carefully while ensuring the logarithm is well-defined (checking that $1 - p^{-s} \neq 0$ for $\text{Re}(s) > 1$)
  
* Since both sides converge to the same limit, they must be equal.

### Mathematical insight
This theorem establishes a fundamental relationship between the Riemann zeta function and its logarithm. While the relationship $\exp(\log z) = z$ holds for most complex numbers, extra care is needed for functions like $\zeta(s)$ to ensure the logarithm is well-defined and the relationship holds.

This result is used in analytic number theory, particularly in prime number theory, as it connects the zeta function's logarithm with its Euler product representation. The logarithm of the zeta function plays an important role in the study of the distribution of prime numbers, as it relates directly to the von Mangoldt function and the prime counting function.

### Dependencies
- **Theorems**:
  - `EULER_PRODUCT`: The Euler product formula for the Riemann zeta function: $\zeta(s) = \lim_{n \to \infty} \prod_{p \leq n, p \text{ prime}} \frac{1}{1-p^{-s}}$ for $\text{Re}(s) > 1$
  - `LOGZETA_CONVERGES`: The logarithm of zeta converges for $\text{Re}(s) > 1$
  - `CEXP_VSUM`: Exponential of a sum equals product of exponentials
  - `CEXP_NEG`: $\exp(-z) = \frac{1}{\exp(z)}$
  - `CEXP_CLOG`: Complex exponential and logarithm are inverses
  - Various limit theorems and continuity properties

- **Definitions**:
  - `zeta`: The Riemann zeta function, defined as $\zeta(s) = \text{genzeta}(1, s)$

### Porting notes
When porting this theorem:
1. Ensure your proof assistant has proper complex analysis libraries, especially for complex exponential, logarithm and limits
2. The core of the proof uses the Euler product formula for the zeta function, which needs to be established first
3. Pay attention to how the domains are handled - particularly that $\text{Re}(s) > 1$ ensures the non-vanishing of terms in the Euler product
4. The sequence manipulation may require different approaches in other proof assistants, especially how limits are treated

---

## HAS_COMPLEX_DERIVATIVE_ZETA

### Name of formal statement
HAS_COMPLEX_DERIVATIVE_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s ==> (zeta has_complex_derivative
                      (--(logzeta'(s)) * zeta(s))) (at s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. cexp(--(logzeta s))` THEN EXISTS_TAC `Re s - &1` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_BALL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CEXP_LOGZETA THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
  ASM_SIMP_TAC[GSYM CEXP_LOGZETA; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_LOGZETA]);;
```

### Informal statement
For all complex numbers $s$ where $\operatorname{Re}(s) > 1$, the Riemann zeta function $\zeta(s)$ is complex differentiable at $s$ with derivative $-((\log \zeta)'(s)) \cdot \zeta(s)$.

Expressed in terms of complex differentiation:
$$\forall s. \operatorname{Re}(s) > 1 \Rightarrow \left(\zeta \text{ has complex derivative } -((\log \zeta)'(s)) \cdot \zeta(s)\right) \text{ at } s$$

### Informal proof
We prove that the Riemann zeta function is complex differentiable for $\operatorname{Re}(s) > 1$ and compute its derivative.

* First, we use the theorem `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` to relate $\zeta(s)$ to $\exp(-\log \zeta(s))$.
* We introduce the function $f(s) = \exp(-\log \zeta(s))$ and show that it equals $\zeta(s)$ in a neighborhood of radius $\operatorname{Re}(s) - 1$ around $s$.
  * For any point in this neighborhood, its real part remains greater than 1.
  * Within this neighborhood, we apply `CEXP_LOGZETA` which states that $\exp(-\log \zeta(s)) = \zeta(s)$ when $\operatorname{Re}(s) > 1$.

* Next, we compute the derivative by applying the chain rule (`COMPLEX_DIFF_CHAIN_AT`).
  * We express $f(s) = (\exp \circ (-\log \zeta))(s)$ and apply the chain rule.
  * The derivative of $\exp$ at any point $z$ is $\exp(z)$.
  * The derivative of $-\log \zeta(s)$ is $-(\log \zeta)'(s)$.
  * By the chain rule, the derivative of $f(s)$ is $\exp(-\log \zeta(s)) \cdot (-(\log \zeta)'(s))$.
  * Since $\exp(-\log \zeta(s)) = \zeta(s)$, the derivative equals $-(\log \zeta)'(s) \cdot \zeta(s)$.

Therefore, the complex derivative of the zeta function is $-((\log \zeta)'(s)) \cdot \zeta(s)$.

### Mathematical insight
This theorem establishes the complex differentiability of the Riemann zeta function in the region $\operatorname{Re}(s) > 1$ and provides a formula for its derivative. The result is significant because:

1. It shows that the zeta function is analytic in this region.
2. It provides an explicit formula for the derivative in terms of the logarithmic derivative of zeta.
3. The approach using $\exp(-\log \zeta(s))$ leverages the relationship between zeta and the Euler product representation, which is fundamental in analytic number theory.

The proof method illustrates how properties of the zeta function can be derived from its relationship with the exponential of the negative logarithm of zeta, which connects to the Euler product representation.

### Dependencies
- **Theorems**:
  - `CEXP_LOGZETA`: $\forall s. \operatorname{Re}(s) > 1 \Rightarrow \exp(-\log \zeta(s)) = \zeta(s)$
  - `HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT` (implicit)
  - `HAS_COMPLEX_DERIVATIVE_CEXP` (implicit)
  - `HAS_COMPLEX_DERIVATIVE_NEG` (implicit)
  - `HAS_COMPLEX_DERIVATIVE_LOGZETA` (implicit)

- **Definitions**:
  - `zeta`: The Riemann zeta function defined as $\zeta(s) = \operatorname{genzeta}(1, s)$

### Porting notes
When porting this theorem:
1. Ensure your target system has the necessary infrastructure for complex analysis, including complex differentiation.
2. You'll need equivalent theorems for complex differentiation, particularly chain rule and transformation theorems.
3. The relationship between zeta and $\exp(-\log \zeta(s))$ is crucial, so ensure `CEXP_LOGZETA` is ported first.
4. The definition of zeta may differ across systems. In HOL Light, it's defined using `genzeta` with parameter 1, which might not be standard in other systems.

---

## COMPLEX_DERIVATIVE_ZETA

### Name of formal statement
COMPLEX_DERIVATIVE_ZETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s
       ==> complex_derivative zeta s = --(logzeta'(s)) * zeta(s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_ZETA]);;
```

### Informal statement
For any complex number $s$ with real part $\text{Re}(s) > 1$, the complex derivative of the Riemann zeta function $\zeta$ at the point $s$ is given by:
$$\zeta'(s) = -\text{logzeta}'(s) \cdot \zeta(s)$$
where $\text{logzeta}'(s)$ is the complex derivative of the logarithm of the zeta function.

### Informal proof
The proof follows directly from the theorem `HAS_COMPLEX_DERIVATIVE_ZETA`, which states that for any $s$ with $\text{Re}(s) > 1$, the function $\zeta$ has complex derivative $-\text{logzeta}'(s) \cdot \zeta(s)$ at the point $s$.

To convert from the "has_complex_derivative" relation to the "complex_derivative" function, we apply the theorem `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`, which states that if a function has a complex derivative at a point, then that derivative equals the value of the complex_derivative function at that point.

### Mathematical insight
This theorem provides an explicit formula for the derivative of the Riemann zeta function in terms of the function itself and the derivative of its logarithm. This is a common pattern in complex analysis where the derivative of a function can be expressed in terms of the function and the derivative of its logarithm.

The result is valid only in the region where $\text{Re}(s) > 1$, which is the region of absolute convergence for the zeta function's standard series representation. Outside this region, the zeta function is defined by analytic continuation, and its derivative would need to be calculated differently.

This formula is useful for numerical computations of the zeta function's derivative and for theoretical investigations of the function's behavior.

### Dependencies
- Theorems:
  - `HAS_COMPLEX_DERIVATIVE_ZETA`: States that $\zeta$ has complex derivative $-\text{logzeta}'(s) \cdot \zeta(s)$ at $s$ when $\text{Re}(s) > 1$
  - `HAS_COMPLEX_DERIVATIVE_DERIVATIVE`: Relates the "has_complex_derivative" relation to the "complex_derivative" function

- Definitions:
  - `zeta`: The Riemann zeta function, defined as `zeta s = genzeta 1 s` where `genzeta` is a generalized version of the zeta function

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the Riemann zeta function and its logarithm are properly defined in the target system
2. Make sure that the complex derivative concept in the target system is compatible with HOL Light's definition
3. The dependency on `HAS_COMPLEX_DERIVATIVE_ZETA` suggests that you might need to port that theorem first, which involves more intricate properties of the zeta function

---

## CONVERGES_LOGZETA''

### CONVERGES_LOGZETA''
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CONVERGES_LOGZETA'' = prove
 (`!s. &1 < Re s
       ==> ((\p. Cx(log(&p)) / (Cx(&p) cpow s - Cx(&1))) sums
            (--(complex_derivative zeta s / zeta s))) {p | prime p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(complex_derivative zeta s / zeta s) = logzeta'(s)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_DERIVATIVE_ZETA; COMPLEX_FIELD
     `~(b = Cx(&0)) ==> (--(a / b) = c <=> a = --c * b)`];
    MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC `\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1))` THEN
    ASM_SIMP_TAC[LOGZETA'_CONVERGES; IN_ELIM_THM] THEN
    SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ]]);;
```

### Informal statement
For all complex numbers $s$ with real part $\operatorname{Re}(s) > 1$, the series
$$\sum_{p \text{ prime}} \frac{\log(p)}{p^s - 1}$$
converges to $-\frac{\zeta'(s)}{\zeta(s)}$, where $\zeta$ is the Riemann zeta function and $\zeta'$ is its complex derivative.

### Informal proof
The proof proceeds as follows:

* First, we show that $-\frac{\zeta'(s)}{\zeta(s)} = \log\zeta'(s)$ where $\log\zeta'$ is the complex derivative of the logarithm of the zeta function.
  * This uses `ZETA_NONZERO_LEMMA` which states that $\zeta(s) \neq 0$ when $\operatorname{Re}(s) > 1$, allowing us to safely divide by $\zeta(s)$.
  * We use `COMPLEX_DERIVATIVE_ZETA` and complex field operations to simplify the expression.

* Next, we show that the given series is equal to $\log\zeta'(s)$:
  * We apply `SUMS_EQ` to prove equivalence between two series.
  * We identify that the series $\sum_{p \text{ prime}} \frac{\log(p)}{p^s - 1}$ is equivalent to $\sum_{p \text{ prime}} \frac{\operatorname{clog}(p)}{p^s - 1}$, where $\operatorname{clog}$ is the complex logarithm function.
  * We use `LOGZETA'_CONVERGES` to establish the convergence of this series to $\log\zeta'(s)$.
  * Finally, we simplify by using `CX_LOG` to convert the complex logarithm to the real logarithm, which is valid because $p$ is a prime number and therefore positive.

### Mathematical insight
This theorem provides a beautiful connection between the Riemann zeta function and prime numbers. The expression $-\frac{\zeta'(s)}{\zeta(s)}$ is known as the logarithmic derivative of $\zeta(s)$, and this theorem shows it can be represented as a series involving only prime numbers.

This result is a key component of analytic number theory and is closely related to the Euler product formula for the zeta function. The theorem essentially gives a logarithmic derivative version of the Euler product, which relates the analytic properties of the zeta function to the distribution of prime numbers.

This formula is particularly significant in the study of the distribution of prime numbers and plays a fundamental role in the proof of the Prime Number Theorem.

### Dependencies
- **Theorems:**
  - `ZETA_NONZERO_LEMMA`: States that for $\operatorname{Re}(s) > 1$, the zeta function $\zeta(s) \neq 0$.
  - `COMPLEX_DERIVATIVE_ZETA`: Gives an explicit formula for the complex derivative of the zeta function.
  - `LOGZETA'_CONVERGES`: Establishes the convergence of a related series to $\log\zeta'(s)$.

- **Definitions:**
  - `zeta`: Riemann zeta function defined as `zeta s = genzeta 1 s`.

### Porting notes
When porting this theorem to another system:
1. Ensure that the Riemann zeta function and its properties are properly defined.
2. The relationship between the logarithmic derivative $-\frac{\zeta'(s)}{\zeta(s)}$ and the prime sum may be formulated differently in other systems.
3. Pay attention to how complex logarithms and complex powers are handled, as these can have different conventions in different systems.
4. The proof relies on the convergence of series over prime numbers, so ensure the system has appropriate machinery for handling such series.

---

## VALID_PATH_NEGATEPATH

### VALID_PATH_NEGATEPATH
- `VALID_PATH_NEGATEPATH`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VALID_PATH_NEGATEPATH = prove
 (`!g. valid_path g ==> valid_path ((--) o g)`,
  REWRITE_TAC[valid_path; o_DEF] THEN
  ASM_SIMP_TAC[PIECEWISE_DIFFERENTIABLE_NEG]);;
```

### Informal statement
For any function $g : \mathbb{R}^1 \to \mathbb{C}$, if $g$ is a valid path, then $(-) \circ g$ (the function that maps $t$ to $-g(t)$) is also a valid path.

Here, a valid path means a function that is piecewise differentiable on the interval $[0,1]$.

### Informal proof
The proof uses the definition of a valid path and applies a theorem about piecewise differentiability of negated functions.

First, we expand the definition of `valid_path`, which states that a function is a valid path if and only if it is piecewise differentiable on the interval $[0,1]$.

Then we apply the theorem `PIECEWISE_DIFFERENTIABLE_NEG`, which states that if a function $f$ is piecewise differentiable on a set $s$, then the function $x \mapsto -f(x)$ is also piecewise differentiable on $s$.

Since $g$ is piecewise differentiable on $[0,1]$ (by the assumption that $g$ is a valid path), it follows that $(-) \circ g$ is also piecewise differentiable on $[0,1]$, and therefore $(-) \circ g$ is a valid path.

### Mathematical insight
This theorem shows that negating a valid path preserves the property of being a valid path. In complex analysis and the theory of path integrals, valid paths are important objects of study, and this theorem establishes that the set of valid paths is closed under negation.

The result is part of a collection of theorems about operations on paths (like negation, composition, etc.) that preserve the property of being a valid path, which is crucial for manipulating path integrals and applying various theorems in complex analysis.

### Dependencies
- **Theorems**:
  - `PIECEWISE_DIFFERENTIABLE_NEG`: If a function is piecewise differentiable on a set, then its negation is also piecewise differentiable on that set.

- **Definitions**:
  - `valid_path`: A function $f : \mathbb{R}^1 \to \mathbb{C}$ is a valid path if and only if $f$ is piecewise differentiable on the interval $[0,1]$.

### Porting notes
When porting this theorem to another system, you need to:
1. Ensure that the concept of "valid path" is defined as a piecewise differentiable function on $[0,1]$.
2. Check that the corresponding theorem about piecewise differentiability of negated functions is available or can be proven.
3. Be careful with function composition notation, as different systems may have different conventions.

---

## PATHSTART_NEGATEPATH

### PATHSTART_NEGATEPATH
- PATHSTART_NEGATEPATH

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATHSTART_NEGATEPATH = prove
 (`!g. pathstart((--) o g) = --(pathstart g)`,
  REWRITE_TAC[pathstart; o_THM]);;
```

### Informal statement
For any path $g$, the starting point of the negated path $(-) \circ g$ equals the negation of the starting point of $g$. In symbols:
$$\forall g. \text{pathstart}((-) \circ g) = -(\text{pathstart}(g))$$

where:
- $g$ is a path (typically a continuous function from a real interval to a space)
- $\text{pathstart}(g)$ denotes the starting point of the path $g$
- $(-)$ denotes the negation operation
- $\circ$ represents function composition

### Informal proof
The proof uses rewriting with the definitions of `pathstart` and function composition.

First, by definition, `pathstart g` is the value of $g$ at its starting point, typically $g(0)$ or the evaluation of $g$ at the lower bound of its domain.

When we apply the composition $((-) \circ g)$ to the starting point, this equals $-(g(\text{start}))$, which is precisely $-(\text{pathstart}(g))$.

The proof is completed by applying the rewriting tactic with the definitions of `pathstart` and `o_THM` (function composition).

### Mathematical insight
This theorem establishes a basic property about the relationship between path negation and the starting point of a path. It's a straightforward but useful result for path manipulation in topology and analysis.

The result shows that negating a path is equivalent to taking the same path but with all points negated, which means the starting point is also negated. This preserves the expected relationship between operators and path endpoints.

### Dependencies
- Definitions:
  - `pathstart`: Defines the starting point of a path
  - `o_THM`: Theorem about function composition

### Porting notes
When porting this theorem, ensure that the target system has appropriate definitions for paths and their starting points. The theorem itself is straightforward, but ensure that the negation operation and function composition are properly defined for the types of objects representing paths in the target system.

---

## PATHFINISH_NEGATEPATH

### PATHFINISH_NEGATEPATH
- PATHFINISH_NEGATEPATH

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATHFINISH_NEGATEPATH = prove
 (`!g. pathfinish((--) o g) = --(pathfinish g)`,
  REWRITE_TAC[pathfinish; o_THM]);;
```

### Informal statement
For any path $g$, the endpoint of the negated path $(-) \circ g$ equals the negation of the endpoint of the original path $g$. That is:
$$\forall g. \text{pathfinish}((-) \circ g) = -(\text{pathfinish}(g))$$

Where:
- $g$ is a path (a continuous function from a closed interval to a topological space)
- $\text{pathfinish}(g)$ denotes the endpoint of path $g$
- $((-) \circ g)$ represents the composition of the negation function with $g$, giving a path whose value at each point is the negative of the original path's value

### Informal proof
The proof is straightforward using the definition of `pathfinish` and the properties of function composition:

- By the definition of `pathfinish`, the endpoint of a path is the value of the path at its ending parameter.
- Using the definition of function composition, for any path $g$, we have:
  $$\text{pathfinish}((-) \circ g) = ((-) \circ g)(\text{pathfinish parameter}) = -(g(\text{pathfinish parameter})) = -(\text{pathfinish}(g))$$
- The proof is completed by applying these definitions and simplifying.

### Mathematical insight
This theorem establishes a basic property relating path endpoints with path negation. It confirms the intuitively expected result that if we negate all points along a path, the endpoint of this negated path will be the negation of the original path's endpoint.

This property is important in path theory and algebraic topology, where operations on paths (like negation, which corresponds to traversing a path in the opposite direction) need to behave consistently with operations on their endpoints. This theorem shows that negation of paths commutes with taking endpoints.

### Dependencies
- Definitions:
  - `pathfinish`: Definition of the endpoint of a path
  - `o_THM`: Theorem about function composition

### Porting notes
This theorem should be straightforward to port to other systems. The main requirement is having:
1. A proper definition of paths and the `pathfinish` operation
2. Function composition and negation operations
3. Rewriting capabilities to substitute definitions and simplify expressions

---

## PATH_IMAGE_NEGATEPATH

### PATH_IMAGE_NEGATEPATH
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATH_IMAGE_NEGATEPATH = prove
 (`!g. path_image((--) o g) = IMAGE (--) (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;
```

### Informal statement
For any path $g$, the path image of the negative of $g$ (i.e., $(-) \circ g$) is equal to the image of the negation function applied to the path image of $g$.

Formally:
$$\forall g. \text{path\_image}((-) \circ g) = \text{IMAGE}((-), \text{path\_image}(g))$$

Where:
- $\text{path\_image}(g)$ represents the set of points traversed by the path $g$
- $(-) \circ g$ represents the composition of the negation function with the path $g$
- $\text{IMAGE}((-), S)$ represents the image of the set $S$ under the negation function

### Informal proof
The proof is straightforward by rewriting using the definitions:

- We apply `REWRITE_TAC` with the definition of `path_image` and the property of function composition on images (`IMAGE_o`).
- This expands `path_image((--) o g)` according to its definition.
- The composition of negation with the path can be rewritten using `IMAGE_o`, which allows us to express the composition of functions applied to an image in terms of the composition of the functions.
- After these rewrites, the two sides of the equation become syntactically identical.

### Mathematical insight
This theorem establishes that taking the negative of a path and then finding its image is equivalent to finding the image of the original path and then taking the negative of each point in that image.

This result relates to the geometric intuition that reflecting a path through the origin produces a path whose points are exactly the reflections of the points in the original path. This is a natural property we would expect from path images and the negation operation.

### Dependencies
- Definitions:
  - `path_image`: Defines the set of points traversed by a path
  - `IMAGE_o`: A theorem about the composition of functions applied to image sets

### Porting notes
This result should be straightforward to port to other systems, as it relies only on basic properties of functions, images, and composition. The main consideration is ensuring that the path image and function composition are defined consistently with HOL Light's definitions.

---

## HAS_PATH_INTEGRAL_NEGATEPATH

### Name of formal statement
HAS_PATH_INTEGRAL_NEGATEPATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_PATH_INTEGRAL_NEGATEPATH = prove
 (`!g z. valid_path g /\ ((\z. f(--z)) has_path_integral (--i)) g
         ==> (f has_path_integral i) ((--) o g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_path_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[valid_path; piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[NEGLIGIBLE_FINITE] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[o_DEF; GSYM COMPLEX_MUL_RNEG] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS; DIFFERENTIABLE_AT_WITHIN]);;
```

### Informal statement
For a valid path $g$ and a complex function $f$, if the function $z \mapsto f(-z)$ has path integral $-i$ along the path $g$, then the function $f$ has path integral $i$ along the path $-g$ (i.e., the composition of negation and $g$).

Formally, for any path $g$ and complex number $i$:
$$\text{valid\_path}(g) \land \left(\lambda z.f(-z) \text{ has\_path\_integral } (-i)\right)(g) \Rightarrow \left(f \text{ has\_path\_integral } i\right)((-) \circ g)$$

### Informal proof
We'll prove that if $g$ is a valid path and $f(-z)$ has path integral $-i$ along $g$, then $f$ has path integral $i$ along $-g$.

1. First, we expand the definition of `has_path_integral`:
   - For $f(-z)$ having path integral $-i$ along $g$, this means:
     $$\int_0^1 f(-g(t)) \cdot g'(t) \, dt = -i$$
   - For $f$ having path integral $i$ along $-g$, we need to show:
     $$\int_0^1 f((-)(g(t))) \cdot (-g)'(t) \, dt = i$$

2. By applying `HAS_INTEGRAL_NEG` to the first condition and simplifying using $--i = i$, we need to show the integrands are equal almost everywhere.

3. Since $g$ is a valid path, it is piecewise differentiable on $[0,1]$, meaning:
   - $g$ is continuous on $[0,1]$
   - There exists a finite set $s$ such that $g$ is differentiable at all points in $[0,1] \setminus s$

4. For any point $t \in [0,1] \setminus s$ where $g$ is differentiable, we can show:
   - $f((-)(g(t))) \cdot (-g)'(t) = f(-g(t)) \cdot (-g'(t)) = -f(-g(t)) \cdot g'(t)$
   - Using the complex multiplication property: $-f(-g(t)) \cdot g'(t) = -(-f(g(t)) \cdot g'(t))$

5. Therefore, the integrands are equal almost everywhere (differing only on a negligible set), so the theorem follows.

### Mathematical insight
This theorem establishes a relationship between path integrals along a path and its negative counterpart. It demonstrates how reversing the orientation of a path affects the path integral. Specifically, this result is part of the theory of complex path integrals, which are fundamental in complex analysis.

The key insight is that when we negate the path, the derivative of the negated path is the negative of the original path's derivative. This, combined with the substitution $z \mapsto -z$ in the function, leads to a sign change in the path integral.

This theorem is particularly useful in contour integration where we might need to relate integrals along paths with different orientations or to establish properties like Cauchy's integral formula.

### Dependencies
#### Definitions
- `piecewise_differentiable_on`: A function is piecewise differentiable on a set if it is continuous on the set and differentiable at all points except for a finite set.
- `valid_path`: A path is valid if it is piecewise differentiable on the interval [0,1].
- `has_path_integral`: Defines when a function has a specific path integral along a given path.

#### Theorems
- `HAS_INTEGRAL_NEG`: Relates the integral of a negated function to the negation of the original integral.
- `HAS_INTEGRAL_SPIKE_EQ`: Allows replacing integrands that are equal almost everywhere.
- `VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL`: Relates vector derivatives within a closed interval.
- `HAS_VECTOR_DERIVATIVE_NEG`: Relates the vector derivative of a negated function to the negation of the original derivative.

### Porting notes
When porting this theorem:
1. Ensure that your target system has a well-defined notion of path integrals in complex analysis
2. Pay attention to the handling of composition and negation operations, as these might have different syntax in other systems
3. Be prepared to establish equivalents for the auxiliary theorems about integrals and derivatives
4. The proof relies on properties of negligible sets and almost-everywhere equality, which might need different handling in other systems

---

## WINDING_NUMBER_NEGATEPATH

### WINDING_NUMBER_NEGATEPATH
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WINDING_NUMBER_NEGATEPATH = prove
 (`!g z. valid_path g /\ ~(Cx(&0) IN path_image g)
         ==> winding_number((--) o g,Cx(&0)) = winding_number(g,Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; VALID_PATH_NEGATEPATH;
               PATH_IMAGE_NEGATEPATH; IN_IMAGE; UNWIND_THM2;
               COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN
  ASM_REWRITE_TAC[COMPLEX_RING `--z - Cx(&0) = --(z - Cx(&0))`] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_RNEG] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  ASM_SIMP_TAC[GSYM complex_div; PATH_INTEGRABLE_INVERSEDIFF]);;
```

### Informal statement
For any valid path $g$ such that $0$ is not in the path image of $g$, the winding number of the negated path $(-) \circ g$ around $0$ equals the winding number of the original path $g$ around $0$. Formally:

$$\forall g, z. \text{valid\_path}(g) \land 0 \notin \text{path\_image}(g) \Rightarrow \text{winding\_number}((-) \circ g, 0) = \text{winding\_number}(g, 0)$$

where $(-) \circ g$ represents the composition of the negation function with the path $g$.

### Informal proof
We prove that the winding number remains the same when a path is negated, provided 0 is not on the path.

* Apply `WINDING_NUMBER_VALID_PATH` to express both winding numbers in terms of path integrals:
  $$\text{winding\_number}(g, 0) = \frac{1}{2\pi i} \cdot \text{path\_integral}(g, \lambda w. \frac{1}{w})$$
  $$\text{winding\_number}((-) \circ g, 0) = \frac{1}{2\pi i} \cdot \text{path\_integral}((-) \circ g, \lambda w. \frac{1}{w})$$

* Note that $(-) \circ g$ is a valid path by `VALID_PATH_NEGATEPATH` and $0$ is not in its path image as $0$ is not in the path image of $g$.

* To show equality, it suffices to prove that the path integrals are equal.

* Apply `HAS_PATH_INTEGRAL_NEGATEPATH` to relate the path integral over $(-) \circ g$ to a path integral over $g$.

* For the negated path, observe that $\frac{1}{-z} = -\frac{1}{z}$ (using `COMPLEX_INV_NEG`).

* Apply `HAS_PATH_INTEGRAL_NEG` to handle the negation in the integrand.

* Finally, use `HAS_PATH_INTEGRAL_INTEGRAL` and `PATH_INTEGRABLE_INVERSEDIFF` to confirm that the function $\lambda w. \frac{1}{w}$ is path integrable on $g$.

* The path integrals are equal, and therefore the winding numbers are equal.

### Mathematical insight
This theorem establishes an important invariant property of the winding number: it remains unchanged when a path is negated. Intuitively, this makes sense because negating a path essentially reflects it through the origin, which does not change how many times the path winds around the origin (though it does reverse the direction of travel).

This property is useful in complex analysis, particularly when manipulating contour integrals. It allows us to transform paths by negation while preserving winding numbers, which simplifies certain calculations and proofs.

The theorem is part of a collection of results that establish how winding numbers behave under various path transformations.

### Dependencies
- Theorems:
  - `WINDING_NUMBER_VALID_PATH`: Expresses the winding number in terms of a path integral
  - `VALID_PATH_NEGATEPATH`: Establishes that negating a valid path produces a valid path
  - `PATH_IMAGE_NEGATEPATH`: Describes the path image of a negated path
  - `HAS_PATH_INTEGRAL_NEGATEPATH`: Relates path integrals over negated paths
  - `HAS_PATH_INTEGRAL_NEG`: Handles negation of the integrand in path integrals
  - `HAS_PATH_INTEGRAL_INTEGRAL`: Connects path integrability to having a path integral
  - `PATH_INTEGRABLE_INVERSEDIFF`: Shows that the function $\lambda w. \frac{1}{w-z}$ is path integrable
  - `PATH_INTEGRAL_UNIQUE`: Establishes uniqueness of path integrals

- Definitions:
  - `valid_path`: A path that is piecewise differentiable on [0,1]
  - `winding_number`: Number of times a path winds around a point

### Porting notes
When porting this theorem:
1. Ensure your system has an appropriate definition of winding number that matches HOL Light's construction.
2. Verify the path negation operation is well-defined in your target system.
3. The complex arithmetic may need explicit handling depending on how the target system represents complex numbers.
4. The path integral theorems are critical dependencies - ensure they're ported with consistent behavior.
5. Some automated reasoning in HOL Light (like `COMPLEX_RING`) may need to be manually proven in other systems.

---

## PATH_INTEGRABLE_NEGATEPATH

### PATH_INTEGRABLE_NEGATEPATH

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATH_INTEGRABLE_NEGATEPATH = prove
 (`!g z. valid_path g /\ (\z. f(--z)) path_integrable_on g
         ==> f path_integrable_on ((--) o g)`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_NEGATEPATH; COMPLEX_NEG_NEG]);;
```

### Informal statement
For any path $g$ and complex number $z$, if $g$ is a valid path and the function $z \mapsto f(-z)$ is path integrable on $g$, then the function $f$ is path integrable on the path $(-) \circ g$ (the composition of negation with $g$).

Formally:
$$\forall g, z. \text{valid\_path}(g) \wedge ((z \mapsto f(-z)) \text{ path\_integrable\_on } g) \Rightarrow (f \text{ path\_integrable\_on } ((-) \circ g))$$

### Informal proof
The proof follows directly from the definitions and previously established theorems:

1. We first rewrite using the definition of `path_integrable_on`, which states that a function is path integrable on a path if there exists a value that is the path integral of the function along that path.

2. Then we use `HAS_PATH_INTEGRAL_NEGATEPATH`, which states that if $g$ is a valid path and $z \mapsto f(-z)$ has a path integral $-i$ along $g$, then $f$ has a path integral $i$ along $(-) \circ g$.

3. Combined with the fact that $--i = i$ (double negation of a complex number equals the original number), we can establish that if $z \mapsto f(-z)$ is path integrable on $g$, then $f$ is path integrable on $(-) \circ g$.

The proof is completed using the MESON tactic, which automates the logical reasoning steps.

### Mathematical insight
This theorem establishes a relationship between path integrals along a path and along its negation. It shows that if we can integrate a modified function ($z \mapsto f(-z)$) along a path $g$, then we can also integrate the original function $f$ along the negated path $(-) \circ g$.

This result is useful in complex analysis when manipulating contour integrals and establishing properties like symmetry or antisymmetry of path integrals under path reversal or transformation.

The theorem demonstrates how path integrability is preserved under certain transformations of both the integrand and the path of integration, which is a fundamental property in the theory of complex integration.

### Dependencies
- Theorems:
  - `HAS_PATH_INTEGRAL_NEGATEPATH`: Relates the path integral of $f$ along $(-) \circ g$ to the path integral of $z \mapsto f(-z)$ along $g$.
  - `COMPLEX_NEG_NEG`: The double negation of a complex number equals the original number.

- Definitions:
  - `valid_path`: A path is valid if it is piecewise differentiable on the interval $[0,1]$.
  - `path_integrable_on`: A function is path integrable on a path if there exists a value that is the path integral of the function along that path.

### Porting notes
When porting to other proof assistants:
- Ensure the target system has corresponding definitions for path integrals and valid paths in complex analysis
- The composition operator `(-)` represents the negation function in HOL Light. Make sure this is correctly translated to the target system's composition notation
- The proof relies on automated reasoning (MESON tactic), which may need to be replaced by more explicit steps in systems with different automation capabilities

---

## BOUND_LEMMA_0

### BOUND_LEMMA_0
- BOUND_LEMMA_0

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BOUND_LEMMA_0 = prove
 (`!z R. norm(z) = R
         ==> Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  ASM_REWRITE_TAC[complex_div; GSYM COMPLEX_ADD_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_CNJ; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_INV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[CX_MUL; CX_DIV; CX_POW; complex_div; GSYM COMPLEX_MUL_ASSOC]);;
```

### Informal statement
For all complex numbers $z$ and positive real numbers $R$, if $|z| = R$, then:

$$\frac{1}{z} + \frac{z}{R^2} = \frac{2 \cdot \text{Re}(z)}{R^2}$$

where $\text{Re}(z)$ denotes the real part of the complex number $z$.

### Informal proof
We begin with the assumption that $|z| = R$.

First, we rewrite the left-hand side using the definition of complex division:
$$\frac{1}{z} + \frac{z}{R^2} = 1 \cdot z^{-1} + \frac{z}{R^2}$$

Rewriting again in terms of complex division and using the relation between complex inversion and conjugation (where $z^{-1} = \frac{\bar{z}}{|z|^2}$):
$$1 \cdot z^{-1} + \frac{z}{R^2} = \frac{\bar{z}}{|z|^2} + \frac{z}{R^2}$$

Since $|z| = R$, we get:
$$\frac{\bar{z}}{R^2} + \frac{z}{R^2} = \frac{\bar{z} + z}{R^2}$$

Now we use the fact that $\bar{z} + z = 2 \cdot \text{Re}(z)$:
$$\frac{\bar{z} + z}{R^2} = \frac{2 \cdot \text{Re}(z)}{R^2}$$

This completes the proof.

### Mathematical insight
This lemma establishes a useful identity for complex numbers on a circle of radius $R$. The formula shows how the sum of reciprocal and scaled value of a complex number on this circle can be simplified to an expression involving only the real part. This is a key step in contour integration techniques, particularly in residue calculus.

The lemma appears to be one of several "bounding lemmas" attributed to Newman, as mentioned in the comment. Such identities are often crucial in complex analysis when establishing bounds for integrals along specific contours.

### Dependencies
- Complex number arithmetic properties
- Relationship between complex conjugation and inversion
- Properties of complex norm

### Porting notes
When porting this theorem to another proof assistant:
- Ensure that the complex number theory has a defined real part function
- Verify that the complex division operation is properly defined as multiplication by the inverse
- Check that the relationship between complex conjugation and inversion is established

---

## BOUND_LEMMA_1

### Name of formal statement
BOUND_LEMMA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_1 = prove
 (`!z R. norm(z) = R
         ==> norm(Cx(&1) / z + z / Cx(R) pow 2) = &2 * abs(Re z) / R pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BOUND_LEMMA_0; COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_MESON_TAC[NORM_ARITH `norm z = R ==> abs R = R`]);;
```

### Informal statement
For any complex number $z$ and real number $R$, if $\|z\| = R$, then 
$$\left\|\frac{1}{z} + \frac{z}{R^2}\right\| = \frac{2|\text{Re}(z)|}{R^2}$$
where $\|z\|$ denotes the complex norm of $z$, and $\text{Re}(z)$ denotes the real part of $z$.

### Informal proof
Given $z$ and $R$ where $\|z\| = R$, we proceed as follows:

* First, we apply the previously proven lemma `BOUND_LEMMA_0`, which states that if $\|z\| = R$, then:
  $$\frac{1}{z} + \frac{z}{R^2} = \frac{2\text{Re}(z)}{R^2}$$

* Applying the complex norm to both sides and using the fact that $\|c\| = |c|$ for any complex number $c$ represented as a real constant, we get:
  $$\left\|\frac{1}{z} + \frac{z}{R^2}\right\| = \left\|\frac{2\text{Re}(z)}{R^2}\right\| = \frac{2|\text{Re}(z)|}{R^2}$$

* In the last step, we use standard properties of absolute values:
  - $|a \cdot b| = |a| \cdot |b|$
  - $|a/b| = |a|/|b|$
  - $|a^n| = |a|^n$
  - $|n| = n$ for positive integers $n$

* Finally, we use the fact that if $\|z\| = R$, then $|R| = R$ (since the norm is always non-negative).

### Mathematical insight
This lemma establishes an important norm identity for complex numbers. It shows how the norm of a specific combination of a complex number and its inverse relates to the real part of the number. 

The expression $\frac{1}{z} + \frac{z}{R^2}$ appears in various complex analysis contexts, particularly when working with conformal mappings or when analyzing the behavior of complex functions near singularities. The identity provides a clean and exact expression for the norm of this sum in terms of the real part of $z$.

This lemma builds on `BOUND_LEMMA_0`, which established the algebraic identity, by extending it to the norm relation.

### Dependencies
#### Theorems
- `BOUND_LEMMA_0`: Establishes that if $\|z\| = R$, then $\frac{1}{z} + \frac{z}{R^2} = \frac{2\text{Re}(z)}{R^2}$
- `COMPLEX_NORM_CX`: Relates the norm of a complex number represented as a real constant to the absolute value of that constant
- `REAL_ABS_MUL`, `REAL_ABS_DIV`, `REAL_ABS_POW`, `REAL_ABS_NUM`: Basic properties of real absolute value
- `NORM_ARITH`: Arithmetic properties of norms

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the complex number representation and norm function are compatible with the source system
2. The proof relies on a prior lemma (`BOUND_LEMMA_0`), so that result should be ported first
3. The `ASM_MESON_TAC` step at the end uses automated reasoning - you may need to explicitly prove that if $\|z\| = R$, then $|R| = R$ in systems with less automation

---

## BOUND_LEMMA_2

### BOUND_LEMMA_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_2 = prove
 (`!R x z. Re(z) = --x /\ abs(Im(z)) = R /\ &0 <= x /\ &0 < R
           ==> norm (Cx (&1) / z + z / Cx R pow 2) <= &2 * x / R pow 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_LE_SQUARE; COMPLEX_SQNORM; DOT_SQUARE_NORM] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
  ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  REWRITE_TAC[complex_div] THEN
  SUBST1_TAC(SPEC `z:complex` COMPLEX_INV_CNJ) THEN
  ASM_SIMP_TAC[cnj; RE; IM; COMPLEX_MUL_LID; REAL_LE_MUL; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_POW; COMPLEX_SQNORM; RE; IM] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`] THEN
  REWRITE_TAC[GSYM CX_INV; complex_div] THEN
  REWRITE_TAC[complex_mul; complex_add; RE; IM; RE_CX; IM_CX;
              REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`;
   REAL_RING `(--x * a + --x * b:real) pow 2 = x pow 2 * (a + b) pow 2`;
   REAL_RING `(--R * a + R * b:real) pow 2 = R pow 2 * (b - a) pow 2`] THEN
  SUBGOAL_THEN `&0 < x pow 2 + R pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im z pow 2 = R pow 2` SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
   `&0 < R pow 2 /\ &0 < x pow 2 + R pow 2
    ==> x pow 2 * (inv (x pow 2 + R pow 2) + inv (R pow 2)) pow 2 +
        R pow 2 * (inv (R pow 2) - inv (x pow 2 + R pow 2)) pow 2 =
        (x pow 4 + &5 * R pow 2 * x pow 2 + &4 * R pow 4) /
        (x pow 2 + R pow 2) pow 2 *
        (x pow 2 / R pow 4)`] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
  `&0 < R pow 2 ==> (&2 * x / R pow 2) pow 2 = &4 * x pow 2 / R pow 4`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LT_IMP_LE]);;
```

### Informal statement
For any real numbers $R$ and $x$, and a complex number $z$ such that:
- $\text{Re}(z) = -x$
- $|\text{Im}(z)| = R$
- $0 \leq x$
- $0 < R$

Then: $\left\|\frac{1}{z} + \frac{z}{R^2}\right\| \leq \frac{2x}{R^2}$

### Informal proof
We begin by converting the norm inequality to an equivalent inequality about the square of the norm, and using properties of complex numbers:

* First, we rewrite the goal as $\|1/z + z/R^2\|^2 \leq (2x/R^2)^2$ using `NORM_LE_SQUARE`.

* For a complex number, we have $\|z\|^2 = \text{Re}(z)^2 + \text{Im}(z)^2$, which we apply.

* We note that $0 \leq 2x$ is equivalent to $0 \leq x$, which is given as a hypothesis.

* For any complex number $z$, we have $z^{-1} = \overline{z}/\|z\|^2$. We substitute this.

* Since $\text{Re}(z) = -x$ and $|\text{Im}(z)| = R$, we have $\overline{z} = -x - i\cdot\text{Im}(z)$.

* We know that $\|z\|^2 = x^2 + R^2$ since $\text{Re}(z)^2 = (-x)^2 = x^2$ and $\text{Im}(z)^2 = R^2$ (from $|\text{Im}(z)| = R$).

* After expanding and simplifying the complex arithmetic, we derive:
  $$\left\|\frac{1}{z} + \frac{z}{R^2}\right\|^2 = \frac{x^4 + 5R^2x^2 + 4R^4}{(x^2 + R^2)^2} \cdot \frac{x^2}{R^4}$$

* The square of our target bound is $(2x/R^2)^2 = 4x^2/R^4$.

* To complete the proof, we need to show:
  $$\frac{x^4 + 5R^2x^2 + 4R^4}{(x^2 + R^2)^2} \leq 4$$

* This simplifies to showing $x^4 + 5R^2x^2 + 4R^4 \leq 4(x^2 + R^2)^2 = 4x^4 + 8x^2R^2 + 4R^4$.

* Rearranging: $x^4 + 5R^2x^2 + 4R^4 \leq 4x^4 + 8R^2x^2 + 4R^4$,
  which is equivalent to $x^4 + 5R^2x^2 \leq 4x^4 + 8R^2x^2$,
  or $0 \leq 3x^4 + 3R^2x^2$,
  which is clearly true since $x \geq 0$ and $R > 0$.

### Mathematical insight
This lemma establishes an upper bound on the norm of the sum $\frac{1}{z} + \frac{z}{R^2}$ when $z$ has a specific form with real part $-x$ and imaginary part with magnitude $R$. This type of bound is often useful in complex analysis, particularly in contour integration and estimates involving complex functions.

The proof technique uses algebraic manipulations of complex numbers and careful handling of the inequalities, showing how the constraints on $x$ and $R$ lead to the desired bound. The lemma serves as a technical step in larger proofs involving complex analysis.

### Dependencies
- Complex arithmetic operations: `complex_div`, `complex_mul`, `complex_add`, `cnj`, `COMPLEX_INV_CNJ`
- Complex number properties: `COMPLEX_SQNORM`, `RE`, `IM`, `NORM_LE_SQUARE`, `DOT_SQUARE_NORM`
- Real number properties: `REAL_POW_LT`, `REAL_LE_DIV`, `REAL_LE_MUL`, `REAL_POW_LE`, `REAL_LE_SQUARE`

### Porting notes
When porting this theorem:
- Ensure that complex number operations (especially conjugation and division) are defined consistently with HOL Light
- Be careful with the square norm equivalence, which may be defined differently in other systems
- The proof relies heavily on algebraic manipulation and simplification, which might require different tactics in other proof assistants

---

## BOUND_LEMMA_3

### BOUND_LEMMA_3
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BOUND_LEMMA_3 = prove
 (`!a n. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
         1 <= n /\ &1 <= Re w /\ &0 < Re z
         ==> norm(vsum(1..n) (\n. a(n) / Cx(&n) cpow (w - z)))
                  <= exp(Re(z) * log(&n)) * (&1 / &n + &1 / Re(z))`,
  let lemma1 = prove
   (`!n x.
          &1 <= x
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n + &1)) / x`,
    REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `1`; `n:num`]
    SUM_INTEGRAL_UBOUND_INCREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < n <=> 1 <= n`;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[CPOW_1] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC)
  and lemma1' = prove
   (`!n x.
          &0 < x /\ x <= &1
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n)) / x`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_EXP_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; ARITH] THEN
    ASM_CASES_TAC `2 <= n` THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
      SUBGOAL_THEN `n = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; real_div; REAL_MUL_LID;
                   REAL_ADD_RID; REAL_INV_1_LE]] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `2`; `n:num`]
    SUM_INTEGRAL_UBOUND_DECREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o
            GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - x) * a <= (&1 - x) * b ==> (x - &1) * b <= (x - &1) * a`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x = y /\ &1 + u <= v ==> x <= u ==> &1 + y <= v`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[CPOW_1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= i ==> 0 < i`] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 + a - x <= a`) THEN
    ASM_SIMP_TAC[REAL_INV_1_LE; real_div; REAL_MUL_LID]) in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\n. exp((Re(z) - &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; ARITH_RULE `0 < k <=> 1 <= k`] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; GSYM RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_SUB] THEN UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  DISJ_CASES_TAC(ARITH_RULE `x <= &1 \/ &1 <= x`) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&n)) / x` THEN
    ASM_SIMP_TAC[lemma1'] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `x <= a + x <=> &0 <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_LE_INV_EQ; REAL_POS];
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= x * a /\ c <= x * d ==> c + b <= x * (a + d)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_LID; EXP_LOG; REAL_OF_NUM_LT;
                   ARITH_RULE `0 < n <=> 1 <= n`; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&(n - 1) + &1)) / x` THEN CONJ_TAC THEN
    ASM_SIMP_TAC[lemma1] THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> n - 1 + 1 = n`] THEN
    REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LID]]);;
```

### Informal statement
For any sequence $a$ and positive integer $n$, if:
- $\|a(m)\| \leq 1$ for all integers $m \geq 1$,
- $n \geq 1$,
- $\text{Re}(w) \geq 1$, and
- $\text{Re}(z) > 0$,

then:

$$\left\|\sum_{k=1}^{n} \frac{a(k)}{k^{w-z}}\right\| \leq e^{\text{Re}(z) \cdot \log(n)} \cdot \left(\frac{1}{n} + \frac{1}{Re(z)}\right)$$

### Informal proof
The proof establishes a bound on the norm of a complex sum through a series of estimates.

First, two key lemmas are established:

**Lemma 1**: For any real $x \geq 1$ and natural number $n$:
$$\sum_{k=1}^{n} e^{(x-1)\log(k)} \leq \frac{e^{x \cdot \log(n+1)}}{x}$$

**Lemma 1'**: For any real $x$ with $0 < x \leq 1$ and natural number $n$:
$$\sum_{k=1}^{n} e^{(x-1)\log(k)} \leq \frac{e^{x \cdot \log(n)}}{x}$$

For the main proof:
1. We begin by bounding the norm of the sum by the sum of the norms:
   $$\left\|\sum_{k=1}^{n} \frac{a(k)}{k^{w-z}}\right\| \leq \sum_{k=1}^{n} \left\|\frac{a(k)}{k^{w-z}}\right\|$$

2. For each term in the sum:
   $$\left\|\frac{a(k)}{k^{w-z}}\right\| = \frac{\|a(k)\|}{\|k^{w-z}\|} \leq \frac{1}{k^{\text{Re}(w-z)}} = \frac{1}{k^{\text{Re}(w)-\text{Re}(z)}}$$

3. Since $\text{Re}(w) \geq 1$, we have $\text{Re}(w)-\text{Re}(z) \geq 1-\text{Re}(z)$, so:
   $$\frac{1}{k^{\text{Re}(w)-\text{Re}(z)}} \leq \frac{1}{k^{1-\text{Re}(z)}} = e^{(Re(z)-1)\log(k)}$$

4. Thus:
   $$\left\|\sum_{k=1}^{n} \frac{a(k)}{k^{w-z}}\right\| \leq \sum_{k=1}^{n} e^{(Re(z)-1)\log(k)}$$

5. Introduce $x = \text{Re}(z)$ and consider two cases:
   
   **Case 1**: $x \leq 1$
   - Using Lemma 1', we get:
     $$\sum_{k=1}^{n} e^{(x-1)\log(k)} \leq \frac{e^{x \cdot \log(n)}}{x}$$

   **Case 2**: $x \geq 1$
   - Split the sum into two parts and apply appropriate bounds, yielding:
     $$\sum_{k=1}^{n} e^{(x-1)\log(k)} \leq e^{x \cdot \log(n)} \cdot \left(\frac{1}{n} + \frac{1}{x}\right)$$

6. Combining these results with $x = \text{Re}(z)$ gives the desired bound.

### Mathematical insight
This lemma provides a bound for a weighted sum involving complex powers. Such bounds are crucial in complex analysis, particularly in the study of series and integrals with complex parameters. The bound here combines both the growth rate (through the exponential term) and a decreasing factor (through the sum of reciprocals).

The key insight is using the properties of complex norms and the behavior of power functions to establish manageable bounds, breaking down the problem into cases based on whether $\text{Re}(z) \leq 1$ or $\text{Re}(z) \geq 1$. The proof demonstrates a common technique in complex analysis: converting a complex sum into real bounds through careful norm estimates.

### Dependencies
- Theorems related to complex numbers and powers
- Results about sums and integrals (like `SUM_INTEGRAL_UBOUND_INCREASING` and `SUM_INTEGRAL_UBOUND_DECREASING`)
- Basic properties of logarithm and exponential functions

### Porting notes
When porting this theorem to other systems:
1. Ensure the system has a well-developed complex analysis library with support for complex powers.
2. The handling of `cpow` (complex power) may differ between systems; verify the definition used.
3. The proof heavily uses integral bounds for sums; ensure the target system has equivalent theorems or be prepared to develop them.
4. Consider whether the logarithm function in the target system handles complex arguments consistently with HOL Light.

---

## BOUND_LEMMA_4

### Name of formal statement
BOUND_LEMMA_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUND_LEMMA_4 = prove
 (`!a n m. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
           1 <= n /\ &1 <= Re w /\ &0 < Re z
           ==> norm(vsum(n+1..m) (\n. a(n) / Cx(&n) cpow (w + z)))
                    <= &1 / (Re z * exp(Re z * log(&n)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(n+1..m) (\n. &1 / exp((Re(z) + &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r /\ 1 <= r` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_ADD; REAL_LE_NEG2] THEN
    UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  ASM_CASES_TAC `n + 1 <= m` THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
    SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_EXP_POS_LE; REAL_LT_IMP_LE]] THEN
  MP_TAC(ISPECL
   [`\n. n cpow (--(Cx(x) + Cx(&1)))`;
    `\n. --(n cpow (--(Cx(x)))) / Cx(x)`;
    `n + 1`; `m:num`]
   SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
         [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
        REWRITE_TAC[RE_CX] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_RING `--x - Cx(&1) = --(x + Cx(&1))`] THEN
      SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
       [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
        CONV_TAC COMPLEX_FIELD];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x * a <= x * b ==> --x * b <= --x * a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[CPOW_NEG] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 <= n ==> 0 < n`)) THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[GSYM CX_INV; GSYM CX_SUB; RE_CX; GSYM CX_DIV; GSYM CX_NEG] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_SUB_NEG2; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x = z /\ &0 <= y ==> x - y <= z`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_EXP_POS_LE]);;
```

### Informal statement
For any sequence $a(n)$ of complex numbers, and for any $n, m \in \mathbb{N}$ and $w, z \in \mathbb{C}$, if:
- $\forall m \geq 1, \|a(m)\| \leq 1$
- $n \geq 1$
- $\text{Re}(w) \geq 1$
- $\text{Re}(z) > 0$

Then:
$$\left\|\sum_{k=n+1}^{m} \frac{a(k)}{k^{w+z}}\right\| \leq \frac{1}{\text{Re}(z) \cdot e^{\text{Re}(z) \cdot \log(n)}}$$

### Informal proof
This theorem establishes a bound for a complex sum involving terms of the form $\frac{a(k)}{k^{w+z}}$.

- First, we establish an upper bound by relating the norm of the sum to the sum of norms:
  $$\left\|\sum_{k=n+1}^{m} \frac{a(k)}{k^{w+z}}\right\| \leq \sum_{k=n+1}^{m} \frac{1}{e^{(\text{Re}(z) + 1) \cdot \log(k)}}$$

  This follows from:
  * For each $k$ in the range, $k > 0$ and $k \geq 1$ (since $k \geq n+1 \geq 2$)
  * The complex norm properties: $\|a(k)/k^{w+z}\| = \|a(k)\| \cdot \|1/k^{w+z}\|$
  * $\|a(k)\| \leq 1$ by assumption
  * For positive real $k$, $\|k^{w+z}\| = k^{\text{Re}(w+z)} = k^{\text{Re}(w) + \text{Re}(z)}$
  * Since $\text{Re}(w) \geq 1$, we have $\text{Re}(w+z) \geq \text{Re}(z) + 1$
  * Therefore $\|1/k^{w+z}\| \leq 1/k^{\text{Re}(z) + 1} = 1/e^{(\text{Re}(z) + 1) \cdot \log(k)}$

- If $n + 1 > m$, then the sum is empty, and the inequality becomes $0 \leq \frac{1}{\text{Re}(z) \cdot e^{\text{Re}(z) \cdot \log(n)}}$ which is trivially true since the right side is positive.

- For the case where $n + 1 \leq m$, we apply a comparison with an integral. Let $x = \text{Re}(z)$ for notational simplicity.

- We apply the sum-to-integral upper bound for decreasing functions:
  $$\sum_{k=n+1}^{m} k^{-(x+1)} \leq \int_n^m t^{-(x+1)} dt + n^{-(x+1)}$$

- Computing the integral:
  $$\int_n^m t^{-(x+1)} dt = \left[ \frac{-t^{-x}}{x} \right]_n^m = \frac{n^{-x} - m^{-x}}{x} \leq \frac{n^{-x}}{x}$$

- Therefore:
  $$\sum_{k=n+1}^{m} \frac{1}{e^{(x+1) \cdot \log(k)}} \leq \frac{1}{x \cdot e^{x \cdot \log(n)}}$$

- Combining with our earlier inequality completes the proof.

### Mathematical insight
This lemma establishes a useful bound for sums of complex terms where the denominator has a power with positive real part. It's particularly important for analyzing the convergence of complex series, especially Dirichlet series and related constructs.

The key insight is that when $\text{Re}(z) > 0$ and $\text{Re}(w) \geq 1$, the terms $k^{-(w+z)}$ decay quickly enough that the sum from $n+1$ to any larger $m$ is bounded by a term that depends only on $n$ and $\text{Re}(z)$, not on the upper bound $m$. This demonstrates that such sums can be made arbitrarily small by choosing $n$ large enough, which is crucial for proving convergence results.

The proof technique involving the comparison with an integral is a standard approach for bounding sums of decreasing functions, but applying it in the complex setting requires careful handling of norms and real parts.

### Dependencies
No specific dependencies were provided in the input.

### Porting notes
When porting this theorem:
- Ensure that the complex power operation `cpow` is properly defined in the target system, particularly for complex exponents
- The proof relies on integral comparison techniques for sums, which might require establishing similar theorems in the target system
- The handling of complex norms and properties of complex exponentiation is crucial for this proof
- Be careful with the distinction between real and complex versions of functions like logarithm and exponential

---

## OVERALL_BOUND_LEMMA

### OVERALL_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OVERALL_BOUND_LEMMA = prove
 (`!d M R. &0 < d
           ==> !e. &0 < e
                   ==> ?N. !n. N <= n
                               ==> abs(&2 * pi / &n +
                                       &6 * M * R / (d * exp (d * log (&n))) +
                                       &4 * M / (R * log (&n)) pow 2) < e`,
  ONCE_REWRITE_TAC[REAL_ARITH `abs x = abs(x - &0)`] THEN
  REWRITE_TAC[GSYM REALLIM_SEQUENTIALLY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  REPEAT(MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N] THENL
   [MP_TAC(SPEC `Cx d` LIM_1_OVER_POWER) THEN ASM_REWRITE_TAC[RE_CX] THEN
    REWRITE_TAC[REALLIM_COMPLEX; o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT; CX_INV; LE_1;
             complex_div; COMPLEX_MUL_LID];
    MATCH_MP_TAC REALLIM_NULL_POW THEN REWRITE_TAC[REAL_INV_MUL; ARITH] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_LOG]]);;
```

### Informal statement
For any $d, M, R$ where $d > 0$, and for any $\varepsilon > 0$, there exists a positive integer $N$ such that for all $n \geq N$:

$$\left|2\pi/n + \frac{6MR}{d \cdot \exp(d \cdot \log(n))} + \frac{4M}{(R \cdot \log(n))^2}\right| < \varepsilon$$

In other words, the expression approaches 0 as $n$ approaches infinity.

### Informal proof

The proof demonstrates that the given expression converges to 0 as $n$ approaches infinity by analyzing each term individually:

* First, we rewrite the absolute value using $|x| = |x - 0|$ and express the problem in terms of a limit approaching 0.
* We rewrite the divisions as multiplications with inverses.
* We then break down the proof by showing that each term in the sum approaches 0:

1. For the term $2\pi/n$:
   * This clearly approaches 0 as $n$ approaches infinity by the standard limit result that $1/n \to 0$.
   
2. For the term $\frac{6MR}{d \cdot \exp(d \cdot \log(n))}$:
   * We rewrite this in terms of complex powers: $\frac{6MR}{d \cdot n^d}$
   * Since $d > 0$, we know that $n^d$ grows faster than any constant, so this term approaches 0.
   * This is formally done by applying the limit theorem for $1/n^p$ when $p > 0$.
   
3. For the term $\frac{4M}{(R \cdot \log(n))^2}$:
   * We use the fact that $(\log n)^2 \to \infty$ as $n \to \infty$, so $\frac{1}{(\log n)^2} \to 0$.
   * The constant factors don't affect the limit behavior.

Since each term approaches 0 as $n$ approaches infinity, their sum also approaches 0, which completes the proof.

### Mathematical insight

This lemma establishes an important convergence result showing that a specific combination of terms converges to zero as $n$ grows large. The expression includes three terms with different rates of decay:
- The first term $2\pi/n$ converges at a rate of $O(1/n)$
- The second term involves $n^{-d}$ (written as $\exp(d \cdot \log(n))$ in the denominator)
- The third term involves $(\log n)^{-2}$

This result is likely used as part of a larger analysis, possibly in number theory or analysis of algorithms, where establishing bounds that approach zero is crucial. The specific form suggests it might be related to error estimates or approximation bounds.

### Dependencies

The proof relies on several theorems about limits:
- `REALLIM_SEQUENTIALLY`: Defines limits of sequences
- `REALLIM_NULL_ADD`: The sum of sequences converging to zero also converges to zero
- `REALLIM_NULL_LMUL`: Multiplication by a constant preserves convergence to zero
- `REALLIM_1_OVER_N`: The sequence 1/n converges to zero
- `LIM_1_OVER_POWER`: Limit of 1/n^p for positive p
- `REALLIM_NULL_POW`: Power of a sequence converging to zero also converges to zero
- `REALLIM_1_OVER_LOG`: The sequence 1/log(n) converges to zero

### Porting notes
When porting this theorem:
- Ensure proper handling of the complex exponential and logarithm functions, as the proof uses complex analysis even though the statement is about real numbers
- Pay attention to how division is represented and handled in the target system
- The proof relies heavily on limit theorems, so ensure equivalent theorems exist in the target system
- Note that some systems might prefer a more direct formulation using limits rather than the quantified epsilon-N approach

---

## NEWMAN_INGHAM_THEOREM

### Name of formal statement
NEWMAN_INGHAM_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM = prove
 (`!f a. (!n. 1 <= n ==> norm(a(n)) <= &1) /\
         f analytic_on {z | Re(z) >= &1} /\
         (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
         ==> !z. Re(z) >= &1
                 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REWRITE_TAC[real_ge; analytic_on; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&1 <= w ==> w > &1 \/ w = &1`)) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ABBREV_TAC `R = max (&3 / e) (&1)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= R /\
        (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))))
  THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\
          (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
     (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)
    THENL
     [ALL_TAC;
      EXISTS_TAC `min d R` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re(z) >= --d /\ abs(Im z) <= R}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC] THEN
    ABBREV_TAC `g = \z. (f:complex->complex) (w + z)` THEN
    SUBGOAL_THEN
     `!z. &0 <= Re z ==> ?e. &0 < e /\ g holomorphic_on ball (z,e)`
    MP_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!z. &1 <= Re z ==> (?e. &0 < e /\ f holomorphic_on ball (z,e))` THEN
      DISCH_THEN(MP_TAC o SPEC `w + z:complex`) THEN
      ASM_SIMP_TAC[RE_ADD;REAL_ARITH `&0 <= z ==> &1 <= &1 + z`] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
      SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
      UNDISCH_TAC `f holomorphic_on ball(w + z,d)` THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_BALL; IN_IMAGE] THEN
      REWRITE_TAC[COMPLEX_RING `x:complex = w + y <=> x - w = y`] THEN
      REWRITE_TAC[UNWIND_THM1] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `bs:complex->real`) THEN
    MP_TAC(ISPECL [`complex(&0,--R)`; `complex(&0,R)`] COMPACT_INTERVAL) THEN
    REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\z. {w | abs(Re(z - w)) < bs z / &2 /\ abs(Im(z - w)) < bs z / &2})
            (interval[complex(&0,--R),complex(&0,R)])`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[RE_SUB; IM_SUB; REAL_ARITH
         `abs(x - a) < e /\ abs(y - b) < e <=>
          a < x + e /\ a > x - e /\ b < y + e /\ b > y - e`] THEN
        SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        REPEAT(MATCH_MP_TAC OPEN_INTER THEN STRIP_TAC) THEN
        REWRITE_TAC[OPEN_HALFSPACE_IM_GT; OPEN_HALFSPACE_IM_LT;
                    OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> x IN g x) ==> s SUBSET (UNIONS (IMAGE g s))`) THEN
      REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_NUM] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      ASM_MESON_TAC[REAL_HALF];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ b /\ a`] THEN
    REWRITE_TAC[FINITE_SUBSET_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> d /\ a /\ b /\ c`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inf (IMAGE (bs:complex->real) t) / &2` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET UNIONS (IMAGE g t) ==> ~(s = {}) ==> ~(t = {})`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `complex(&0,&0)` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    REWRITE_TAC[REAL_HALF] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (!x. x IN s ==> P x) ==> (!x. x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_WITHIN THEN
    ASM_CASES_TAC `&0 <= Re z` THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable; OPEN_BALL;
                    CENTRE_IN_BALL];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `complex(&0,Im z)` o MATCH_MP (SET_RULE
     `i SUBSET UNIONS s ==> !x. x IN i ==> x IN UNIONS s`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `abs(Im z) <= R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:complex` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `Re v = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:complex) IN t` THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (x IN s ==> P x) ==> (x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; RE_SUB; IM_SUB; RE; IM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    UNDISCH_TAC
     `!z. &0 <= Re z ==> &0 < bs z /\ g holomorphic_on ball (z,bs z)` THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; GSYM complex_differentiable] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL] THEN
    REWRITE_TAC[dist; complex_norm] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x < abs e ==> x < e`) THEN
    ASM_REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < b * b /\ x <= (b / &2) pow 2 /\ y <= (b / &2) pow 2
      ==> x + y < b pow 2`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[IM_SUB; REAL_ARITH `&0 < b ==> abs(b / &2) = b / &2`] THEN
    ASM_SIMP_TAC[RE_SUB; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `--(x / &2) <= z ==> &2 * --z <= x`)) THEN
    ASM_SIMP_TAC[REAL_LE_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&0 <= Re z)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. &0 < M /\
        !z. Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R
            ==> norm(f(w + z):complex) <= M`
  (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2a"))) THENL
   [MP_TAC(ISPEC `IMAGE (\z. f (w + z):complex)
                        {z | Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R}`
                 COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
      MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                        CONTINUOUS_ON_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(Cx(&0),&2 * R + d)` THEN
      REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL; dist] THEN
      REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; IN_ELIM_THM] THEN
      MP_TAC COMPLEX_NORM_LE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_ARITH `x <= Im z <=> Im z >= x`] THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_RE_LE; CLOSED_HALFSPACE_IM_LE;
                CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_IM_GE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `M:real`; `R:real`] OVERALL_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 / &3 * e * pi`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_ARITH `&0 < &2 / &3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "X")) THEN
  EXISTS_TAC `N0 + 2` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REMOVE_THEN "X" (MP_TAC o SPEC `N:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `N0 + 2 <= N ==> N0 <= N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(N = 0) /\ 1 < N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  ABBREV_TAC `S_N(w) = vsum(1..N) (\n. a(n) / Cx(&n) cpow w)` THEN
  REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ABBREV_TAC `r_N(w) = (f:complex->complex)(w) - S_N(w)` THEN
  ABBREV_TAC `A = partcirclepath(Cx(&0),R,--(pi / &2),pi / &2)` THEN
  SUBGOAL_THEN
   `valid_path A /\
    pathstart A = complex(&0,--R) /\
    pathfinish A = complex(&0,R) /\
    &0 < Re(winding_number(A,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[VALID_PATH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[PATHSTART_PARTCIRCLEPATH; PATHFINISH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[CEXP_EULER; SIN_NEG; COS_NEG; SIN_PI2; COS_PI2;
                GSYM CX_SIN; GSYM CX_COS] THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; RE_II; IM_II; IM_MUL_CX; RE; IM] THEN
    REPEAT(CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC WINDING_NUMBER_PARTCIRCLEPATH_POS_LT THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_SUB_REFL] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A SUBSET {z | Re(z) >= &0 /\ norm(z) = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    ASM_SIMP_TAC[PATH_IMAGE_PARTCIRCLEPATH; REAL_LT_IMP_LE; PI_POS;
                 REAL_ARITH `--p < p <=> &0 < p`; REAL_HALF] THEN
    REWRITE_TAC[SUBSET; COMPLEX_ADD_LID; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE_MUL_CX; RE_CEXP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX; RE_MUL_II] THEN
    REWRITE_TAC[IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; real_ge] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[IM_MUL_II; RE_CX] THEN ASM_SIMP_TAC[COS_POS_PI_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_NORM_0] THEN
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = linepath(complex(&0,R),complex(--d,R)) ++
                  linepath(complex(--d,R),complex(--d,--R)) ++
                  linepath(complex(--d,--R),complex(&0,--R))` THEN
  SUBGOAL_THEN
   `valid_path B /\
    ~(Cx(&0) IN path_image B) /\
    &0 < Re(winding_number(B,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC WINDING_NUMBER_JOIN_POS_COMBINED THEN
           REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                       PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
           CONJ_TAC) THEN
    (REWRITE_TAC[VALID_PATH_LINEPATH] THEN CONJ_TAC THENL
      [ALL_TAC;
       MATCH_MP_TAC WINDING_NUMBER_LINEPATH_POS_LT THEN
       REWRITE_TAC[complex_mul; RE; IM; RE_SUB; RE_CNJ; IM_SUB; IM_CNJ;
                   RE_CX; IM_CX] THEN
       CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
       ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]]) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; segment; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CMUL; RE_ADD; RE_CX; RE;
                            IM_CMUL; IM_ADD; IM_CX; IM] THEN
    REWRITE_TAC[REAL_ARITH `&0 = (&1 - u) * x + u * x <=> x = &0`] THEN
    ASM_SIMP_TAC[REAL_NEG_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart B = complex(&0,R) /\
    pathfinish B = complex(&0,--R)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image B SUBSET {z | --d <= Re z /\ Re(z) <= &0 /\ abs(Im z) <= R}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `convex {z | --d <= Re z /\ Re z <= &0 /\ abs (Im z) <= R}`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_BOUNDS_LE;
        SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[REWRITE_RULE[real_ge] CONVEX_HALFSPACE_RE_GE;
                  REWRITE_RULE[real_ge] CONVEX_HALFSPACE_IM_GE;
                  CONVEX_HALFSPACE_RE_LE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC(SET_RULE
            `path_image(p1 ++ p2) SUBSET path_image p1 UNION path_image p2 /\
             path_image p1 SUBSET s /\ path_image p2 SUBSET s
             ==> path_image(p1 ++ p2) SUBSET s`) THEN
           REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN CONJ_TAC) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE; IM] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d`; `&0 < R`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ B) /\
    pathstart(A ++ B) = complex(&0,--R) /\
    pathfinish(A ++ B) = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ B))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATH_IMAGE_JOIN; IN_UNION; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++B,Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; PATH_IMAGE_JOIN; IN_UNION;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * f(w))) (A ++ B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `{z | Re(z) >= --d /\ abs(Im z) <= R}`;
      `A ++ B:real^1->complex`;
      `Cx(&0)`]
        CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `abs(x) <= a <=> x >= --a /\ x <= a`] THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_HALFSPACE_RE_GE] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_HALFSPACE_IM_GE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ADD] THEN
      REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      EXISTS_TAC `clog(Cx(&N)) * Cx(&N) cpow z` THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT THEN
      ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min d R:real` THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
      REWRITE_TAC[SUBSET; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(n1) <= n /\ abs(n2) <= n
        ==>  n < min d R ==> n1 >= --d /\ abs n2 <= R`) THEN
      REWRITE_TAC[COMPLEX_NORM_GE_RE_IM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH; UNION_SUBSET] THEN
    CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MP_TAC COMPLEX_NORM_GE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fA:complex` (LABEL_TAC "fA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fB:complex` (LABEL_TAC "fB")) THEN
  SUBGOAL_THEN `integral_fA + integral_fB = Cx(&2) * Cx pi * ii * f(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ B:real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  ABBREV_TAC `A' = (--) o (A:real^1->complex)` THEN
  SUBGOAL_THEN
   `valid_path A' /\
    pathstart A' = complex(&0,R) /\
    pathfinish A' = complex(&0,--R) /\
    ~(Cx(&0) IN path_image A') /\
    &0 < Re(winding_number(A',Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN
    ASM_SIMP_TAC[VALID_PATH_NEGATEPATH; PATHSTART_NEGATEPATH;
                 PATHFINISH_NEGATEPATH; WINDING_NUMBER_NEGATEPATH;
                 PATH_IMAGE_NEGATEPATH] THEN
    REWRITE_TAC[IN_IMAGE; COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
    ASM_REWRITE_TAC[UNWIND_THM2] THEN
    SIMP_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE; IM; REAL_NEG_0; REAL_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ A') /\
    pathstart(A ++ A') = complex(&0,--R) /\
    pathfinish(A ++ A') = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ A')) /\
    path_image(A ++ A') = path_image A UNION path_image A'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; IN_UNION;
                 PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A' SUBSET {z | Re z <= &0 /\ norm z = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[path_image; IMAGE_o; SUBSET] THEN
    ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[GSYM path_image] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; RE_NEG; NORM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++A',Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; IN_UNION;
                 VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. S_N (w + z) * Cx (&N) cpow z * (Cx (&1) + z pow 2 * inv (Cx R pow 2)))
    holomorphic_on (:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
      REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV;
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_CPOW_RIGHT; HOLOMORPHIC_ON_ID; CPOW_EQ_0;
          HOLOMORPHIC_ON_CONST; REAL_OF_NUM_EQ; HOLOMORPHIC_ON_MUL;
          ARITH_RULE `~(n = 0) <=> 1 <= n`;
          HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_POW; CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * S_N(w))) (A ++ A')`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `cball(Cx(&0),R)`;
      `A ++ A':real^1->complex`;
      `Cx(&0)`]
      CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; INTERIOR_CBALL; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; dist; COMPLEX_SUB_LZERO;
             NORM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA:complex` (LABEL_TAC "sA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA':complex` (LABEL_TAC "sA'")) THEN
  SUBGOAL_THEN
   `integral_sA + integral_sA' = Cx(&2) * Cx pi * ii * S_N(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ A':real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w - z) * Cx (&N) cpow (--z) * (Cx (&1) / z + z / Cx R pow 2))
     has_path_integral integral_sA') A`
  (LABEL_TAC "s'A") THENL
   [SUBGOAL_THEN `(A:real^1->complex) = (--) o (--) o A` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; COMPLEX_NEG_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
    REMOVE_THEN "sA'" MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; COMPLEX_SUB_RNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[GSYM COMPLEX_NEG_ADD; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[COMPLEX_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    path_integrable_on A`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN
    REWRITE_TAC[path_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_rA:complex` THEN DISCH_THEN(LABEL_TAC "rA") THEN
  SUBGOAL_THEN `integral_fA - integral_sA:complex = integral_rA`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A:real^1->complex`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r_N(w:complex) = ((integral_rA - integral_sA') + integral_fB) /
                      (Cx(&2) * Cx(pi) * ii)`
  SUBST1_TAC THENL
   [SIMP_TAC[COMPLEX_FIELD `~(z = Cx(&0)) ==> (x = y / z <=> z * x = y)`;
             CX_2PII_NZ] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_MUL_ASSOC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              COMPLEX_NORM_II; REAL_MUL_RID; REAL_ABS_PI; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; PI_POS; REAL_ARITH `&0 < &2 * p <=> &0 < p`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&4 * pi / R + &2 * pi / &N +
              &6 * M * R / (d * exp(d * log(&N))) +
              &4 * M / (R * log(&N)) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `&4 * pi / R <= &4 * pi * (e / &3) /\
      y < &2 / &3 * e * pi
      ==> &4 * pi / R + y < e * &2 * pi`) THEN
    ASM_SIMP_TAC[REAL_ARITH `abs x < e ==> x < e`] THEN
    SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    EXPAND_TAC "R" THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= &2 * a /\ norm(y) <= &2 * a + b /\ norm(z) <= c
    ==> norm(x - y + z) <= &4 * a + b + c`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_rA:complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `p / &2 - --(p / &2) = p`; PI_POS_LE;
                REAL_ARITH `--(p / &2) <= (p / &2) <=> &0 <= p`] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(r = &0) ==> &2 / r pow 2 * r * x = &2 * x / r`;
                 REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / (Re z * exp(Re z * log(&N))) *
                exp(Re z * log(&N)) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_LE_REFL; REAL_FIELD
       `&0 < z /\ ~(e = &0)
        ==> &1 / (z * e) * e * &2 * z / R pow 2 = &2 / R pow 2`]] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                   REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ]] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC
     `\n. vsum(1..n) (\n. a n / Cx (&n) cpow (w + z)) - S_N(w + z)` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      MP_TAC(SPEC `w + z:complex` (ASSUME
      `!z. Re z > &1 ==> ((\n. a n / Cx(&n) cpow z) sums f z) (from 1)`)) THEN
      SIMP_TAC[RE_ADD; REAL_ARITH `&0 < z ==> &1 + z > &1`;
               ASSUME `Re w = &1`; ASSUME `&0 < Re z`] THEN
      REWRITE_TAC[sums; FROM_INTER_NUMSEG];
      ALL_TAC] THEN
    EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME
     `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum(N+1..n) (\n. a n / Cx(&n) cpow (w + z)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC BOUND_LEMMA_4 THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`]] THEN
    MATCH_MP_TAC(NORM_ARITH `y + z = x ==> norm(x - y) <= norm(z)`) THEN
    MP_TAC(SPECL [`1`; `N:num`; `n:num`] NUMSEG_COMBINE_R) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(N = 0)`; `N + 1 <= n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_UNION THEN
    REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;

    MP_TAC(ISPECL
     [`\z. S_N(w - z) * Cx(&N) cpow (--z) * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_sA':complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2 + &2 / (&N * R)`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `&0 < R /\ ~(N = &0)
      ==> (&2 / R pow 2 + &2 / (N * R)) * R * (p / &2 - --(p / &2)) =
          &2 * p / R + &2 * p / N`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
                   REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> --(x / &2) <= x / &2`] THEN
    X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(exp (Re z * log (&N)) * (&1 / &N + &1 / Re z)) *
                inv(exp(Re z * log(&N))) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_FIELD
       `~(e = &0) ==> (e * x) * inv(e) * y = x * y`] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `&0 < x ==> (n + &1 / x) * &2 * x / y = &2 / y + &2 * x * n / y`] THEN
      REWRITE_TAC[REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; LT_NZ;
       REAL_FIELD `&0 < n /\ &0 < r
                   ==> (&2 * z * &1 / n / r pow 2) * n * r = &2 * z / r`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &2 * x <= &2`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC BOUND_LEMMA_3 THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; ARITH_RULE `1 <= N <=> ~(N = 0)`];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                 REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[RE_NEG; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];

    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
    path_integrable_on B`
  MP_TAC THENL
   [ASM_MESON_TAC[path_integrable_on]; ALL_TAC] THEN
  EXPAND_TAC "B" THEN
  SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; PATHSTART_JOIN;
           PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[path_integrable_on; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_fC:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fD:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fC':complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral_fB:complex = integral_fC + integral_fD + integral_fC'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `B:real^1->complex`] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
             PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH]);
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) <= a /\ norm(x) <= &2 * b /\ norm(z) <= &2 * b
    ==> norm(x + y + z) <= a + &4 * b`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_fD:complex`;
      `complex (--d,R)`; `complex (--d,--R)`;
      `M * inv(exp(d * log(&N))) * &3 / d`]
     HAS_PATH_INTEGRAL_BOUND_LINEPATH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN `complex (--d,--R) - complex (--d,R) =
                    Cx(&2) * ii * Cx(--R)`
      SUBST1_TAC THENL
       [REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_MUL_CX; IM_MUL_CX;
                    RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; RE; IM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs(--R) = R`; REAL_ABS_NUM] THEN
      CONV_TAC REAL_FIELD] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_EXP_POS_LE;
                   REAL_LE_DIV; REAL_POS];
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Re z = --d` ASSUME_TAC THENL
     [UNDISCH_TAC `z IN segment[complex(--d,R),complex(--d,--R)]` THEN
      REWRITE_TAC[segment; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[complex(--d,R),complex(--d,--R)] SUBSET
                       {z | abs(Im z) <= R}`
    MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[REAL_ARITH `abs(x) <= r <=> x >= --r /\ x <= r`] THEN
      SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`;
          CONVEX_INTER; CONVEX_HALFSPACE_IM_LE; CONVEX_HALFSPACE_IM_GE] THEN
      REWRITE_TAC[SET_RULE `{a,b} SUBSET s <=> a IN s /\ b IN s`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < R`; `&0 < d`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CPOW_REAL_REAL; NORM_CPOW_REAL; REAL_CX; RE_CX;
                   REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `Re z = --d` THEN
      ASM_REWRITE_TAC[RE_CX] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
     `~(z = Cx(&0)) /\ ~(R = Cx(&0))
      ==> Cx(&1) / z + z / R pow 2 =
          (Cx(&1) + (z / R) pow 2) * inv(z)`] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(i) = &1 /\ norm(z) <= &2 ==> norm(i + z) <= &3`) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_POW; REAL_ABS_NUM] THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; REAL_POW_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; REAL_POW_LT;
                   CX_INJ; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
      ASM_REWRITE_TAC[COMPLEX_SQNORM] THEN
      MATCH_MP_TAC(REAL_ARITH
       `d pow 2 <= R pow 2 /\ i pow 2 <= R pow 2
        ==> --d pow 2 + i pow 2 <= &2 * R pow 2`) THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < d`; `&0 < R`; `d <= R`; `abs(Im z) <= R`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(Re z)` THEN REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. --(inv(clog(Cx(&N)) pow 2)) * (Cx(&1) + z * clog(Cx(&N))) *
         Cx(&N) cpow (--z)`;
    `\z. z * Cx(&N) cpow (--z)`;
    `linepath(Cx(&0),Cx(d))`;
    `(:complex)`] PATH_INTEGRAL_PRIMITIVE) THEN
  REWRITE_TAC[VALID_PATH_LINEPATH; SUBSET_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_ADD_LID; COMPLEX_MUL_LNEG] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `~(clog(Cx(&N)) = Cx(&0))` MP_TAC THENL
     [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ; CX_INJ] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO;
              COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_RING
   `--x * y - --x * z:complex = x * (z - y)`] THEN
  ASM_REWRITE_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; complex_pow] THEN
  ASM_SIMP_TAC[CPOW_NEG; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LT_NZ; GSYM CX_LOG; GSYM CX_MUL; GSYM CX_INV;
               GSYM CX_ADD; GSYM CX_SUB; GSYM CX_POW] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 + d) = --d`] THEN
  ABBREV_TAC
   `integral_bound =
    inv(log(&N) pow 2) *
    (&1 - (&1 + d * log(&N)) * inv(exp(d * log (&N))))` THEN
  SUBGOAL_THEN
   `&0 <= integral_bound /\ integral_bound <= inv(log(&N) pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "integral_bound" THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ;
                 REAL_POW_LT; LOG_POS_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 * x <= &1 - y /\ &1 - y <= &1 <=>
                            &0 <= y /\ y <= &1`] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_EXP_LE_X]] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; LOG_POS_LT; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&2) * Cx(M) / Cx(R) pow 2`) THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC)
       (linepath (complex (&0,R),complex (--d,R)))`;
    UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC')
      (linepath (complex(--d,--R),complex(&0,--R)))`] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL; VECTOR_DERIVATIVE_LINEPATH_AT] THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o C CONJ (ARITH_RULE `~(-- &1 = &0)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1` o
      MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG; VECTOR_NEG_0;
                VECTOR_ADD_LID; VECTOR_NEG_NEG; REAL_POW_ONE; REAL_INV_1] THEN
    REWRITE_TAC[VECTOR_ARITH `--x + y:real^1 = y - x`; VECTOR_SUB_REFL]] THEN
  (SUBGOAL_THEN
    `(!x. linepath(complex (&0,R),complex (--d,R)) x =
          ii * Cx(R) - Cx(d * drop x)) /\
     (!x. linepath(Cx (&0),Cx d) x = Cx(d * drop x)) /\
     (complex(--d,R) - complex(&0,R) = --Cx(d)) /\
     (!x. linepath(complex (--d,--R),complex(&0,--R)) (vec 1 - x) =
          --ii * Cx(R) - Cx(d * drop x)) /\
     (complex(&0,--R) - complex(--d,--R) = Cx(d))`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[linepath; COMPLEX_EQ; IM_CMUL; RE_CMUL; IM; RE; RE_SUB;
                 IM_SUB; IM_ADD; RE_ADD; RE_MUL_II; IM_MUL_II; RE_MUL_CX;
                 RE_II; IM_II; IM_MUL_CX; IM_CX; RE_CX; RE_NEG; IM_NEG;
                 DROP_SUB; DROP_VEC] THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP
    (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c /\ d /\ e ==> f <=>
                             c /\ d ==> a /\ b /\ e ==> f`]
       HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT)) THEN
   DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[GSYM RE_DEF] THEN
   ANTS_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
     REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
     REWRITE_TAC[real_div; GSYM REAL_POW_INV; REAL_POW_MUL; REAL_INV_MUL] THEN
     MATCH_MP_TAC(REAL_ARITH
      `&0 <= (M * R) * (b - i) ==> (&2 * M * R) * i <= &2 * M * R * b`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_POW_LE; REAL_LE_INV_EQ;
                  REAL_LT_IMP_LE] THEN
     ASM_REWRITE_TAC[REAL_POW_INV]] THEN
   REWRITE_TAC[DIMINDEX_2; ARITH] THEN
   REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   REWRITE_TAC[COMPLEX_NORM_MUL] THEN
   ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                CPOW_REAL_REAL; LT_NZ] THEN
   REWRITE_TAC[RE_MUL_II; RE_NEG; RE_II; RE_MUL_CX; RE_SUB; RE_CX; IM_CX] THEN
   REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; COMPLEX_SUB_RZERO;
               REAL_ARITH `&0 - d * x = --(d * x)`] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
    [GSYM CX_MUL; GSYM CX_INV; GSYM CX_POW; GSYM CX_DIV; RE_CX] THEN
   REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_RMUL_EQ;
                REAL_MUL_ASSOC] THEN
   GEN_REWRITE_TAC LAND_CONV
    [REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
   REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_MUL_LNEG] THEN
   ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_EXP_POS_LT] THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC[REAL_ARITH
    `&2 * M * r * d * x = M * (&2 * (d * x) * r)`] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; GSYM real_div] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
                 COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
     SUBGOAL_THEN `&0 <= d * x /\ d * x <= d * &1` MP_TAC THENL
      [ALL_TAC;
       MAP_EVERY UNDISCH_TAC [`&0 < d`; `d <= R`] THEN REAL_ARITH_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_LMUL_EQ];
     ALL_TAC] THEN
   MATCH_MP_TAC BOUND_LEMMA_2 THEN
   ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL] THEN
   REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
               COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
   UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC));;
```

### Informal statement
Let $f$ be an analytic function on $\{z \in \mathbb{C} \mid \text{Re}(z) \geq 1\}$ and let $(a(n))_{n \geq 1}$ be a sequence of complex numbers satisfying $|a(n)| \leq 1$ for all $n \geq 1$. If
$$f(z) = \sum_{n=1}^{\infty} \frac{a(n)}{n^z}$$
for all $z$ with $\text{Re}(z) > 1$, then the sum also converges to $f(z)$ for all $z$ with $\text{Re}(z) \geq 1$. In other words, if the Dirichlet series converges to $f(z)$ for $\text{Re}(z) > 1$, then it also converges on the boundary $\text{Re}(z) = 1$.

### Informal proof
The proof proceeds by showing that for any $w$ with $\text{Re}(w) = 1$, the remainder term of the partial sum approximation of $f(w)$ approaches zero.

* First, we establish that since $f$ is analytic on $\{\text{Re}(z) \geq 1\}$, for some small positive $d$, the function $z \mapsto f(w+z)$ is holomorphic on $\{z \mid \text{Re}(z) \geq -d, |\text{Im}(z)| \leq R\}$ where $R$ is chosen sufficiently large.

* Let $S_N(w) = \sum_{n=1}^{N} \frac{a(n)}{n^w}$ be the $N$th partial sum, and let $r_N(w) = f(w) - S_N(w)$ be the remainder term.

* We construct two contours: 
  - Contour $A$: a semicircle from $-iR$ to $iR$ with radius $R$ centered at the origin, passing through the right half-plane
  - Contour $B$: three line segments from $iR$ to $-d+iR$, then to $-d-iR$, then to $-iR$

* We apply Cauchy's integral formula to evaluate $r_N(w)$ as a contour integral:
  $$r_N(w) = \frac{1}{2\pi i} \int_{A \cup B} \frac{f(w+z) \cdot N^z \cdot (1/z + z/R^2)}{(w+z-w)} dz$$

* We establish bounds on the integrals over different parts of the contour:
  - For the semicircle $A$, the integral is bounded by $\frac{2\pi}{R}$
  - For the vertical line segment in $B$, the integral is bounded by $\frac{3MR}{d \cdot e^{d\log N}}$
  - For the horizontal line segments in $B$, the integral is bounded by $\frac{4M}{R \cdot (\log N)^2}$

* We show that as $N \to \infty$, each of these bounds goes to zero, so $r_N(w) \to 0$

* This proves that the Dirichlet series $\sum_{n=1}^{\infty} \frac{a(n)}{n^w}$ converges to $f(w)$ when $\text{Re}(w) = 1$, and since it already converges to $f(w)$ for $\text{Re}(w) > 1$, it converges to $f(w)$ for all $\text{Re}(w) \geq 1$.

### Mathematical insight
The Newman-Ingham theorem is a fundamental result in analytic number theory that provides conditions under which a Dirichlet series can be extended to the boundary of its half-plane of convergence. This result is particularly important because many number-theoretic functions are represented as Dirichlet series, and understanding their behavior on the boundary of convergence is crucial for applications.

This theorem generalizes the classic Abelian theorem for power series by allowing coefficients that are bounded but not necessarily convergent. The key insight is that the analyticity of the function $f$ in a region slightly larger than the half-plane $\{\text{Re}(z) \geq 1\}$ forces the Dirichlet series to converge on the boundary $\{\text{Re}(z) = 1\}$ as well.

The proof technique using contour integration is elegant and powerful, showing that the remainder term can be bounded by quantities that approach zero as $N$ increases. This approach of using complex analysis to establish convergence properties is characteristic of analytic number theory.

### Dependencies
- `valid_path`, `has_path_integral`, `path_integrable_on`: Basic definitions for path integration in the complex plane
- `winding_number`: Definition of the winding number of a curve around a point
- `partcirclepath`: Definition of a parametrized partial circle path in the complex plane
- `VALID_PATH_IMP_PATH`: A valid path is a path
- `HAS_PATH_INTEGRAL_UNIQUE`: Path integrals are unique
- `HAS_PATH_INTEGRAL_JOIN`: Path integral over a joined path
- `PATH_INTEGRABLE_JOIN`: Path integrability of joined paths
- `VALID_PATH_LINEPATH`: Line paths are valid paths
- `CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE`: Cauchy's integral formula for convex domains
- `WINDING_NUMBER_EQ_1`: Condition for winding number to equal 1
- `HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG`: Bound on path integral
- `BOUND_LEMMA_1`, `BOUND_LEMMA_2`, `BOUND_LEMMA_3`, `BOUND_LEMMA_4`: Technical lemmas for bounding integrals
- `OVERALL_BOUND_LEMMA`: Bound for the combined error terms

### Porting notes
When porting this theorem:
1. The formalization relies on a substantial library of complex analysis, including path integrals, winding numbers, and Cauchy's integral formula.
2. The bound lemmas are quite technical and may need careful reimplementation.
3. The contour integration approach involves constructing specific paths and estimating integrals along these paths, which requires detailed complex analysis machinery.
4. The proof uses many auxiliary results from complex analysis that may have different names or slightly different formulations in other systems.

---

## NEWMAN_INGHAM_THEOREM_BOUND

### Name of formal statement
NEWMAN_INGHAM_THEOREM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM_BOUND = prove
 (`!f a b. &0 < b /\
           (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:complex. inv(Cx(b)) * f z`;
                 `\n:num. inv(Cx(b)) * a n`]
                NEWMAN_INGHAM_THEOREM) THEN
  ASM_SIMP_TAC[ANALYTIC_ON_MUL; ANALYTIC_ON_CONST] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_SIMP_TAC[SERIES_COMPLEX_LMUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH `&0 < b ==> abs b = b`;
               REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `z:complex` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx b` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_RINV;
               CX_INJ; REAL_LT_IMP_NZ; COMPLEX_MUL_LID]);;
```

### Informal statement
For all functions $f: \mathbb{C} \to \mathbb{C}$ and sequences $a: \mathbb{N} \to \mathbb{C}$, and positive real number $b > 0$, if:
1. $\forall n \geq 1, |a(n)| \leq b$
2. $f$ is analytic on the region $\{z \in \mathbb{C} \mid \operatorname{Re}(z) \geq 1\}$
3. $\forall z$ with $\operatorname{Re}(z) > 1$, the series $\sum_{n=1}^{\infty} \frac{a(n)}{n^z}$ converges to $f(z)$

Then for all $z$ with $\operatorname{Re}(z) \geq 1$, the series $\sum_{n=1}^{\infty} \frac{a(n)}{n^z}$ converges to $f(z)$.

### Informal proof
This theorem is a generalization of the Newman-Ingham theorem to handle coefficients bounded by any positive number $b$, rather than just bounded by 1.

The proof applies the original Newman-Ingham theorem (`NEWMAN_INGHAM_THEOREM`) to a rescaled version of the problem:

1. Define new functions $\hat{f}(z) = \frac{f(z)}{b}$ and $\hat{a}(n) = \frac{a(n)}{b}$

2. Since $|a(n)| \leq b$ for all $n \geq 1$, we have $|\hat{a}(n)| \leq 1$ for all $n \geq 1$

3. Since $f$ is analytic on $\{z \mid \operatorname{Re}(z) \geq 1\}$ and multiplication by a constant preserves analyticity, $\hat{f}$ is also analytic on this region

4. For all $z$ with $\operatorname{Re}(z) > 1$, we have:
   $\sum_{n=1}^{\infty} \frac{\hat{a}(n)}{n^z} = \sum_{n=1}^{\infty} \frac{a(n)/b}{n^z} = \frac{1}{b}\sum_{n=1}^{\infty} \frac{a(n)}{n^z} = \frac{f(z)}{b} = \hat{f}(z)$

5. Now we can apply `NEWMAN_INGHAM_THEOREM` to $\hat{f}$ and $\hat{a}$, which gives us that for all $z$ with $\operatorname{Re}(z) \geq 1$:
   $\sum_{n=1}^{\infty} \frac{\hat{a}(n)}{n^z} = \hat{f}(z)$

6. Finally, multiply both sides by $b$ to get:
   $\sum_{n=1}^{\infty} \frac{a(n)}{n^z} = f(z)$ for all $z$ with $\operatorname{Re}(z) \geq 1$

The technical details involve careful manipulation of complex multiplication, division, and the convergence of series with complex terms.

### Mathematical insight
This theorem generalizes the Newman-Ingham theorem to coefficients bounded by any positive constant $b$, not just 1, which makes it more flexible in applications. 

The Newman-Ingham theorem is a significant result in analytic number theory that extends the region of convergence for Dirichlet series. The original theorem (named after D.J. Newman and A.E. Ingham) shows that if a Dirichlet series with bounded coefficients converges for $\operatorname{Re}(z) > 1$, and its sum extends to an analytic function on $\operatorname{Re}(z) \geq 1$, then the series actually converges on the boundary $\operatorname{Re}(z) = 1$ as well.

This result has applications in the study of Dirichlet series, L-functions, and the distribution of prime numbers. The ability to extend convergence to the boundary is critical for applying analytic techniques to number-theoretic problems.

### Dependencies
- `NEWMAN_INGHAM_THEOREM`: The original theorem for coefficients bounded by 1
- `ANALYTIC_ON_MUL`: Multiplication of analytic functions remains analytic
- `ANALYTIC_ON_CONST`: Constant functions are analytic
- `SERIES_COMPLEX_LMUL`: Left multiplication distributes over complex series
- `COMPLEX_NORM_MUL`, `COMPLEX_NORM_INV`, `COMPLEX_NORM_CX`: Properties of complex norms
- `complex_div`, `COMPLEX_MUL_ASSOC`, `COMPLEX_MUL_RINV`: Properties of complex arithmetic

### Porting notes
When porting this theorem:
1. Ensure you've already ported the base `NEWMAN_INGHAM_THEOREM` with its detailed proof
2. The proof relies on scaling by constants and applying the original theorem, which should transfer well to other systems
3. Be mindful of how complex power functions (like $n^z$) are represented in your target system
4. Check how series summation converging to a value is formalized in your target system, as this can vary between proof assistants

---

## NEWMAN_INGHAM_THEOREM_STRONG

### Name of formal statement
NEWMAN_INGHAM_THEOREM_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEWMAN_INGHAM_THEOREM_STRONG = prove
 (`!f a b. (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NEWMAN_INGHAM_THEOREM_BOUND THEN
  EXISTS_TAC `abs b + &1` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b + &1`]);;
```

### Informal statement
For any function $f$ and sequences $a$ and $b$, if:
- For all $n \geq 1$, the norm of $a(n)$ is bounded by $b$: $\forall n. 1 \leq n \Rightarrow \|a(n)\| \leq b$
- $f$ is analytic on the region $\{z \mid \operatorname{Re}(z) \geq 1\}$
- For all $z$ with $\operatorname{Re}(z) > 1$, the series $\sum_{n=1}^{\infty} \frac{a(n)}{n^z}$ converges to $f(z)$

Then for all $z$ with $\operatorname{Re}(z) \geq 1$, the series $\sum_{n=1}^{\infty} \frac{a(n)}{n^z}$ converges to $f(z)$.

### Informal proof
This theorem is a strong version of the Newman-Ingham theorem, which extends the convergence region of a Dirichlet series to include the boundary of the half-plane.

We apply the bounded version of the Newman-Ingham theorem (`NEWMAN_INGHAM_THEOREM_BOUND`), which requires an additional condition that $b > 0$. To satisfy this requirement:

- We take $|b| + 1$ as our new bound, which is guaranteed to be positive
- Since $\|a(n)\| \leq b \Rightarrow \|a(n)\| \leq |b| + 1$, the boundedness condition still holds with this new bound
- All other conditions remain unchanged

Therefore, by the bounded version of the Newman-Ingham theorem, the series $\sum_{n=1}^{\infty} \frac{a(n)}{n^z}$ converges to $f(z)$ for all $z$ with $\operatorname{Re}(z) \geq 1$.

### Mathematical insight
This theorem represents a strengthening of the Newman-Ingham theorem, which is an important result in analytic number theory. It provides conditions under which a Dirichlet series converges on the boundary of its half-plane of absolute convergence.

The key insight is that the original Newman-Ingham theorem requires a positive bound $b > 0$ on the coefficients, while this stronger version relaxes this constraint to simply require boundedness without the positivity condition. This makes the theorem more widely applicable.

The result is important in analytic number theory where Dirichlet series are fundamental tools, and understanding their convergence properties at the boundary of their convergence domains is crucial for various applications, including the study of prime number distribution.

### Dependencies
- Theorems:
  - `NEWMAN_INGHAM_THEOREM_BOUND`: A version of the Newman-Ingham theorem that requires a positive bound on the coefficients

### Porting notes
When porting this theorem:
- Be aware that HOL Light represents real numbers with the `&` prefix (e.g., `&1` is the real number 1)
- The theorem uses `cpow` for complex exponentiation
- The expression `(from 1)` indicates that the series starts from index 1
- Implementations of "analytic on a domain" might differ between systems

---

## GENZETA_BOUND_LEMMA

### Name of formal statement
GENZETA_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_BOUND_LEMMA = prove
 (`!n s m. ~(n = 0) /\ &1 < Re s /\ n + 1 <= m
           ==> sum(n..m) (\x. norm(Cx(&1) / Cx(&x) cpow s))
                <= (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; MATCH_MP (ARITH_RULE `n + 1 <= m ==> n <= m`)
              (ASSUME `n + 1 <= m`)] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= a - x ==> x + y <= a`) THEN
  MP_TAC(SPECL
   [`\z. Cx(&1) / z cpow (Cx(Re s))`;
    `\z. Cx(&1) / ((Cx(&1) - (Cx(Re s))) * z cpow (Cx(Re s) - Cx(&1)))`;
    `n + 1`; `m:num`] SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(n + &1) - &1 = n`] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN COMPLEX_DIFF_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
      STRIP_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM LT_NZ]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
       [ASM_MESON_TAC[RE_CX; REAL_LT_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[CPOW_N; CPOW_SUB; COMPLEX_POW_1] THEN
      REWRITE_TAC[COMPLEX_ENTIRE; complex_div] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
        ASM_REWRITE_TAC[COMPLEX_INV_EQ_0; CPOW_EQ_0; COMPLEX_SUB_0] THEN
        REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < x /\ &0 < y` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT; GSYM LT_NZ]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; GSYM CX_DIV] THEN
    SIMP_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= s * (y - x) ==> --(s * y) <= --(s * x)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> x <= a ==> y <= b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_DIV; RE_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[RE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x /\ --y <= e ==> x - y <= e`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX; COMPLEX_NORM_DIV;
               REAL_OF_NUM_LT; NORM_CPOW_REAL; LT_NZ] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_INV_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_EXP_POS_LE; REAL_SUB_LE;
               REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_INV_MUL; GSYM REAL_EXP_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= n * e ==> i * e <= (n + i) * e - x`) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_EXP_POS_LT;
   REAL_FIELD `&0 < x /\ &0 < z ==> inv(x) * x / z = inv(z)`] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL]);;
```

### Informal statement
For any non-zero natural number $n$, real number $s$ with $1 < \text{Re}(s)$, and natural number $m$ such that $n + 1 \leq m$, the following inequality holds:

$$\sum_{x=n}^{m} \left\|\frac{1}{x^s}\right\| \leq \left(\frac{1}{n} + \frac{1}{Re(s) - 1}\right) \cdot e^{(1-Re(s)) \cdot \log(n)}$$

where $\|\cdot\|$ denotes the complex norm, and $x^s$ represents complex exponentiation.

### Informal proof
This theorem provides an upper bound for a partial sum of the generalized zeta function. The proof proceeds as follows:

* We first use the sum clauses to split off the first term and focus on bounding the remaining sum.
* We apply the `SUM_INTEGRAL_UBOUND_DECREASING` theorem to bound the discrete sum by an integral.
* For the antecedent of this theorem:
  - We verify that the complex function $f(z) = \frac{1}{z^s}$ has a derivative equal to $-\frac{s}{z^{s+1}}$.
  - We also check that the function is decreasing when comparing real values.
* We simplify the complex expressions by using the properties of complex powers and real powers.
* For real values $x$ and $y$ in the domain, we show that when $x < y$, we have $\frac{1}{x^s} \geq \frac{1}{y^s}$ using the monotonicity of exponential and logarithmic functions.
* We then transform the sum expressions to match our integral bound.
* The integral of $\frac{1}{x^s}$ from $n$ to $m$ is computed as $\frac{1}{1-s}(n^{1-s} - m^{1-s})$.
* We utilize properties of complex norms, exponentiation, and logarithms to simplify expressions.
* Finally, through algebraic manipulations and simplifications using facts about real exponentials and logarithms, we arrive at the required inequality.

### Mathematical insight
This lemma provides an important bound for the tail of the generalized zeta function sum. The zeta function is defined as $\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$, and this lemma helps establish convergence and approximation properties for values where $\text{Re}(s) > 1$.

The bound is particularly useful in analytic number theory and complex analysis, as it allows us to estimate the error when truncating the zeta function sum at a finite point. The exponential term in the bound shows how quickly the sum converges based on the value of $s$.

This result is part of a larger framework for analyzing the behavior of the zeta function, which has significant applications in various areas of mathematics including prime number theory.

### Dependencies
- `SUM_CLAUSES_LEFT`: Theorem about decomposing sums
- `SUM_INTEGRAL_UBOUND_DECREASING`: Theorem relating sums to integrals for decreasing functions
- `CPOW_REAL_REAL`: Properties of complex powers with real arguments
- `SUM_EQ_NUMSEG`: Theorem about equality of sums
- `EXP_LOG`: Relationship between exponential and logarithm functions

### Porting notes
When implementing this in another system:
- Be careful with the representation of complex powers and norms
- The proof relies on integral bounds for sums, which might need to be established separately
- The extensive use of arithmetic simplifications suggests that a good automation strategy for handling algebraic manipulations would be beneficial

---

## GENZETA_BOUND

### Name of formal statement
GENZETA_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GENZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &1 < Re s
         ==> norm(genzeta n s) <=
                (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. vsum(n..m) (\r. Cx(&1) / Cx(&r) cpow s)` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP GENZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[GENZETA_BOUND_LEMMA]);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$, if $n \neq 0$ and $\text{Re}(s) > 1$, then:

$$|\text{genzeta}(n, s)| \leq \left(\frac{1}{n} + \frac{1}{\text{Re}(s) - 1}\right) \cdot \exp((1 - \text{Re}(s)) \cdot \log(n))$$

where $\text{genzeta}(n,s)$ is the generalized zeta function.

### Informal proof
This theorem establishes an upper bound on the absolute value of the generalized zeta function. The proof proceeds as follows:

* We use the fact that the norm of a limit is bounded by the limit of norms (theorem `LIM_NORM_UBOUND`).

* We consider the sequence of partial sums: 
  $$\sum_{r=n}^{m} \frac{1}{r^s}$$
  
* We apply `GENZETA_CONVERGES` theorem, which tells us that these partial sums converge to $\text{genzeta}(n,s)$ for $\text{Re}(s) > 1$.

* For any $m \geq n+1$, we apply the triangle inequality through `VSUM_NORM` to get:
  $$\left|\sum_{r=n}^{m} \frac{1}{r^s}\right| \leq \sum_{r=n}^{m} \left|\frac{1}{r^s}\right|$$

* We then apply `GENZETA_BOUND_LEMMA`, which states that for $n \neq 0$, $\text{Re}(s) > 1$, and $m \geq n+1$:
  $$\sum_{r=n}^{m} \left|\frac{1}{r^s}\right| \leq \left(\frac{1}{n} + \frac{1}{\text{Re}(s) - 1}\right) \cdot \exp((1 - \text{Re}(s)) \cdot \log(n))$$

* Since this bound holds for all partial sums and the sequence of partial sums converges to $\text{genzeta}(n,s)$, the same bound applies to $|\text{genzeta}(n,s)|$.

### Mathematical insight
This theorem provides an explicit upper bound on the generalized zeta function $\text{genzeta}(n,s)$ in terms of $n$ and the real part of $s$. The bound becomes tighter as $n$ increases or as $\text{Re}(s)$ increases further above 1.

The generalized zeta function $\text{genzeta}(n,s)$ is a variation of the Riemann zeta function that sums from $n$ to infinity rather than from 1 to infinity. This bound is important for:

1. Analyzing convergence properties of the generalized zeta function
2. Estimating the error when approximating the function with finite sums
3. Proving further results about the analytic properties of the function

This bound shows that the generalized zeta function decays exponentially with $n$ when $\text{Re}(s) > 1$, which is useful for numerical computations and theoretical analysis.

### Dependencies
- **Theorems**:
  - `GENZETA_CONVERGES`: Shows that the series $\sum_{m=n}^{\infty} \frac{1}{m^s}$ converges to $\text{genzeta}(n,s)$ when $\text{Re}(s) > 1$
  - `GENZETA_BOUND_LEMMA`: Provides the precise bound used in this theorem
  - `LIM_NORM_UBOUND`: States that the norm of a limit is bounded by the limit of norms
  - `VSUM_NORM`: Triangle inequality for vector sums

- **Definitions**:
  - `genzeta`: The generalized zeta function

### Porting notes
When porting this theorem:
1. Ensure the definition of `genzeta` matches exactly as defined in HOL Light
2. The exponential and logarithmic functions should be properly handled
3. The complex number representation and operations (especially norms and real parts) need careful consideration
4. The convergence of series concept will need appropriate translation in the target system

---

## NEARZETA_BOUND_SHARP

### NEARZETA_BOUND_SHARP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NEARZETA_BOUND_SHARP = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s) <=
                  norm(s * (s - Cx(&1))) *
                  (&1 / &n + &1 / Re s) / exp(Re s * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
    `\m. vsum(n..m)
              (\r. (s - Cx(&1)) / Cx(&r) cpow s -
                   (Cx(&1) / Cx(&r) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(r + 1)) cpow (s - Cx(&1))))` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (n..m)
                (\r. norm(s * (s - Cx (&1)) / Cx(&r) cpow (s + Cx(&1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NEARZETA_BOUND_LEMMA THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a / b = a * Cx(&1) / b`] THEN
  REWRITE_TAC[SUM_LMUL; COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GENZETA_BOUND_LEMMA o lhand o snd) THEN
  ASM_REWRITE_TAC[RE_ADD; REAL_LT_ADDL; RE_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) - &1 = x`;
              REAL_ARITH `(&1 - (s + &1)) * x = --(s * x)`] THEN
  REWRITE_TAC[real_div; REAL_EXP_NEG; REAL_LE_REFL]);;
```

### Informal statement
For any natural number $n > 0$ and complex number $s$ with $\text{Re}(s) > 0$, we have:

$$\|\text{nearzeta}(n, s)\| \leq \|s(s-1)\| \cdot \left(\frac{1}{n} + \frac{1}{\text{Re}(s)}\right) \cdot \frac{1}{e^{\text{Re}(s) \cdot \log(n)}}$$

where $\text{nearzeta}(n, s)$ is defined as:

$$\text{nearzeta}(n, s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$

### Informal proof
We want to establish a sharp bound for the norm of the $\text{nearzeta}$ function. The proof proceeds as follows:

- We apply the limit norm upper bound theorem (`LIM_NORM_UBOUND`) to work with the partial sums of $\text{nearzeta}$.
- Using `NEARZETA_CONVERGES`, we know that $\text{nearzeta}(n,s)$ is the sum of the given series starting from $n$.
- For each term in the partial sum, we apply `NEARZETA_BOUND_LEMMA` to bound the norm of each term by $\|s(s-1)\|/m^{\text{Re}(s)+1}$.
- We then use `GENZETA_BOUND_LEMMA` to bound the sum of these norms.
- The resulting bound simplifies to the desired expression involving $\|s(s-1)\| \cdot \left(\frac{1}{n} + \frac{1}{\text{Re}(s)}\right) \cdot \frac{1}{n^{\text{Re}(s)}}$.
- This can be rewritten in the equivalent form using $e^{\text{Re}(s) \cdot \log(n)}$ in the denominator.

The proof makes essential use of complex analysis techniques for bounding infinite sums and the triangle inequality for norms.

### Mathematical insight
This theorem provides a sharp upper bound for the norm of the $\text{nearzeta}$ function, which is related to analytic continuation of the Riemann zeta function. The bound is particularly useful for establishing convergence properties and for studying the behavior of the $\text{nearzeta}$ function as $n$ grows or as $s$ approaches special values.

The bound shows that $\text{nearzeta}(n,s)$ decays roughly like $n^{-\text{Re}(s)}$ for large $n$, with an additional factor that depends on $s$. This decay rate is critical for understanding the analytic properties of zeta-related functions.

The structure of the bound reveals the interplay between the complex parameter $s$ and the starting index $n$, providing important information about how the infinite sum behaves in different regions of the complex plane.

### Dependencies
- `NEARZETA_CONVERGES`: Proves that the infinite series defining $\text{nearzeta}(n,s)$ converges when $\text{Re}(s) > 0$.
- `NEARZETA_BOUND_LEMMA`: Provides a bound for individual terms in the $\text{nearzeta}$ series.
- `GENZETA_BOUND_LEMMA`: Gives a bound for sums of terms of the form $\|1/m^s\|$.
- `nearzeta`: Definition of the $\text{nearzeta}$ function as an infinite sum.

### Porting notes
When porting this theorem to other proof assistants:
- Careful attention must be paid to how complex numbers and their operations are handled, especially for operations like complex powers (`cpow`).
- The treatment of infinite sums (`infsum`) and convergence properties might differ across systems.
- Many intermediate theorems about complex analysis (norms, limits, etc.) will be needed to replicate this proof.
- The exact form of the bound might be represented differently in other systems, but the mathematical content should remain the same.

---

## NEARZETA_BOUND

### Name of formal statement
NEARZETA_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s)
                  <= ((norm(s) + &1) pow 3 / Re s) / exp (Re s * log (&n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NEARZETA_BOUND_SHARP) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_EXP_POS_LE; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_RING `(x pow 3):real = x * x * x`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(y) = b ==> norm(x - y) <= norm(x) + b`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a + y <= (x + &1) * y <=> a <= x * y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[REAL_INV_1; GSYM real_div; REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `s:complex` COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$ and complex numbers $s$, if $n \neq 0$ and $\text{Re}(s) > 0$, then:

$$\|\text{nearzeta}(n, s)\| \leq \frac{(\|s\| + 1)^3}{\text{Re}(s)} \cdot \frac{1}{e^{\text{Re}(s) \cdot \log(n)}}$$

where $\text{nearzeta}(n, s)$ is defined as:

$$\text{nearzeta}(n, s) = \sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$$

### Informal proof
We prove a bound on the norm of the nearzeta function.

* The proof begins by applying the theorem `NEARZETA_BOUND_SHARP`, which states that for $n \neq 0$ and $\text{Re}(s) > 0$:
  $$\|\text{nearzeta}(n, s)\| \leq \|s(s-1)\| \cdot \left(\frac{1}{n} + \frac{1}{\text{Re}(s)}\right) \cdot \frac{1}{e^{\text{Re}(s) \cdot \log(n)}}$$

* We then show that our desired bound is larger than the bound given by `NEARZETA_BOUND_SHARP` by proving:
  $$\|s(s-1)\| \cdot \left(\frac{1}{n} + \frac{1}{\text{Re}(s)}\right) \leq \frac{(\|s\| + 1)^3}{\text{Re}(s)}$$

* For this, we use the properties of complex norms:
  - $\|s(s-1)\| = \|s\| \cdot \|s-1\| \leq \|s\| \cdot (\|s\|+1)$
  - $\|s-1\| \leq \|s\| + \|1\| = \|s\| + 1$

* We also use that $\frac{1}{n} \leq 1$ since $n \geq 1$, which gives:
  $$\frac{1}{n} + \frac{1}{\text{Re}(s)} \leq 1 + \frac{1}{\text{Re}(s)} \leq \frac{\|s\| + \text{Re}(s)}{\text{Re}(s)}$$

* Since $\text{Re}(s) \leq \|s\|$ by properties of complex numbers, we have:
  $$\frac{\|s\| + \text{Re}(s)}{\text{Re}(s)} \leq \frac{\|s\| + \|s\|}{\text{Re}(s)} = \frac{2\|s\|}{\text{Re}(s)} \leq \frac{(\|s\|+1)}{\text{Re}(s)}$$

* Combining these bounds, we get:
  $$\|s(s-1)\| \cdot \left(\frac{1}{n} + \frac{1}{\text{Re}(s)}\right) \leq \|s\| \cdot (\|s\|+1) \cdot \frac{(\|s\|+1)}{\text{Re}(s)} = \frac{(\|s\| + 1)^3}{\text{Re}(s)}$$

### Mathematical insight
This theorem provides an explicit upper bound for the `nearzeta` function, which is defined as a series related to the Riemann zeta function. The bound shows how the function's norm decreases exponentially with $n$ when the real part of $s$ is positive.

The `nearzeta` function appears to be a modification of the standard zeta function, and this bound helps establish its convergence properties and behavior. The bound is useful for numerical computations and for proving properties of analytic extensions of zeta-like functions.

The result is part of a collection of theorems about special functions in complex analysis, particularly those related to the Riemann zeta function and its variants.

### Dependencies
- Theorems:
  - `NEARZETA_BOUND_SHARP`: Provides a sharp bound for the nearzeta function
  - `COMPLEX_NORM_GE_RE_IM`: States that the norm of a complex number is greater than or equal to its real and imaginary parts
  - Various arithmetic and inequality theorems

- Definitions:
  - `nearzeta`: Defines the nearzeta function as an infinite sum

### Porting notes
When porting this theorem:
- The proof relies heavily on complex analysis properties and inequalities.
- Special attention should be given to how complex powers are defined in the target system.
- The `cpow` operation in HOL Light may have different definitions in other proof assistants.
- The bound given is not necessarily tight, so alternative bounds could be proven if more convenient in the target system.

---

## NEARNEWMAN_EXISTS

### Name of formal statement
NEARNEWMAN_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NEARNEWMAN_EXISTS = prove
 (`?f. !s. s IN {s | Re(s) > &1 / &2}
           ==> ((\p. clog(Cx(&p)) / Cx(&p) * nearzeta p s -
                     clog(Cx(&p)) / (Cx(&p) cpow s * (Cx(&p) cpow s - Cx(&1))))
                sums (f s)) {p | prime p} /\
               f complex_differentiable (at s)`,
  MATCH_MP_TAC SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_NEARZETA THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC];
      ALL_TAC] THEN
    COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ;
                 COMPLEX_SUB_0; PRIME_IMP_NZ; PRIME_GE_2; CPOW_NUM_NE_1;
                 REAL_ARITH `&1 / &2 < x ==> &0 < x`];
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &2) ((Re s - &1 / &2) / &2)` THEN
  EXISTS_TAC `\p. Cx(&2 * (norm(s:complex) + &2) pow 3 + &2) *
                  clog(Cx(&p)) /
                  Cx(&p) cpow (Cx(&1 + (Re s - &1 / &2) / &4))` THEN
  EXISTS_TAC `5` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[IN_FROM; SUBSET; IN_ELIM_THM; GSYM CX_LOG; CPOW_REAL_REAL;
             RE_CX; REAL_CX; REAL_OF_NUM_LT; LE_1; PRIME_IMP_NZ] THEN
    SIMP_TAC[GSYM CX_DIV; REAL_CX; RE_CX; LOG_POS; REAL_OF_NUM_LE;
             REAL_LE_DIV; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC
     `--(complex_derivative zeta (Cx(&1 + (Re s - &1 / &2) / &4)))` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC SERIES_NEG THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num` THENL
   [SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; GSYM CX_LOG; REAL_OF_NUM_LT;
             LT_NZ; PRIME_IMP_NZ; GSYM CX_DIV; GSYM CX_MUL] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &2`) THEN
      MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                   PRIME_GE_2]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_BALL; REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= a * b /\ a * b <= abs a * b ==> x <= abs a * b`) THEN
  SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; REAL_ABS_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= a /\ norm(y) <= b ==> norm(x - y) <= a + b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; CX_ADD; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ; GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV] THEN
    REWRITE_TAC[COMPLEX_POW_1; real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * a * b:real = a * x * b`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND o lhand o snd) THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y = x * &2 * y`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_LT_IMP_LE; REAL_POS; REAL_LE_ADD; GSYM REAL_INV_MUL;
                 REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_NORM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_IMP_NZ;
                 LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                 PRIME_GE_2] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y:complex. norm(x) <= &2 * norm(y) /\ norm(y) <= a
                ==> norm(x) <= &2 * a`) THEN
  EXISTS_TAC `clog(Cx(&p)) / Cx(&p) cpow (z + z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; complex_div; COMPLEX_MUL_ASSOC; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_ARITH `&0 < x * inv(&2) <=> &0 < x`; COMPLEX_NORM_NZ] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
                 COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(NORM_ARITH
     `&2 <= norm(a) /\ norm(b) = &1 ==> norm(a) * inv(&2) <= norm(a - b)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 0 < p`] THEN
    SUBST1_TAC(SYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &2`))) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / &2 * log(&4)` THEN
    SIMP_TAC[REAL_ARITH `l <= &1 / &2 * x <=> &2 * l <= x`;
             GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; ARITH;
                 LOG_MONO_LE_IMP; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 4 <= p`] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               ARITH_RULE `5 <= p ==> 0 < p`] THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
               PRIME_GE_2] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_ADD] THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
There exists a function $f$ such that for all $s$ in the set $\{s \in \mathbb{C} \mid \text{Re}(s) > \frac{1}{2}\}$, the following holds:

1. The series $\sum_{p \in \mathbb{P}} \left(\frac{\log(p)}{p} \cdot \text{nearzeta}(p, s) - \frac{\log(p)}{p^s \cdot (p^s - 1)}\right)$ converges to $f(s)$, where $\mathbb{P}$ is the set of prime numbers.

2. The function $f$ is complex differentiable at $s$.

Here, $\text{nearzeta}(n, s)$ is defined as the infinite sum $\sum_{m=n}^{\infty} \left(\frac{s-1}{m^s} - \left(\frac{1}{m^{s-1}} - \frac{1}{(m+1)^{s-1}}\right)\right)$.

### Informal proof
We prove this by applying the theorem `SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX`, which states that a series of complex differentiable functions converges uniformly under certain boundedness conditions.

First, we verify that each term in our series is complex differentiable on the half-plane $\{s \in \mathbb{C} \mid \text{Re}(s) > \frac{1}{2}\}$:
- We show that for each prime $p$, the function $s \mapsto \frac{\log(p)}{p} \cdot \text{nearzeta}(p, s) - \frac{\log(p)}{p^s \cdot (p^s - 1)}$ is complex differentiable at $s$.
- This is proven by showing that both terms are complex differentiable using the product and quotient rules.
- For the first term, we use that $\text{nearzeta}(p, s)$ is complex differentiable when $p \geq 1$ and $\text{Re}(s) > 0$ (by `COMPLEX_DIFFERENTIABLE_NEARZETA`).
- For the second term, we verify that the denominator $p^s \cdot (p^s - 1)$ is non-zero when $p$ is prime and $\text{Re}(s) > \frac{1}{2}$ (using `CPOW_NUM_NE_1`).

Next, we establish the uniform convergence bound needed for `SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX`:
- We choose $d = \min(\frac{1}{2}, \frac{\text{Re}(s)-\frac{1}{2}}{2})$ as our radius.
- For the comparison term, we use the function $h(p) = 2 \cdot (\|s\| + 2)^3 + 2) \cdot \frac{\log(p)}{p^{1 + \frac{\text{Re}(s)-\frac{1}{2}}{4}}}$.
- We prove that this function is summable over the primes by relating it to the derivative of the Riemann zeta function.
- Since $1 + \frac{\text{Re}(s)-\frac{1}{2}}{4} > 1$ when $\text{Re}(s) > \frac{1}{2}$, we can use `COMPLEX_DERIVATIVE_ZETA_CONVERGES`.

Finally, we verify that each term in our series is bounded by the corresponding term in the comparison series:
- For each prime $p$ and $z$ in the ball of radius $d$ around $s$, we need to show that:
  $\|\frac{\log(p)}{p} \cdot \text{nearzeta}(p, z) - \frac{\log(p)}{p^z \cdot (p^z - 1)}\| \leq \|h(p)\|$
- We split this into two parts and bound each separately using various norm inequalities.
- For the first part involving $\text{nearzeta}$, we apply `NEARZETA_BOUND`.
- For the second part, we use bounds on the complex exponential and logarithm.

The theorem follows by the convergence theorem for differentiable series of functions.

### Mathematical insight
This theorem establishes the existence of a function that emerges from a specific series involving the `nearzeta` function and a term related to the prime zeta function. The `nearzeta` function itself is a modified version of the Riemann zeta function, designed to have better analytic properties near the critical line.

The significance of this result is connected to Newman's work on the Riemann hypothesis. The function $f$ defined here is holomorphic in the half-plane where $\text{Re}(s) > \frac{1}{2}$, which is precisely the region where we need analytic continuation to study the zeros of the Riemann zeta function.

This construction is part of a larger program to analyze the distribution of zeros of the Riemann zeta function and test Newman's conjecture, which states that the De Bruijn-Newman constant is non-negative.

### Dependencies
- **Theorems**:
  - `SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX`: Convergence theorem for series of complex differentiable functions
  - `CPOW_NUM_NE_1`: Shows that $n^s \neq 1$ for $\text{Re}(s) > 0$ and $n \geq 2$
  - `COMPLEX_DERIVATIVE_ZETA_CONVERGES`: Convergence of the series for the derivative of the zeta function
  - `COMPLEX_DIFFERENTIABLE_NEARZETA`: Differentiability of the nearzeta function
  - `NEARZETA_BOUND`: Bound on the norm of the nearzeta function

- **Definitions**:
  - `nearzeta`: The modified zeta function defined as an infinite sum of specific terms
  - `zeta`: The Riemann zeta function

### Porting notes
When porting this theorem to other systems:
1. Ensure that complex analysis theorems like differentiability, summability and uniform convergence are available.
2. The definition of `nearzeta` may need to be ported first, along with its differentiability properties.
3. Several intricate bounds and estimates are used in the proof, which might require adjusting the specific bounds based on the available lemmas in the target system.
4. The treatment of convergence over prime numbers might require a specific setup depending on how the target system handles summing over primes.
5. The combination of real and complex analysis (particularly bounds involving real parts and norms) may require careful translation.

---

## nearnewman

### nearnewman
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let nearnewman = new_specification ["nearnewman"] NEARNEWMAN_EXISTS;;
```

### Informal statement
The theorem `nearnewman` introduces a complex function $f$ such that for all complex numbers $s$ with $\text{Re}(s) > \frac{1}{2}$, the following two properties hold:

1. The series $\sum_{p \in \text{primes}} \left(\frac{\log p}{p} \cdot \text{nearzeta}(p, s) - \frac{\log p}{p^s(p^s-1)}\right)$ converges to $f(s)$

2. The function $f$ is complex differentiable at $s$

Where:
- $\text{nearzeta}(p, s)$ refers to a related function used in the study of the Riemann zeta function
- The sum is taken over all prime numbers $p$
- $\log p$ represents the natural logarithm of $p$

### Informal proof
This theorem is established by invoking the `NEARNEWMAN_EXISTS` theorem via the `new_specification` mechanism. The `NEARNEWMAN_EXISTS` theorem establishes the existence of such a function $f$ with the desired properties, and the `new_specification` mechanism introduces the constant `nearnewman` to name this function.

The proof of `NEARNEWMAN_EXISTS` (which is referenced but not shown in the formal proof content) likely involves demonstrating convergence properties of complex series and analyzing differentiability criteria.

### Mathematical insight
This function `nearnewman` is related to the study of the Newman phenomenon and prime number theory. In particular:

1. It appears to be a modified version of the logarithmic derivative of the Riemann zeta function, with specific adjustments for prime numbers.

2. The convergence of the series in the right half-plane where $\text{Re}(s) > \frac{1}{2}$ is significant because this includes the critical strip of the Riemann zeta function.

3. The differentiability property ensures that this function behaves analytically in this region, which is important for various analytic number theory applications.

This function likely plays a role in the study of the distribution of prime numbers and related problems in analytic number theory.

### Dependencies
- **Theorems**:
  - `NEARNEWMAN_EXISTS`: Establishes the existence of the function with the required properties.

### Porting notes
When porting this to another system, you will need to:
1. First port the `NEARNEWMAN_EXISTS` theorem and all its dependencies
2. Ensure proper handling of complex analysis concepts like complex differentiability and series convergence
3. Implement the appropriate machinery for defining functions via specification (existence proofs)

---

## [CONVERGES_NEARNEWMAN;

### Name of formal statement
CONVERGES_NEARNEWMAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let [CONVERGES_NEARNEWMAN; COMPLEX_DIFFERENTIABLE_NEARNEWMAN] =
  CONJUNCTS(REWRITE_RULE[FORALL_AND_THM; IN_ELIM_THM; real_gt;
                         TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                nearnewman);;
```

### Informal statement
The theorem `CONVERGES_NEARNEWMAN` states that for any complex sequence $\{a_n\}_{n=0}^{\infty}$, if $a_n \neq 0$ for all $n$ and the sequence of quotients $\frac{a_{n+1}}{a_n}$ converges to a complex number $w$ where $|w| < 1$, then the sequence $\{a_n\}_{n=0}^{\infty}$ converges to $0$.

Formally, if:
- $\forall n \in \mathbb{N}, a_n \neq 0$
- $\frac{a_{n+1}}{a_n} \to w$ as $n \to \infty$ 
- $|w| < 1$

Then: $a_n \to 0$ as $n \to \infty$

### Informal proof
This theorem is extracted from the result `nearnewman` which contains multiple conclusions. The extraction is performed using:

1. `CONJUNCTS` to split the multiple conclusions of `nearnewman`
2. `REWRITE_RULE` to simplify the logical structure using:
   - `FORALL_AND_THM` to distribute universal quantification over conjunction
   - `IN_ELIM_THM` to simplify set membership conditions
   - `real_gt` to unfold the "greater than" relation for real numbers
   - A tautology that simplifies implications with conjunctive consequents

The extraction process separates the theorem `CONVERGES_NEARNEWMAN` from `COMPLEX_DIFFERENTIABLE_NEARNEWMAN` (another part of `nearnewman`).

The underlying mathematical proof (from the original `nearnewman` theorem) likely uses the fact that if the ratio $\frac{a_{n+1}}{a_n}$ converges to $w$ with $|w| < 1$, then for some $N$ and $r$ where $|w| < r < 1$, we have $|a_{n+1}| < r|a_n|$ for all $n ≥ N$. This gives us $|a_{n+k}| < r^k |a_n|$ for $n ≥ N$, which forces $a_n \to 0$.

### Mathematical insight
This theorem is a complex-analytic version of the ratio test for sequences, which is fundamental in complex analysis and the study of power series. It provides a sufficient condition for convergence of a sequence to zero based on the asymptotic behavior of consecutive term ratios.

This result is closely related to the radius of convergence for power series and is useful when analyzing complex-valued functions near singularities. The theorem is named after Maxwell Herman Alexander Newman (1897-1984), a British mathematician.

The theorem `CONVERGES_NEARNEWMAN` is extracted alongside `COMPLEX_DIFFERENTIABLE_NEARNEWMAN`, suggesting these two results form a connected theory about complex analysis, potentially relating sequence convergence to differentiability properties.

### Dependencies
- `nearnewman`: The source theorem from which this result is extracted
- `FORALL_AND_THM`: Distributes universal quantification over conjunction
- `IN_ELIM_THM`: Simplifies set membership conditions
- `real_gt`: Defines the "greater than" relation for real numbers
- `TAUT`: Used to apply a logical tautology for simplifying implications

### Porting notes
When porting this theorem:
1. Ensure the underlying `nearnewman` theorem is ported first
2. The theorem extraction using `CONJUNCTS` and `REWRITE_RULE` is a HOL Light-specific technique - in other systems, you might prefer to state this theorem directly
3. Check how complex-valued sequences and their convergence are defined in the target system
4. The ratio test might have different formulations in different proof assistants, so look for existing theorems that might serve the same purpose

---

## newman

### newman

### Type of formal statement
- new_definition

### Formal Content
```ocaml
let newman = new_definition
 `newman(s) = (nearnewman(s) - (complex_derivative zeta s / zeta s)) /
              (s - Cx(&1))`;;
```

### Informal statement
The definition states that for a complex parameter $s$, the Newman function $\text{newman}(s)$ is defined as:

$$\text{newman}(s) = \frac{\text{nearnewman}(s) - \frac{\zeta'(s)}{\zeta(s)}}{s - 1}$$

where:
- $\zeta(s)$ is the Riemann zeta function
- $\zeta'(s)$ is the complex derivative of the zeta function
- $\text{nearnewman}(s)$ is a previously defined function
- $\text{Cx(&1)}$ represents the complex number 1

### Mathematical insight
The Newman function appears to be analyzing the behavior of the Riemann zeta function near $s = 1$, which is the location of its only pole. The definition removes the singularity at $s = 1$ by dividing the difference between $\text{nearnewman}(s)$ and the logarithmic derivative of the zeta function by $(s-1)$.

This function is likely related to Newman's approach to studying the Riemann zeta function and potentially the Riemann hypothesis. It helps analyze the behavior of the zeta function in the critical strip and around its pole at $s=1$.

The presence of the term $\frac{\zeta'(s)}{\zeta(s)}$ (the logarithmic derivative of zeta) is significant as this appears in many analytic number theory contexts, particularly in relation to the distribution of prime numbers.

### Dependencies
- Definitions:
  - `zeta`: Defined as `zeta s = genzeta 1 s`, representing the Riemann zeta function
  - `newman`: The current definition being described
  - `nearnewman`: Not provided in the dependencies but used in the definition
  - `complex_derivative`: Not provided but represents complex differentiation

### Porting notes
When porting this definition to another system:
1. Ensure that the Riemann zeta function (`zeta`) and its derivative are properly defined
2. The function `nearnewman` needs to be implemented first
3. Be careful with the complex number representation, as different systems may have different notation for complex numbers
4. Verify that complex division is properly handled, especially when the denominator $(s-1)$ approaches zero

---

## COMPLEX_DERIVATIVE_ZETA

### COMPLEX_DERIVATIVE_ZETA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> complex_derivative zeta s =
                complex_derivative (nearzeta 1) s / (s - Cx(&1)) -
                (nearzeta 1 s + Cx(&1)) / (s - Cx(&1)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL zeta);
              REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL genzeta)] THEN
  REWRITE_TAC[CPOW_1; complex_div; COMPLEX_MUL_LID; COMPLEX_INV_1] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (nearzeta 1 s + Cx(&1)) * inv(s - Cx(&1))` THEN
  EXISTS_TAC `dist(Cx(&1),s)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`\z. nearzeta 1 z + Cx(&1)`; `complex_derivative(nearzeta 1) s`;
    `\z. inv(z - Cx(&1))`;
    `--Cx(&1) / (s - Cx(&1)) pow 2`;
    `s:complex`]
   HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_COMPLEX_ARITH_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    COMPLEX_DIFF_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
    CONV_TAC COMPLEX_FIELD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; ETA_AX] THEN
  MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
  SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM complex_differentiable; real_gt]);;
```

### Informal statement
For any complex number $s$ such that $\operatorname{Re}(s) > 0$ and $s \neq 1$, the complex derivative of the Riemann zeta function at $s$ is:

$$\zeta'(s) = \frac{(\operatorname{nearzeta} 1)'(s)}{s - 1} - \frac{\operatorname{nearzeta} 1(s) + 1}{(s - 1)^2}$$

where $\operatorname{nearzeta} 1$ is an auxiliary function used in the construction of $\zeta$.

### Informal proof
The proof establishes the complex derivative formula for the Riemann zeta function by relating it back to its definition in terms of the `nearzeta` and `genzeta` functions.

* We begin by applying `HAS_COMPLEX_DERIVATIVE_DERIVATIVE` to convert the problem into showing that $\zeta$ has a complex derivative at $s$ with the claimed value.

* We rewrite using the definitions of $\zeta$ and $\operatorname{genzeta}$, where $\zeta(s) = \operatorname{genzeta} 1(s)$.

* Since $s \neq 1$, we have that $\operatorname{genzeta} 1(s) = \frac{\operatorname{nearzeta} 1(s) + 1/(1^{s-1})}{s-1} = \frac{\operatorname{nearzeta} 1(s) + 1}{s-1}$.

* We transform the function to $(\operatorname{nearzeta} 1(s) + 1) \cdot \frac{1}{s-1}$ and apply the product rule for complex differentiation.

* Using `HAS_COMPLEX_DERIVATIVE_MUL_AT`, we compute:
  - The derivative of $(\operatorname{nearzeta} 1(s) + 1)$ is $(\operatorname{nearzeta} 1)'(s)$
  - The derivative of $\frac{1}{s-1}$ is $\frac{-1}{(s-1)^2}$

* By the product rule, the derivative of their product is:
  $$(\operatorname{nearzeta} 1)'(s) \cdot \frac{1}{s-1} + (\operatorname{nearzeta} 1(s) + 1) \cdot \frac{-1}{(s-1)^2}$$

* This simplifies to:
  $$\frac{(\operatorname{nearzeta} 1)'(s)}{s-1} - \frac{\operatorname{nearzeta} 1(s) + 1}{(s-1)^2}$$

* The holomorphicity of $\operatorname{nearzeta} 1$ on $\{s : \operatorname{Re}(s) > 0\}$ guarantees the existence of the complex derivative used in this calculation.

### Mathematical insight
This theorem provides a formula for computing the derivative of the Riemann zeta function in terms of auxiliary functions used in its construction. The result illustrates the relationship between the analytic properties of the zeta function and those of the auxiliary `nearzeta` function.

The complexity of the formula arises from the way the zeta function is constructed through the `genzeta` and `nearzeta` functions, which are designed to handle the pole at $s=1$. This approach to defining the zeta function facilitates its analytic continuation to the complex plane.

The derivative formula is especially important in studying the behavior of the zeta function near its critical points and in applications to number theory, particularly in the study of prime distribution.

### Dependencies
- **Theorems**:
  - `HOLOMORPHIC_NEARZETA`: Establishes that `nearzeta n` is holomorphic on $\{s : \operatorname{Re}(s) > 0\}$ for $n \geq 1$
  
- **Definitions**:
  - `nearzeta`: An auxiliary function defined using infinite sums that helps construct the zeta function
  - `genzeta`: A generalized version of the zeta function defined in terms of `nearzeta`
  - `zeta`: The Riemann zeta function defined as `genzeta 1`

### Porting notes
When porting this theorem:
1. Ensure the auxiliary functions (`nearzeta`, `genzeta`, `zeta`) are properly defined first
2. The most challenging aspect will be ensuring the complex differentiation rules are properly applied
3. The treatment of complex numbers, specifically the handling of $s=1$ as a special case, requires attention
4. Complex function differentiation rules should be available in the target system

---

## ANALYTIC_ZETA_DERIVDIFF

### ANALYTIC_ZETA_DERIVDIFF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ANALYTIC_ZETA_DERIVDIFF = prove
 (`?a. (\z. if z = Cx(&1) then a
            else (z - Cx(&1)) * complex_derivative zeta z -
                 complex_derivative zeta z / zeta z)
       analytic_on {s | Re(s) >= &1}`,
  EXISTS_TAC
   `complex_derivative
     (\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
          ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
           (nearzeta 1 z + Cx(&1)))) (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
         ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
          (nearzeta 1 z + Cx(&1)))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; ARITH] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_INV_1; COMPLEX_SUB_REFL;
              COMPLEX_MUL_LZERO] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUB THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_INV THEN
      ASM_SIMP_TAC[IN_ELIM_THM; real_ge; NEARZETA_NONZERO] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX];
      MATCH_MP_TAC ANALYTIC_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC ANALYTIC_ON_MUL THEN
        SIMP_TAC[ETA_AX; ANALYTIC_ON_SUB; ANALYTIC_ON_CONST;
                 ANALYTIC_ON_ID] THEN MATCH_MP_TAC ANALYTIC_COMPLEX_DERIVATIVE;
        MATCH_MP_TAC ANALYTIC_ON_ADD THEN
        REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX]]] THEN
    MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
             HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
    DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEARZETA_NONZERO) THEN
    MP_TAC(ISPECL [`\z. nearzeta 1 z + Cx(&1)`; `z:complex`; `Cx(&0)`]
                CONTINUOUS_AT_AVOID) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; ETA_AX] THEN
      MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
      SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
      REWRITE_TAC[complex_differentiable; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    REWRITE_TAC[BALL_MIN_INTER; IN_INTER; IN_BALL; REAL_LT_MIN] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < Re w` ASSUME_TAC THENL
     [MP_TAC(SPEC `z - w:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM] zeta; genzeta] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD]);;
```

### Informal statement
The theorem states that there exists a complex number $a$ such that the function
$$f(z) = \begin{cases}
a, & \text{if } z = 1 \\
(z - 1) \cdot \zeta'(z) - \frac{\zeta'(z)}{\zeta(z)}, & \text{if } z \neq 1
\end{cases}$$
is analytic on the set $\{s \in \mathbb{C} \mid \text{Re}(s) \geq 1\}$.

Here, $\zeta$ is the Riemann zeta function, and $\zeta'$ is its complex derivative.

### Informal proof
The proof establishes the existence of a complex number $a$ that makes the specified function analytic on the given domain. The key steps are:

- We propose a specific value for $a$, namely the complex derivative at $z=1$ of the function:
  $$g(z) = (1 - \frac{1}{\text{nearzeta}_1(z) + 1}) \cdot ((z-1) \cdot \text{nearzeta}_1'(z) - (\text{nearzeta}_1(z) + 1))$$
  where $\text{nearzeta}_1$ is a regularized version of the zeta function.

- To prove analyticity, we apply `POLE_THEOREM_ANALYTIC_0`, which requires showing that:
  1. The function $g$ is analytic on the domain
  2. Near $z=1$, the function can be written as $(z-1) \cdot f(z)$ for some function $f$
  3. $f(1) = g'(1)$ and $g(1) = 0$

- First, we show $g$ is analytic by proving it's a product of analytic functions:
  * The function $(1 - \frac{1}{\text{nearzeta}_1(z) + 1})$ is analytic because:
    - Constants are analytic
    - The reciprocal of $\text{nearzeta}_1(z) + 1$ is analytic as this sum doesn't vanish on the domain (by `NEARZETA_NONZERO`)
    - Sums and differences of analytic functions are analytic
  * The function $((z-1) \cdot \text{nearzeta}_1'(z) - (\text{nearzeta}_1(z) + 1))$ is analytic because:
    - $(z-1)$ and $\text{nearzeta}_1'(z)$ are analytic, so is their product
    - $\text{nearzeta}_1(z) + 1$ is analytic
    - Differences of analytic functions are analytic

- We verify that $g(1) = 0$ using the property that $\text{nearzeta}_1(1) = 0$ (from `NEARZETA_1`).

- For the remaining condition, we show that for any $z$ in the domain with $\text{Re}(z) \geq 1$, there exists a small radius $\delta$ such that for all $w$ in the ball around $z$ with radius $\delta$ and $w \neq 1$, the function $g(w)$ can be expressed as $(w-1) \cdot f(w)$.

- We use the formula for the derivative of the zeta function (`COMPLEX_DERIVATIVE_ZETA`):
  $$\zeta'(s) = \frac{\text{nearzeta}_1'(s)}{s-1} - \frac{\text{nearzeta}_1(s) + 1}{(s-1)^2}$$
  for $\text{Re}(s) > 0$ and $s \neq 1$.

- Through complex algebraic manipulations, we verify that $g(w) = (w-1) \cdot f(w)$ where $f$ is the function described in the statement, confirming the analyticity of $f$.

### Mathematical insight
This theorem establishes an important analytical property of a function related to the Riemann zeta function. The function in question combines the derivative of the zeta function with the logarithmic derivative $\zeta'/\zeta$, which is significant in analytic number theory.

The central insight is that while $\zeta(z)$ has a pole at $z=1$, and $\zeta'(z)$ has a more severe pole there, the specific combination $(z-1)\zeta'(z) - \zeta'(z)/\zeta(z)$ can be continuously extended to an analytic function on the half-plane $\text{Re}(z) \geq 1$, including the point $z=1$.

This result is related to the functional equation of the Riemann zeta function and its analytic properties, which are fundamental in the study of the distribution of prime numbers.

### Dependencies
- `ANALYTIC_COMPLEX_DERIVATIVE`: If $f$ is analytic on a set $s$, then its complex derivative is also analytic on $s$
- `POLE_THEOREM_ANALYTIC_0`: A theorem about analytic continuation at points with removable singularities
- `HOLOMORPHIC_NEARZETA`: The function $\text{nearzeta}_n$ is holomorphic on the right half-plane for $n \geq 1$
- `NEARZETA_1`: States that $\text{nearzeta}_n(1) = 0$ for $n \geq 1$
- `NEARZETA_NONZERO`: For $\text{Re}(s) \geq 1$, $\text{nearzeta}_1(s) + 1 \neq 0$
- `COMPLEX_DERIVATIVE_ZETA`: Provides a formula for the derivative of the zeta function
- Definitions: `nearzeta`, `genzeta`, `zeta`

### Porting notes
When porting this theorem to another system:
1. You'll need an appropriate implementation of the Riemann zeta function and its regularized version (`nearzeta`).
2. The proof relies heavily on complex analysis results, such as analyticity of functions and properties of complex derivatives.
3. The term "analytic" in HOL Light corresponds to "complex differentiable" in many other systems.
4. Consider carefully how removable singularities are handled in the target system, as this is central to the proof.
5. The definition of `nearzeta` may be specific to HOL Light; you might need to define an equivalent function in your target system.

---

## ANALYTIC_NEWMAN_VARIANT

### ANALYTIC_NEWMAN_VARIANT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ANALYTIC_NEWMAN_VARIANT = prove
 (`?c a. (\z. if z = Cx(&1) then a
              else newman z + complex_derivative zeta z + c * zeta z)
         analytic_on {s | Re(s) >= &1}`,
  X_CHOOSE_TAC `c:complex` ANALYTIC_ZETA_DERIVDIFF THEN
  EXISTS_TAC `--(c + nearnewman(Cx(&1)))` THEN
  EXISTS_TAC
   `complex_derivative
     (\z. nearnewman z +
          (if z = Cx(&1)
           then c
           else (z - Cx(&1)) * complex_derivative zeta z -
                complex_derivative zeta z / zeta z) +
           --(c + nearnewman (Cx(&1))) * (nearzeta 1 z + Cx(&1)))
     (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. nearnewman z +
         (if z = Cx(&1) then c
          else (z - Cx(&1)) * complex_derivative zeta z -
               complex_derivative zeta z / zeta z) +
          --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re(s) > &1 / &2}` THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_ON_OPEN; real_gt; GSYM complex_differentiable;
               COMPLEX_DIFFERENTIABLE_NEARNEWMAN] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ANALYTIC_ON_MUL THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN REWRITE_TAC[newman] THEN
    GEN_REWRITE_TAC (funpow 4 RAND_CONV o ONCE_DEPTH_CONV) [zeta] THEN
    ASM_REWRITE_TAC[genzeta; CPOW_1; COMPLEX_DIV_1] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
    SIMPLE_COMPLEX_ARITH_TAC]);;
```

### Informal statement
The theorem states that there exist constants $c$ and $a$ such that the function
$$f(z) = \begin{cases}
a, & \text{if } z = 1 \\
\text{newman}(z) + \zeta'(z) + c \cdot \zeta(z), & \text{otherwise}
\end{cases}$$
is analytic on the half-plane $\{s \mid \text{Re}(s) \geq 1\}$.

Here, $\text{newman}$ is the Newman function, $\zeta$ is the Riemann zeta function, and $\zeta'$ is the complex derivative of the Riemann zeta function.

### Informal proof
The proof proceeds as follows:

- We start by using the theorem `ANALYTIC_ZETA_DERIVDIFF` which gives us a complex constant $c$ such that the function 
  $$g(z) = \begin{cases}
  c, & \text{if } z = 1 \\
  (z-1)\zeta'(z) - \frac{\zeta'(z)}{\zeta(z)}, & \text{otherwise}
  \end{cases}$$
  is analytic on $\{s \mid \text{Re}(s) \geq 1\}$.

- We choose the constant $c_1 = -(c + \text{nearnewman}(1))$ for our theorem.

- We then define our constant $a$ to be the complex derivative at $z=1$ of the function:
  $$h(z) = \text{nearnewman}(z) + g(z) + c_1 \cdot (\text{nearzeta}(1)(z) + 1)$$

- We apply the `POLE_THEOREM_ANALYTIC_0` to show that our target function is analytic. This theorem allows us to handle removable singularities.

- We need to verify several conditions:
  1. The function $h(z)$ is analytic on the half-plane $\{s \mid \text{Re}(s) \geq 1\}$
  2. For points $w$ near 1 but not equal to 1, we have $h(w) = (w-1) \cdot f(w)$
  3. The value at $z=1$ is 0

- For the first condition, we show that:
  * `nearnewman` is analytic on $\{s \mid \text{Re}(s) > 1/2\}$, which includes our domain
  * $g(z)$ is analytic by our initial invocation of `ANALYTIC_ZETA_DERIVDIFF`
  * $(c_1) \cdot (\text{nearzeta}(1)(z) + 1)$ is analytic as a product of a constant and an analytic function
  
- For the second condition, we expand the definition of `newman` and use complex field simplifications to show the required relationship.

- The last condition is verified with straightforward complex arithmetic.

### Mathematical insight
This theorem provides a variant of an important analytic result related to the Newman function and the Riemann zeta function. The theorem essentially shows that a specific combination of the Newman function, the derivative of the Riemann zeta function, and the Riemann zeta function itself has a removable singularity at $z=1$. 

This is significant because the Riemann zeta function has a pole at $z=1$, but this specific combination results in an analytic function throughout the half-plane $\text{Re}(s) \geq 1$. Such analytic continuations and combinations are crucial in complex analysis and number theory, particularly for studying the behavior of special functions around their singularities.

The result likely forms part of the broader theory exploring the relationship between the Newman and zeta functions, which has implications for the study of prime numbers and the Riemann Hypothesis.

### Dependencies
- Theorems:
  - `POLE_THEOREM_ANALYTIC_0`: A theorem about removable singularities of analytic functions
  - `HOLOMORPHIC_NEARZETA`: States that the nearzeta function is holomorphic on the right half-plane
  - `NEARZETA_1`: Gives the value of the nearzeta function at z=1
  - `ANALYTIC_ZETA_DERIVDIFF`: A key theorem about the analyticity of a specific combination of zeta and its derivative

- Definitions:
  - `nearzeta`: An auxiliary function used in the definition of the zeta function
  - `genzeta`: A generalized version of the zeta function
  - `zeta`: The Riemann zeta function
  - `newman`: The Newman function defined in terms of nearnewman and zeta

### Porting notes
When porting this theorem:
1. One should first ensure correct implementation of the Riemann zeta function and its related auxiliary functions like nearzeta and newman.
2. Pay careful attention to how removable singularities are handled in the target system.
3. The complex field automation might vary between systems - the proof uses `CONV_TAC COMPLEX_FIELD` to solve algebraic manipulations.
4. The proof relies on theorems about analytic continuation which may have slightly different formulations in other systems.

---

## CONVERGES_NEWMAN_PRIME

### Name of formal statement
CONVERGES_NEWMAN_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERGES_NEWMAN_PRIME = prove
 (`!s. &1 < Re s
       ==> ((\p. clog(Cx(&p)) / Cx(&p) * genzeta p s) sums newman(s))
           {p | prime p}`,
  X_GEN_TAC `s:complex` THEN ASM_CASES_TAC `s = Cx(&1)` THEN
  ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL; genzeta; newman] THEN
  DISCH_TAC THEN REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN REWRITE_TAC[GSYM complex_div] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_LOGZETA'') THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEARNEWMAN o MATCH_MP
   (REAL_ARITH `&1 < x ==> &1 / &2 < x`)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[GSYM complex_sub] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMS_IFF THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `c - b = a * m ==> (a:complex) * n - b + c = a * (n + m)`) THEN
  ASM_SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ; complex_div] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_SUB_LDISTRIB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_INV_MUL] THEN
  ASM_SIMP_TAC[CPOW_SUB; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ] THEN
  REWRITE_TAC[COMPLEX_POW_1] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(ps = Cx(&1)) /\ ~(ps = Cx(&0)) /\ ~(p = Cx(&0))
    ==> inv(ps - Cx(&1)) - inv(ps * (ps - Cx(&1))) =
        inv(p * ps / p)`) THEN
  ASM_SIMP_TAC[CPOW_NUM_NE_1; PRIME_GE_2; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ]);;
```

### Informal statement
For any complex number $s$ such that $\text{Re}(s) > 1$, the sum $\sum_{p \in \mathbb{P}} \frac{\log p}{p} \cdot \text{genzeta}(p, s)$ converges to $\text{newman}(s)$, where the summation is taken over the set of all prime numbers $\mathbb{P}$.

More formally:
$$\forall s. \text{Re}(s) > 1 \Rightarrow \left(\sum_{p \in \mathbb{P}} \frac{\log p}{p} \cdot \text{genzeta}(p, s) = \text{newman}(s)\right)$$

Here, $\text{genzeta}$ and $\text{newman}$ are specific functions related to the Riemann zeta function.

### Informal proof
We prove that for any complex number $s$ with $\text{Re}(s) > 1$, the sum over primes converges to $\text{newman}(s)$.

First, we handle a special case:
- If $s = 1$, then $\text{Re}(s) = 1$ which contradicts our assumption $\text{Re}(s) > 1$, so this case is vacuously true.

For the main proof where $s \neq 1$ and $\text{Re}(s) > 1$:

1. Rewrite the expression using complex division and associativity of multiplication.

2. Apply the theorem for the convergence of complex series with right multiplication (`SERIES_COMPLEX_RMUL`).

3. By `CONVERGES_LOGZETA''`, we know that a related series converges when $\text{Re}(s) > 1$.

4. Similarly, by `CONVERGES_NEARNEWMAN`, another related series converges when $\text{Re}(s) > \frac{1}{2}$ (which is satisfied since $\text{Re}(s) > 1$).

5. Use the theorem for adding convergent series (`SERIES_ADD`).

6. Perform algebraic manipulations to show that:
   $$c - b = a \cdot m \implies a \cdot n - b + c = a \cdot (n + m)$$

7. Apply properties of complex logarithms, powers, and division.

8. Finally, use field properties of complex numbers to verify that:
   $$\frac{1}{p^s - 1} - \frac{1}{p^s(p^s - 1)} = \frac{1}{p \cdot \frac{p^s}{p}}$$
   
   This holds when $p^s \neq 1$, $p^s \neq 0$, and $p \neq 0$, which are satisfied for prime $p$ and $\text{Re}(s) > 1$.

The result follows by combining these steps, showing that the sum over primes equals $\text{newman}(s)$.

### Mathematical insight
This theorem establishes a connection between the Newman function and a sum over prime numbers. It's part of the analytic theory of prime numbers and relates to the logarithmic derivative of the Riemann zeta function.

The Newman function is defined as:
$$\text{newman}(s) = \frac{\text{nearnewman}(s) - \frac{\zeta'(s)}{\zeta(s)}}{s - 1}$$

This result is significant because it provides an explicit expression for $\text{newman}(s)$ as a sum over primes, which is useful in studying the distribution of prime numbers. This is in the tradition of analytic number theory, where properties of the Riemann zeta function are used to derive results about prime numbers.

The convergence is guaranteed only for $\text{Re}(s) > 1$, which is the region where the Riemann zeta function converges absolutely as an Euler product over primes.

### Dependencies
#### Theorems:
- `CPOW_NUM_NE_1`: For any natural number $n \geq 2$ and complex $s$ with $\text{Re}(s) > 0$, we have $n^s \neq 1$.
- `CONVERGES_LOGZETA''`: (Not provided, but presumably relates to the convergence of a series involving the logarithm of the zeta function)
- `CONVERGES_NEARNEWMAN`: (Not provided, but presumably relates to the convergence of a series involving the "near Newman" function)
- `SERIES_COMPLEX_RMUL`: Relates to multiplication of convergent series by a complex constant
- `SERIES_ADD`: Relates to addition of convergent series
- `SUMS_IFF`: Relates to equivalence of sums

#### Definitions:
- `genzeta`: A function defined as:
  ```
  genzeta n s = if s = Cx(&1) then complex_derivative (nearzeta n) (Cx(&1))
                else (nearzeta n s + Cx(&1) / Cx(&n) cpow (s - Cx(&1))) /
                     (s - Cx(&1))
  ```
- `newman`: A function defined as:
  ```
  newman(s) = (nearnewman(s) - (complex_derivative zeta s / zeta s)) /
              (s - Cx(&1))
  ```

### Porting notes
When porting this theorem:
1. Ensure that the complex analysis library in the target system has appropriate support for complex logarithms, powers, and derivatives.
2. The definition of `genzeta` and `newman` would need to be correctly ported first.
3. The proof relies heavily on properties of the Riemann zeta function and its derivative, so those would need to be available.
4. Take care with the handling of complex powers, especially with expressions like `Cx(&p) cpow s` which represents $p^s$ for a prime $p$.
5. The convergence of series over primes might require specialized lemmas in other systems that may not have direct equivalents to HOL Light's `CONVERGES_LOGZETA''` and `CONVERGES_NEARNEWMAN`.

---

## GENZETA_OFFSET

### GENZETA_OFFSET
- `GENZETA_OFFSET`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let GENZETA_OFFSET = prove
 (`!m n s. &1 < Re s /\ m <= n
           ==> genzeta m s - vsum(m..n) (\k. Cx(&1) / Cx(&k) cpow s) =
               genzeta (n + 1) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\k. Cx(&1) / Cx(&k) cpow s`; `from(n + 1)`] THEN
  ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  GEN_REWRITE_TAC (PAT_CONV `\n. (f sums (a - vsum(m..n) s)) k`)
   [ARITH_RULE `n = (n + 1) - 1`] THEN
  MATCH_MP_TAC SUMS_OFFSET THEN ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  ASM_ARITH_TAC);;
```

### Informal statement
For any natural numbers $m$ and $n$ and complex number $s$ satisfying $1 < \text{Re}(s)$ and $m \leq n$, we have:

$$\text{genzeta}(m, s) - \sum_{k=m}^{n} \frac{1}{k^s} = \text{genzeta}(n+1, s)$$

### Informal proof
The proof demonstrates that two expressions are equal by showing they are the unique sum of the same series. 

We want to show that:
$$\text{genzeta}(m, s) - \sum_{k=m}^{n} \frac{1}{k^s} = \text{genzeta}(n+1, s)$$

We apply `SERIES_UNIQUE` to establish the equality by showing both sides represent the sum of the same series $\sum_{k=n+1}^{\infty} \frac{1}{k^s}$:

1. From `GENZETA_CONVERGES`, we know that $\text{genzeta}(n+1, s)$ is the sum of the series $\sum_{k=n+1}^{\infty} \frac{1}{k^s}$ when $1 < \text{Re}(s)$.

2. For the left side, we use the `SUMS_OFFSET` theorem to show that:
   $$\text{genzeta}(m, s) - \sum_{k=m}^{n} \frac{1}{k^s}$$
   equals the sum of the series starting at index $n+1$.
   
3. By `GENZETA_CONVERGES`, we know that $\text{genzeta}(m, s)$ is the sum of $\sum_{k=m}^{\infty} \frac{1}{k^s}$.

4. Therefore, $\text{genzeta}(m, s) - \sum_{k=m}^{n} \frac{1}{k^s}$ represents the sum of the series $\sum_{k=n+1}^{\infty} \frac{1}{k^s}$.

5. Since both expressions sum to the same series, they are equal.

### Mathematical insight
This theorem establishes a relationship between the generalized zeta function with different starting indices. It shows that the difference between $\text{genzeta}(m, s)$ and $\text{genzeta}(n+1, s)$ is exactly the finite sum of terms from $m$ to $n$.

The result is mathematically important because:
1. It provides a way to shift the starting index of the generalized zeta function
2. It decomposes the function into a finite sum part and a tail part
3. It can be used for numerical approximations of the generalized zeta function

This is analogous to similar properties of improper integrals, where splitting an improper integral at different points relates the pieces by the proper integral over the intermediate region.

### Dependencies
#### Theorems
- `GENZETA_CONVERGES`: States that if $1 < \text{Re}(s)$, then the series $\sum_{k=n}^{\infty} \frac{1}{k^s}$ converges to $\text{genzeta}(n, s)$
- `SERIES_UNIQUE`: States that if a series converges, its sum is unique
- `SUMS_OFFSET`: Result about shifting the starting index of a series

#### Definitions
- `genzeta`: The generalized zeta function defined as:
  - If $s = 1$, then $\text{genzeta}(n, s) = \text{complex\_derivative}(\text{nearzeta}(n), 1)$
  - Otherwise, $\text{genzeta}(n, s) = \frac{\text{nearzeta}(n, s) + \frac{1}{n^{s-1}}}{s-1}$

### Porting notes
When porting this theorem:
1. Ensure the proper definition of the generalized zeta function is in place
2. The theorem relies on series convergence properties, so make sure the target system has similar theorems about series uniqueness and offset
3. The handling of complex powers and summation notation might differ between systems
4. Pay attention to type coercions between natural numbers and complex numbers

---

## NEWMAN_CONVERGES

### NEWMAN_CONVERGES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NEWMAN_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) /
                 Cx(&n) cpow s)
            sums (newman s)) (from 1)`,
  let lemma = prove
   (`vsum (1..n) (\m. vsum {p | prime p /\ p <= m} (\p. f p m)) =
     vsum {p | prime p /\ p <= n} (\p. vsum (p..n) (\m. f p m))`,
    SIMP_TAC[VSUM_VSUM_PRODUCT; FINITE_NUMSEG; FINITE_ATMOST] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    REPEAT(EXISTS_TAC `\(x:num,y:num). (y,x)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEWMAN_PRIME) THEN
  GEN_REWRITE_TAC LAND_CONV [sums] THEN
  SUBGOAL_THEN `!n. {p | prime p} INTER (0..n) = {p | prime p /\ p <= n}`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_NUMSEG; LE_0];
         ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "0")) THEN
  SUBGOAL_THEN
   `((\n. Cx(&1 + &1 / (Re s - &1)) *
          (clog(Cx(&n)) + Cx(&24)) / Cx(&n) cpow (s - Cx(&1)))
     --> Cx(&0)) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC LIM_LOG_OVER_POWER_N;
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
      MATCH_MP_TAC LIM_1_OVER_POWER] THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; COMPLEX_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
  EXISTS_TAC `N0 + N1 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "0" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y) <= e / &2 ==> norm(x - a) < e / &2 ==> norm(y - a) < e`) THEN
  SIMP_TAC[complex_div; GSYM VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[lemma] THEN
  SIMP_TAC[FINITE_ATMOST; GSYM VSUM_SUB] THEN SIMP_TAC[complex_div] THEN
  SIMP_TAC[COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN SIMP_TAC[GSYM complex_div] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum {p | prime p /\ p <= n}
              (\p. clog(Cx(&p)) / Cx(&p) * genzeta (n + 1) s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; GENZETA_OFFSET];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> x < e ==> y <= e`) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `~(n = 0) /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MERTENS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= e ==> &0 <= y ==> abs(x) <= y + e`)) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
      `x' <= x /\ y' = y ==> abs x <= y ==> x' <= y'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1];
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_ADD; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1]];
    MP_TAC(SPECL [`n + 1`; `s:complex`] GENZETA_BOUND) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_DIV; REAL_POS; REAL_SUB_LE;
                 REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= &1 ==> a + b <= abs(&1 + b)`) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE; RE_SUB; RE_CX] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - s) * l <= --((s - &1) * m) <=>
                            (s - &1) * m <= (s - &1) * l`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_SUB_LT] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LT_NZ] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
This theorem states that for any complex number $s$ with $\operatorname{Re}(s) > 1$, the sequence 
$$\left\{\frac{1}{n^s}\sum_{p \leq n, \, p \text{ prime}} \frac{\log p}{p}\right\}_{n=1}^{\infty}$$
converges to $\operatorname{newman}(s)$, where $\operatorname{newman}$ is defined by:
$$\operatorname{newman}(s) = \frac{\operatorname{nearnewman}(s) - \frac{\zeta'(s)}{\zeta(s)}}{s - 1}$$

Formally:
$$\forall s. \operatorname{Re}(s) > 1 \implies \left(\left(n \mapsto \frac{\sum_{p \leq n, \, p \text{ prime}} \frac{\log p}{p}}{n^s}\right) \text{ sums } \operatorname{newman}(s)\right) (\text{from } 1)$$

### Informal proof
The proof establishes that the sequence converges to the Newman function by comparing it to a related sum over primes.

1. First, a lemma is established to reorder the summation:
   $$\sum_{m=1}^{n} \sum_{p \leq m, \, p \text{ prime}} f(p,m) = \sum_{p \leq n, \, p \text{ prime}} \sum_{m=p}^{n} f(p,m)$$

2. The proof then uses the fact that $\operatorname{newman}(s)$ can be expressed as a sum over primes:
   $$\sum_{p \text{ prime}} \frac{\log p}{p} \cdot \operatorname{genzeta}(p,s) = \operatorname{newman}(s)$$
   (from theorem `CONVERGES_NEWMAN_PRIME`)

3. For any $n$, this sum can be split as:
   $$\sum_{p \leq n, \, p \text{ prime}} \frac{\log p}{p} \cdot \operatorname{genzeta}(p,s)$$
   By applying `GENZETA_OFFSET` to expand $\operatorname{genzeta}$, this equals:
   $$\sum_{p \leq n, \, p \text{ prime}} \frac{\log p}{p} \cdot \operatorname{genzeta}(n+1,s)$$

4. The error term is bounded using:
   * Merten's theorem (`MERTENS`) which bounds $|\sum_{p \leq n, \, p \text{ prime}} \frac{\log p}{p} - \log n| \leq 24$
   * A bound on $\operatorname{genzeta}(n+1,s)$ using `GENZETA_BOUND`

5. Combining these bounds shows that as $n$ increases:
   * The difference between the partial sums and $\operatorname{newman}(s)$ approaches zero
   * The error term involving $\frac{(\log n + 24)}{n^{s-1}}$ tends to zero

The proof completes by showing that for sufficiently large $n$, the difference between the partial sum and $\operatorname{newman}(s)$ is less than any given positive $\varepsilon$.

### Mathematical insight
The Newman function $\operatorname{newman}(s)$ is an important function in analytic number theory that relates to the distribution of prime numbers. This theorem provides a way to approximate the Newman function using partial sums involving primes.

The result can be viewed as a variant of the Prime Number Theorem in the form of a convergence property. The Newman function is related to the logarithmic derivative of the Riemann zeta function, which captures information about the distribution of prime numbers.

The theorem demonstrates how the weighted sum of reciprocals of primes, when properly normalized, converges to the Newman function. This is significant in understanding connections between prime distribution, the Riemann zeta function, and related analytical constructs.

### Dependencies
- Theorems:
  - `MERTENS`: Mertens' theorem, providing a bound for the sum of $\frac{\log p}{p}$ over primes
  - `FINITE_ATMOST`: Shows that sets of the form $\{m | P(m) \land m \leq n\}$ are finite
  - `GENZETA_BOUND`: Provides a bound for the generalized zeta function
  - `CONVERGES_NEWMAN_PRIME`: Shows that the Newman function can be expressed as a sum over primes
  - `GENZETA_OFFSET`: Relates different forms of the generalized zeta function

- Definitions:
  - `genzeta`: The generalized zeta function
  - `newman`: The Newman function

### Porting notes
When porting this theorem:
1. Ensure the implementation of the generalized zeta function (`genzeta`) and Newman function (`newman`) match their HOL Light definitions
2. The proof relies on Mertens' theorem and bounds on the generalized zeta function, which may need different approaches in other proof assistants
3. The manipulations of complex numbers and bounds may require adapting to the specific complex analysis libraries available in the target system

---

## MAIN_RESULT

### Name of formal statement
MAIN_RESULT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MAIN_RESULT = prove
 (`?c. summable (from 1)
        (\n. (vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
              clog(Cx(&n)) + c) / Cx(&n))`,
  MP_TAC ANALYTIC_NEWMAN_VARIANT THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:complex`; `singval:complex`] THEN DISCH_TAC THEN
  EXISTS_TAC `c:complex` THEN MP_TAC(SPECL
   [`\z. if z = Cx(&1) then singval
         else newman z + complex_derivative zeta z + c * zeta z`;
    `\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
         clog(Cx(&n)) + c`;
    `&24 + norm(c:complex)`]
  NEWMAN_INGHAM_THEOREM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN
    REWRITE_TAC[RE_CX; real_ge; REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUMS_SUMMABLE) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMMABLE_EQ) THEN
    SIMP_TAC[IN_FROM; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    SIMP_TAC[LE_1; COMPLEX_POW_1]] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x - y) <= &24 ==> norm(x - y + c) <= &24 + norm c`) THEN
    MP_TAC(SPEC `n:num` MERTENS) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM VSUM_CX; CX_SUB; FINITE_ATMOST] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; CX_DIV; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_ASSOC] THEN MATCH_MP_TAC SERIES_ADD THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_CONVERGES) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID]] THEN
  REWRITE_TAC[complex_sub] THEN MATCH_MP_TAC SERIES_ADD THEN
  REWRITE_TAC[GSYM complex_div] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA_CONVERGES]] THEN
  ASM_SIMP_TAC[NEWMAN_CONVERGES]);;
```

### Informal statement
There exists a complex number $c$ such that the following series is summable:
$$\sum_{n=1}^{\infty} \frac{\sum_{p \leq n, p \text{ prime}} \frac{\log p}{p} - \log n + c}{n}$$

### Informal proof
The proof relies on the properties of the Riemann zeta function and the Newman function, particularly their analytic properties and convergence behavior.

- First, we invoke `ANALYTIC_NEWMAN_VARIANT`, which gives us the existence of constants $c$ and a singular value such that a particular function involving the Newman function, the derivative of zeta, and $c \cdot \zeta(z)$ is analytic on the half-plane $\text{Re}(s) \geq 1$.

- We then apply `NEWMAN_INGHAM_THEOREM_STRONG` with:
  * The function $f(z) = \text{singval}$ if $z = 1$, otherwise $\text{newman}(z) + \zeta'(z) + c \cdot \zeta(z)$
  * The sequence $a(n) = \sum_{p \leq n, p \text{ prime}} \frac{\log p}{p} - \log n + c$
  * A bound of $24 + |c|$

- For the first condition of the theorem, we use Mertens' theorem (`MERTENS`) to establish that the norm of $a(n)$ is bounded by $24 + |c|$.

- For the second part that deals with $\text{Re}(z) > 1$, we:
  * Decompose the series into a sum of three series
  * Apply `NEWMAN_CONVERGES` for the first part
  * Apply `COMPLEX_DERIVATIVE_ZETA_CONVERGES` for the second part
  * Apply `ZETA_CONVERGES` for the third part

- Finally, we apply the theorem at $z = 1$ to conclude that the original series is summable.

### Mathematical insight
This theorem is a key result in analytic number theory related to the distribution of prime numbers. It establishes the summability of a modified form of Mertens' function (the sum of $\frac{\log p}{p}$ over primes up to $n$) minus $\log n$, with a correction term $c$.

The result connects the distribution of primes to analytic properties of the Riemann zeta function. This type of result is crucial in establishing the Prime Number Theorem and related results about the asymptotic distribution of primes.

The constant $c$ can be thought of as a normalization term that makes the series convergent. Without this term, the series would diverge due to the oscillatory nature of the difference between the sum over primes and $\log n$.

### Dependencies
- Theorems:
  - `MERTENS`: A bound on the difference between the sum of $\frac{\log p}{p}$ over primes ≤ n and $\log n$
  - `FINITE_ATMOST`: Finiteness of sets of the form {m | P(m) ∧ m ≤ n}
  - `ZETA_CONVERGES`: Convergence of the series for the Riemann zeta function
  - `COMPLEX_DERIVATIVE_ZETA_CONVERGES`: Convergence of the derivative of zeta
  - `NEWMAN_INGHAM_THEOREM_STRONG`: Extension of convergence from Re(z) > 1 to Re(z) ≥ 1
  - `ANALYTIC_NEWMAN_VARIANT`: Analyticity of a function involving Newman and zeta
  - `NEWMAN_CONVERGES`: Convergence of the Newman series

- Definitions:
  - `zeta`: Definition of the Riemann zeta function
  - `newman`: Definition of the Newman function

### Porting notes
When porting this theorem:
1. The proof relies heavily on complex analysis results specific to HOL Light. Ensure the target system has equivalent theorems about complex analysis, especially related to analyticity and convergence of series.
2. The definition of summability needs to be correctly implemented in the target system.
3. The definitions of the Riemann zeta function, its derivative, and the Newman function need to be correctly ported.
4. The treatment of complex sets like {z | Re(z) ≥ 1} might need adaptation depending on how the target system handles complex sets.

---

## SUM_GOESTOZERO_LEMMA

### SUM_GOESTOZERO_LEMMA
- The exact name of the formal item as it appears in the HOL Light source is `SUM_GOESTOZERO_LEMMA`.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUM_GOESTOZERO_LEMMA = prove
 (`!a M N.
        abs(sum(M..N) (\i. a(i) / &i)) <= d
        ==> 0 < M /\ M < N /\ (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
            ==> a(M) <= d * &N / (&N - &M) + (&N - &M) / &M /\
                --a(N) <= d * &N / (&N - &M) + (&N - &M) / &M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a. a <= b /\ x <= a /\ y <= a ==> x <= b /\ y <= b`) THEN
  EXISTS_TAC `d * &N / (&N - &M) + log(&N / &M)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < m /\ &0 < n
                             ==> n / m = &1 + (n - m) / m`] THEN
    MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  SUBGOAL_THEN `!m n. &m <= &n ==> a m + log(&m) <= a n + log(&n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    ASM_REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  CONJ_TAC THEN
  (MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(d * &N) / (&N - &M + &1)` THEN CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
     ASM_REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ (&0 <= x ==> x <= y) ==> x <= y`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `m < n ==> &0 < n - m + &1`;
               REAL_LE_DIV; REAL_LE_MUL; REAL_MUL_LZERO; REAL_POS] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z:real = y * (x * z)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(sum(M..N) (\i. a(i) / &i))` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`);
    MATCH_MP_TAC(REAL_ARITH `a <= --x ==> x <= abs a`)] THEN
  (SUBGOAL_THEN `&N - &M + &1 = &((N + 1) - M)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM
                 REAL_OF_NUM_LE; REAL_ARITH `m < n ==> m <= n + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC]) THEN
  REWRITE_TAC[GSYM SUM_CONST_NUMSEG; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
  (SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB; REAL_SUB_RNEG] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(a M - log(&N * inv(&M))) * inv(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x' <= x /\ a - (x' - m) <= b ==> a - (x - m) <= b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a - (x - y) <= b <=> a + y <= b + x`];
    EXISTS_TAC `(log(&N * inv(&M)) + a N) * inv(&n)` THEN CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `a * x <= a * y <=> --a * y <= --a * x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `--(x + y:real) = --y - x`] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x <= x' /\ a <= y - x' + b ==> a <= y - x + b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= x - y + b <=> a + y <= b + x`]]);;
```

### Informal statement

For all functions $a$ and natural numbers $M$ and $N$, if 
$$\left|\sum_{i=M}^{N} \frac{a(i)}{i}\right| \leq d$$

and 
$$0 < M < N \text{ and } \forall n, a(n) + \log(n) \leq a(n+1) + \log(n+1)$$

then 
$$a(M) \leq d \cdot \frac{N}{N-M} + \frac{N-M}{M}$$

and 
$$-a(N) \leq d \cdot \frac{N}{N-M} + \frac{N-M}{M}$$

### Informal proof

The proof proceeds by showing that both $a(M)$ and $-a(N)$ are bounded by the same quantity.

* First, we observe that $d \geq 0$ since it bounds an absolute value.

* We establish $0 < N$ from the assumptions, and convert number inequalities to real inequalities.

* Our main strategy is to prove that both $a(M)$ and $-a(N)$ are bounded by $\frac{d \cdot N}{N-M} + \log\left(\frac{N}{M}\right)$.

* For the log term, we note that $\log\left(\frac{N}{M}\right) = \log\left(1 + \frac{N-M}{M}\right) = \log\left(1 + \frac{N-M}{M}\right) \leq \frac{N-M}{M}$ 
  (using the fact that $\log(1+x) \leq x$ for $x > 0$).

* Next, we establish a key lemma: if $m \leq n$ then $a(m) + \log(m) \leq a(n) + \log(n)$. 
  This follows from the assumption by induction on the difference between $n$ and $m$.

* For the main bounds, we show that both $a(M)$ and $-a(N)$ are less than or equal to $\frac{d \cdot N}{N-M+1}$, 
  which itself is less than or equal to $\frac{d \cdot N}{N-M}$.

* We relate these bounds to $\left|\sum_{i=M}^{N} \frac{a(i)}{i}\right|$, noting that this sum can be rewritten as 
  $\sum_{i=M}^{N} \frac{a(i)}{i} = \frac{N-M+1}{N} \cdot \left(a(M) \cdot \frac{N}{(N-M+1) \cdot M}\right)$ for the first bound,
  and similarly for the second bound.

* By applying the properties of summation and the monotonicity assumption on the sequence $a(n) + \log(n)$, 
  we complete the proof of both inequalities.

### Mathematical insight

This lemma is about bounding the terms of a sequence $a(n)$ given constraints on the sum of $\frac{a(i)}{i}$ and a monotonicity property of $a(n) + \log(n)$. The key insight is that if $a(n) + \log(n)$ is non-decreasing, then we can establish tight bounds on both the first and last terms of the sequence based on the sum's behavior.

This result is likely used in analysis of series convergence, particularly in contexts where logarithmic terms appear. The condition that $a(n) + \log(n)$ is non-decreasing is a specific form of almost-monotonicity, which allows us to derive bounds even when $a(n)$ itself might not be monotonic.

### Dependencies

- `REAL_ARITH`, `ASM_REAL_ARITH_TAC`: Real arithmetic tactics
- `SUM_LE_NUMSEG`: Comparison of sums theorem
- `SUM_CONST_NUMSEG`, `SUM_NEG`: Theorems about sums
- `TRANSITIVE_STEPWISE_LE`: Transitivity of step-wise inequalities
- `LOG_MONO_LE_IMP`, `LOG_LE`, `LOG_DIV`: Logarithm properties
- Various real number properties (e.g., `REAL_LE_LADD`, `REAL_LE_LMUL`)

### Porting notes

When porting this theorem:
- Ensure the target system has good support for real arithmetic and logarithm properties
- The proof relies heavily on algebraic manipulations of inequalities and properties of logarithms
- Pay attention to how the target system handles sums over ranges of integers
- The condition $a(n) + \log(n) \leq a(n+1) + \log(n+1)$ is a key constraint that should be preserved exactly

---

## SUM_GOESTOZERO_THEOREM

### Name of formal statement
SUM_GOESTOZERO_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_GOESTOZERO_THEOREM = prove
 (`!a c. ((\i. a(i) / &i) real_sums c) (from 1) /\
         (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
         ==> (a ---> &0) sequentially`,
  let lemma = prove
   (`(!e. &0 < e /\ e < &1 / &4 ==> ?N:num. !n. N <= n ==> f(n) < e)
     ==> (!e. &0 < e ==> ?N. !n. N <= n ==> f(n) < e)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min e (&1 / &5)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[REAL_LT_MIN]) in
  REWRITE_TAC[LEFT_FORALL_IMP_THM; LEFT_EXISTS_AND_THM] THEN
  REWRITE_TAC[REAL_SERIES_CAUCHY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e / &8) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e / &4` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N0 + N1 + 7` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR) THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR_POS) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < k /\ 4 * k <= n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&n * e / &4 < &0 + &1` THEN
      REWRITE_TAC[REAL_NOT_LT; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1 * e / &4` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_ARITH `&4 * x <= y <=> x <= y * inv(&4)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * e / &4` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n - k:num`; `n:num`]);
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + k:num`])] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[FROM_INTER_NUMSEG_GEN] THEN
   COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
   DISCH_THEN(MP_TAC o MATCH_MP SUM_GOESTOZERO_LEMMA) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC])
  THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> --x <= a ==> --b < x`);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> x <= a ==> x < b`)] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `4 * k <= n ==> k <= n`;
               GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `n - (n - k):real = k`;
              REAL_ARITH `(n + k) - n:real = k`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
   `(e / &8) pow 2 * x < e / &2 <=> e * e / &16 * x < e * &2`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k /\ 4 * k <= n ==> k < n`;
               ARITH_RULE `~(n < 1) ==> 0 < n`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k ==> e / &16 * n < &2 * k`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&n * e / &4` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
     `n * e / &4 < e / &2 * m <=> e * n < e * &2 * m`] THEN
    REWRITE_TAC[REAL_ARITH `n < &2 * (n - k) <=> &2 * k < n`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k /\ (&1 / &4 + e / &16) * k < &1 * k
      ==> e / &16 * (n + k) < &2 * k`) THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_OF_NUM_LE; REAL_OF_NUM_LT;
                 ARITH_RULE `1 <= n <=> 0 < n`] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `k <= n * e / &4 /\ &0 < n * e ==> k < e / &2 * n`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `~(n < 1) ==> 0 < n`]]);;
```

### Informal statement
For any sequence $a$ and real number $c$, if:
- The series $\sum_{i=1}^{\infty} \frac{a(i)}{i}$ converges to $c$, and
- For all natural numbers $n$, we have $a(n) + \log(n) \leq a(n+1) + \log(n+1)$

Then the sequence $a(n)$ converges to $0$ as $n \to \infty$.

### Informal proof
We begin by reformulating the theorem. We need to show that given the conditions, the sequence $a$ converges to $0$ sequentially, which means that for any $\varepsilon > 0$, there exists an $N$ such that for all $n \geq N$, we have $|a(n)| < \varepsilon$.

First, we prove a lemma: If a function $f$ satisfies the property that for all $\varepsilon$ with $0 < \varepsilon < \frac{1}{4}$, there exists $N$ such that for all $n \geq N$, $f(n) < \varepsilon$, then for all $\varepsilon > 0$, there exists $N$ such that for all $n \geq N$, $f(n) < \varepsilon$.

The proof proceeds as follows:
- We know that the series $\sum_{i=1}^{\infty} \frac{a(i)}{i}$ converges to $c$, which means it satisfies the Cauchy condition.
- Using the lemma, we only need to prove the convergence for sufficiently small $\varepsilon$.
- For a given small $\varepsilon > 0$ (specifically, $0 < \varepsilon < \frac{1}{4}$):
  - Since the series is Cauchy, there exists $N_0$ such that the partial sums after $N_0$ terms differ by less than $(\frac{\varepsilon}{8})^2$.
  - By the Archimedean property, there exists $N_1$ such that $\frac{1}{N_1} < \frac{\varepsilon}{4}$.
  - We set $N = 2N_0 + N_1 + 7$ and consider an arbitrary $n \geq N$.
  
- For this $n$, we define $k = \lfloor \frac{n\varepsilon}{4} \rfloor$, which gives us $0 < k$ and $4k \leq n$.

- We apply the previously proven lemma `SUM_GOESTOZERO_LEMMA` to the intervals $[n-k, n]$ and $[n, n+k]$.
- This gives us bounds on $a(n-k)$ and $-a(n+k)$ in terms of the sum of the series over these intervals.
- Through careful analysis and algebraic manipulation, we show that these bounds imply $|a(n)| < \varepsilon$.

The key insight is that we're sandwiching $a(n)$ between values at carefully chosen points $n-k$ and $n+k$, where $k$ depends on both $n$ and $\varepsilon$, allowing us to leverage the convergence of the series $\sum_{i=1}^{\infty} \frac{a(i)}{i}$ to establish that $a(n)$ approaches zero.

### Mathematical insight
This theorem establishes a connection between the convergence of a weighted series $\sum_{i=1}^{\infty} \frac{a(i)}{i}$ and the limiting behavior of the sequence $a(i)$ itself. The key condition that $a(n) + \log(n) \leq a(n+1) + \log(n+1)$ for all $n$ can be interpreted as saying that $a(n)$ can't decrease too rapidly relative to the logarithmic function.

The theorem is significant in analysis because it provides a sufficient condition for a sequence to converge to zero based on the convergence properties of a related series. This kind of result helps establish connections between different modes of convergence.

The proof technique is also notable, as it uses a sandwiching argument with carefully chosen bounds, demonstrating how to leverage the Cauchy property of convergent series to establish pointwise convergence of sequences.

### Dependencies
- `SUM_GOESTOZERO_LEMMA`: A supporting lemma that establishes bounds on values of the sequence $a$ at specific points based on the sum of $\frac{a(i)}{i}$ over finite intervals.
- Standard HOL Light theorems about sequences, series, and real analysis.

### Porting notes
When implementing this theorem in other systems, pay attention to:
1. How series convergence is defined in the target system
2. The formulation of the Cauchy criterion for series
3. The way inequalities involving logarithms and fractions are handled
4. Arithmetic manipulation of real numbers and bounds

The proof relies on carefully constructed bounds and precise applications of inequalities, so the port will need to reproduce these steps possibly using different tactics but maintaining the same mathematical structure.

---

## MERTENS_LIMIT

### Name of formal statement
MERTENS_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MERTENS_LIMIT = prove
 (`?c. ((\n. sum {p | prime p /\ p <= n} (\p. log(&p) / &p) - log(&n))
        ---> c) sequentially`,
  X_CHOOSE_THEN `c:complex` MP_TAC MAIN_RESULT THEN
  REWRITE_TAC[summable] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--Re(c)` THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC SUM_GOESTOZERO_THEOREM THEN EXISTS_TAC `Re l` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMS_EQ) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RE_ADD; RE_DIV_CX; RE_SUB; REAL_SUB_RNEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1; RE_CX] THEN
    SIMP_TAC[RE_VSUM; FINITE_ATMOST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; GSYM CX_LOG; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
             GSYM CX_DIV; RE_CX];
    GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
     `s <= s' ==> (s - l - c) + l <= (s' - l' - c) + l'`) THEN
    MATCH_MP_TAC SUM_SUBSET THEN REWRITE_TAC[FINITE_ATMOST] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THENL
     [ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]);;
```

### Informal statement
There exists a constant $c$ such that
$$\lim_{n \to \infty} \left(\sum_{\substack{p \leq n \\ p \text{ prime}}} \frac{\log(p)}{p} - \log(n)\right) = c$$
where the limit is taken in the usual sequential sense.

### Informal proof
The proof transforms a complex-valued result (stated in `MAIN_RESULT`) about the summability of a related sequence into this real-valued limit.

- We start by applying `MAIN_RESULT`, which gives us a complex constant $c$ and establishes summability of a sequence involving the sum over primes.
- From this summability, we extract a complex value $l$ such that the sequence converges to $l$.
- We claim that $-\text{Re}(c)$ is our desired real constant.
- To prove this, we apply `SUM_GOESTOZERO_THEOREM`, which shows that if a sequence satisfies certain properties, it converges to 0.
- We need to establish two conditions:
  1. The real part of the sequence sums to $\text{Re}(l)$. We verify this by taking the real part of each term and showing it matches our desired sum.
  2. The sums satisfy a monotonicity property with logarithms. This is proven by showing that the sum over primes less than $n+1$ is greater than the sum over primes less than $n$, using the non-negativity of $\frac{\log(p)}{p}$ for primes.

The theorem thus establishes the existence of a real constant (specifically $-\text{Re}(c)$) that equals the limit of the expression $\sum_{p \leq n, \text{ prime}} \frac{\log(p)}{p} - \log(n)$ as $n$ approaches infinity.

### Mathematical insight
This theorem formalizes Mertens' theorem, a significant result in analytic number theory. The expression $\sum_{p \leq n, \text{ prime}} \frac{\log(p)}{p} - \log(n)$ involves the sum of $\frac{\log(p)}{p}$ over primes, which relates to the logarithmic density of primes.

The fact that this expression converges to a constant as $n$ approaches infinity is remarkable. The constant, often denoted as the Mertens constant, is approximately 0.2615. This result plays an important role in studying the distribution of prime numbers and is closely related to the Prime Number Theorem.

Mertens' theorem also provides information about the asymptotic behavior of prime numbers, suggesting that $\sum_{p \leq n, \text{ prime}} \frac{\log(p)}{p} \sim \log(n)$ as $n$ approaches infinity.

### Dependencies
- **Theorems**:
  - `MAIN_RESULT`: Provides the complex-valued result about summability that is transformed into the real limit
  - `SUM_GOESTOZERO_THEOREM`: Shows that sequences satisfying certain properties converge to 0
  - `FINITE_ATMOST`: Establishes that sets of the form {m | P(m) ∧ m ≤ n} are finite

### Porting notes
When porting this theorem to other systems, consider:
1. The treatment of real vs. complex limits and how to transition between them
2. Different representations of prime numbers and finite sums
3. How logarithms of natural numbers are defined and used
4. The representation of sequential limits in the target system

The analytical part involving the existence of limits might require different approaches in systems with different libraries for real analysis.

---

## PNT_PARTIAL_SUMMATION

### Name of formal statement
PNT_PARTIAL_SUMMATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PNT_PARTIAL_SUMMATION = prove
 (`&(CARD {p | prime p /\ p <= n}) =
        sum(1..n)
         (\k. &k / log (&k) *
              (sum {p | prime p /\ p <= k} (\p. log (&p) / &p) -
               sum {p | prime p /\ p <= k - 1} (\p. log (&p) / &p)))`,
  REWRITE_TAC[PRIME_ATMOST_ALT] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (PAT_CONV `\x. l = a * (sum(1..x) f - s)`)
        [MATCH_MP (ARITH_RULE `1 <= p ==> p = SUC(p - 1)`) th]) THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= p ==> SUC(p - 1) = p`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < x /\ &0 < y ==> &1 = x / y * y / x`) THEN
  ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; LE_1; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`]);;
```

### Informal statement
For any natural number $n$, the cardinality of the set of prime numbers less than or equal to $n$ can be expressed using partial summation as follows:
$$|\{p \mid p \text{ is prime} \wedge p \leq n\}| = \sum_{k=1}^{n} \frac{k}{\log k} \cdot \left(\sum_{p \in \{p \mid p \text{ is prime} \wedge p \leq k\}} \frac{\log p}{p} - \sum_{p \in \{p \mid p \text{ is prime} \wedge p \leq k-1\}} \frac{\log p}{p}\right)$$

### Informal proof
The proof proceeds through algebraic manipulation and application of summation properties:

- Start by rewriting the set of primes using `PRIME_ATMOST_ALT` to express it as $\{p \mid p \in 1..n \wedge p \text{ is prime}\}$
- Transform the left-hand side by multiplying by 1: $|\{p \mid p \text{ is prime} \wedge p \leq n\}| = |\{p \mid p \text{ is prime} \wedge p \leq n\}| \cdot 1$
- Apply summation properties to rewrite this as a sum over the set
- Rewrite the sum over a set restriction as a sum over the range 1..n with a conditional expression
- For each $p$ in the range 1..n, use that $p = \text{SUC}(p-1)$ for $p \geq 1$
- Apply the summation clauses for ranges to expand the summation
- Simplify using arithmetic and substitution of $\text{SUC}(p-1) = p$ when $p \geq 1$
- For the case where $p$ is prime, show that the expression evaluates to 1 using the field property: if $x, y > 0$ then $1 = \frac{x}{y} \cdot \frac{y}{x}$
- Verify that the necessary conditions are met by showing $\log p > 0$ for $p \geq 2$ and using the fact that all primes are $\geq 2$
- When $p$ is not prime, the indicator function evaluates to 0, which matches the sum's value

### Mathematical insight
This theorem reformulates the Prime Number Theorem (PNT) using partial summation. The key idea is to express the counting function of primes ($\pi(n)$) using a weighted sum involving logarithmic terms. This transformation is part of the analytical approach to studying the distribution of prime numbers.

The partial summation technique allows us to relate the count of primes to the logarithmic weights, which connects to the asymptotic behavior described by the Prime Number Theorem. This formulation is particularly useful for analytical manipulations in the proof of the PNT.

This result serves as an intermediate step in establishing the relationship between the counting function $\pi(n)$ and the function $n/\log n$, which is at the heart of the Prime Number Theorem.

### Dependencies
- Theorems:
  - `PRIME_ATMOST_ALT`: Set equality showing that $\{p \mid \text{prime}(p) \wedge p \leq n\} = \{p \mid p \in 1..n \wedge \text{prime}(p)\}$

### Porting notes
When porting this theorem:
- Ensure that the target system has good support for summation over sets and ranges
- Verify that the logarithm function behaves consistently, especially regarding domains
- The proof relies heavily on arithmetic simplification and field properties, which may require different tactics in other systems

---

## SUM_PARTIAL_LIMIT

### Name of formal statement
SUM_PARTIAL_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_PARTIAL_LIMIT = prove
 (`!f e c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n + 1)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g") (LABEL_TAC "e")) THEN
  SUBGOAL_THEN `!k:num. M <= k ==> &0 <= f k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SIMP_TAC[tendsto_real] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?N. (!k. N <= k ==> &0 < f k) /\
                    (!k. N <= k ==> f(k) <= f(k + 1)) /\
                    (!k. N <= k ==> abs(e k - c) < d / &4)`
   (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)
  THENL
   [USE_THEN "e" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `d / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[ARITH_RULE `M + N <= (n:num) ==> M <= n /\ N <= n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N + 1 <= n
        ==> abs((sum((N+1)..n) (\k. e k * (f (k + 1) - f k)) -
                 e(n) * f(n + 1)) +
                c * f(N + 1))
            <= d / &2 * f(n + 1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\k. (e k - c:real) * (f (k + 1) - f k)`;
                   `\k. d / &4 * (f (k + 1) - f k)`;
                   `(N+1)..n`] SUM_ABS_LE) THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; ARITH_RULE `N + 1 <= n ==> N <= n`;
                   REAL_ARITH `a <= b ==> abs(b - a) = b - a`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_PARTIAL_SUC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
     [SUM_PARTIAL_SUC] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= d * f1 /\ &0 <= dd /\ abs(en - cn) <= d / &4 * f1
      ==> abs(s - (cn - cN)) <= d / &4 * f1 - dd
          ==> abs(s - en + cN) <= d / &2 * f1`) THEN
    REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_SUB_RDISTRIB] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_DIV; REAL_LT_IMP_LE; REAL_OF_NUM_LT;
                 ARITH; LE_ADD; ARITH_RULE `N + 1 <= n ==> N <= n + 1`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  USE_THEN "g" (MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `sum(1..N) (\k. e k * (f (k + 1) - f k)) - c * f(N + 1)`) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `N + 1 <= n`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `&0 < x ==> abs x = x`;
               ARITH_RULE `N + 1 <= n ==> N <= n + 1`; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REAL_ARITH_TAC);;
```

### Informal statement
Let $f$ be a sequence of positive reals that is monotonically increasing from some index $M$ onwards, and such that $\frac{1}{f(k)} \to 0$ as $k \to \infty$. Let $e$ be a sequence converging to a limit $c$. Then the sequence 
$$\frac{\sum_{k=1}^n e(k) \cdot (f(k+1) - f(k)) - e(n) \cdot f(n+1)}{f(n+1)}$$
converges to $0$ as $n \to \infty$.

### Informal proof
The proof proceeds by establishing bounds on the terms of the sequence to show it converges to zero:

1. First, we establish that $f(k) \geq 0$ for all $k \geq M$ as an immediate consequence of $f(k) > 0$.

2. Since $e(k) \to c$, for any $d > 0$, there exists some $N$ such that for all $k \geq N$:
   - $f(k) > 0$
   - $f(k) \leq f(k+1)$ (monotonicity)
   - $|e(k) - c| < \frac{d}{4}$

3. The core of the proof involves showing that for all $n \geq N+1$:
   $$\left|\left(\sum_{k=N+1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)\right) + cf(N+1)\right| \leq \frac{d}{2}f(n+1)$$

   This is established by:
   - Using the triangle inequality and bounds on $|e(k) - c|$
   - Applying properties of summations and partial sums
   - Leveraging the monotonicity of $f$

4. The final step uses the fact that $\frac{1}{f(k)} \to 0$ to conclude that
   $$\frac{\sum_{k=1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)}{f(n+1)} \to 0$$

   This follows by combining the previously established bound with the fact that any fixed term multiplied by $\frac{1}{f(n+1)}$ converges to zero.

### Mathematical insight
This theorem provides a limiting result for a weighted sum of terms where both the weights $e(k)$ and the differences in an increasing sequence $f$ are involved. It's useful in analysis when studying weighted summation methods, particularly for series with monotone behavior.

The key insight is that when dividing by $f(n+1)$, which grows large, the partial sum adjusted by the boundary term $e(n)f(n+1)$ becomes negligible. This is a common pattern in asymptotic analysis where the behavior of weighted sums depends on both the convergence of the coefficients and the growth rate of the weights.

### Dependencies
None explicitly provided in the input.

### Porting notes
When implementing this theorem in other proof assistants:
- Pay careful attention to the handling of sequences, which may have different conventions in different systems
- The proof relies heavily on algebraic manipulation of sums and inequalities, which should translate straightforwardly
- The theorem uses sequential limits (indicated by `---> sequentially` in HOL Light), which should be mapped to the appropriate limit concept in the target system

---

## SUM_PARTIAL_LIMIT_ALT

### Name of formal statement
SUM_PARTIAL_LIMIT_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_PARTIAL_LIMIT_ALT = prove
 (`!f e b c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        ((\n. f(n + 1) / f n) ---> b) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
         f(n + 1)) * (f(n + 1) / f(n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `M:num` THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a /\ &0 < b ==> x / b * b / a = x / a`;
                 ARITH_RULE `M <= n ==> M <= n + 1`];
    ALL_TAC] THEN
  SUBST1_TAC(REAL_ARITH `&0 = &0 * b`) THEN
  MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_PARTIAL_LIMIT THEN ASM_MESON_TAC[]);;
```

### Informal statement
For all functions $f$ and $e$ from natural numbers to real numbers, and for all real numbers $b$, $c$, and natural number $M$, if:
1. $\forall k. M \leq k \Rightarrow 0 < f(k)$ (i.e., $f(k)$ is positive for all $k \geq M$)
2. $\forall k. M \leq k \Rightarrow f(k) \leq f(k+1)$ (i.e., $f(k)$ is non-decreasing for all $k \geq M$)
3. $\left(\lambda k. \frac{1}{f(k)}\right) \to 0$ sequentially (i.e., $\lim_{k\to\infty} \frac{1}{f(k)} = 0$)
4. $\left(\lambda n. \frac{f(n+1)}{f(n)}\right) \to b$ sequentially (i.e., $\lim_{n\to\infty} \frac{f(n+1)}{f(n)} = b$)
5. $e \to c$ sequentially (i.e., $\lim_{n\to\infty} e(n) = c$)

Then
$$\left(\lambda n. \frac{\sum_{k=1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)}{f(n)}\right) \to 0$$
sequentially.

### Informal proof
To prove this theorem, we'll transform the sequence into one for which we already know the limit, and then apply the properties of limits.

Let's start by introducing a transformation of our sequence:
$$\left(\frac{\sum_{k=1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)}{f(n)}\right) = \left(\frac{\sum_{k=1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)}{f(n+1)}\right) \cdot \frac{f(n+1)}{f(n)}$$

We'll show that this transformation is valid eventually (for all $n \geq M$) and then prove that the transformed sequence converges to 0.

* First, we note that for all $n \geq M$, $f(n) > 0$ and $f(n+1) > 0$ by our assumptions. 
* For all such $n$, by the field properties of real numbers, we have:
  $$\frac{x}{f(n+1)} \cdot \frac{f(n+1)}{f(n)} = \frac{x}{f(n)}$$

* To find the limit of the transformed sequence, we use the product rule for limits.
* The first factor $\left(\frac{\sum_{k=1}^n e(k)(f(k+1) - f(k)) - e(n)f(n+1)}{f(n+1)}\right)$ converges to 0 by the `SUM_PARTIAL_LIMIT` theorem, as all prerequisites for applying this theorem are satisfied by our assumptions.
* The second factor $\frac{f(n+1)}{f(n)}$ converges to $b$ by assumption.
* Therefore, the product converges to $0 \cdot b = 0$.

Thus, our original sequence converges to 0, which proves the theorem.

### Mathematical insight
This theorem provides an alternative version of the partial limit theorem for sums. It extends `SUM_PARTIAL_LIMIT` by introducing the additional assumption that $\frac{f(n+1)}{f(n)}$ converges to some limit $b$. 

The result deals with the asymptotic behavior of weighted differences in the context of monotonically increasing functions. It's particularly useful in analysis when studying convergence properties of sequences involving summations, especially when dealing with summation by parts techniques. The theorem allows us to transform certain sequences and determine their limits by leveraging known limit theorems.

### Dependencies
- Theorems:
  - `SUM_PARTIAL_LIMIT`: The primary theorem that this result builds upon
  - `REALLIM_TRANSFORM_EVENTUALLY`: Allows transformation of a sequence when calculating limits
  - `REALLIM_MUL`: Product rule for sequential limits of real sequences

### Porting notes
When porting this theorem:
1. Make sure that the prerequisite theorems about sequential limits are available in the target system
2. Pay attention to how sequential limits are defined in the target system - they might use different notation or slightly different definitions
3. The proof relies heavily on algebraic manipulation of real expressions, so the target system should have good support for algebraic reasoning about real numbers

The proof is relatively straightforward when the dependencies are available, as it mainly involves sequence transformation and application of limit theorems.

---

## REALLIM_NA_OVER_N

### REALLIM_NA_OVER_N
- REALLIM_NA_OVER_N

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REALLIM_NA_OVER_N = prove
 (`!a. ((\n. (&n + a) / &n) ---> &1) sequentially`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N]]);;
```

### Informal statement
For any real number $a$, the sequence $\frac{n+a}{n}$ converges to $1$ as $n$ approaches infinity.

Formally: $\forall a \in \mathbb{R}. \lim_{n\to\infty} \frac{n+a}{n} = 1$

### Informal proof
The proof shows that the sequence $\frac{n+a}{n}$ converges to $1$ for any real number $a$:

1. First, rewrite $\frac{n+a}{n}$ as $\frac{n}{n} + \frac{a}{n}$ using the distributive property of division over addition.

2. Further rewrite this as $(1 + \frac{a}{n})$ by recognizing that $\frac{n}{n} = 1$.

3. Now we can apply the limit addition theorem (`REALLIM_ADD`), which states that the limit of a sum equals the sum of limits:
   - Show that $\lim_{n\to\infty} 1 = 1$ (trivial as it's a constant sequence)
   - Show that $\lim_{n\to\infty} \frac{a}{n} = 0$

4. For the first part:
   - Apply `REALLIM_TRANSFORM_EVENTUALLY` to establish that the sequence $\frac{n}{n}$ eventually equals the constant sequence $1$
   - Use `REALLIM_CONST` which states that the limit of a constant sequence is that constant

5. For the second part:
   - Apply `REALLIM_NULL_LMUL` which states that if a sequence converges to 0, then multiplying by a constant also converges to 0
   - Use `REALLIM_1_OVER_N` which states that $\lim_{n\to\infty} \frac{1}{n} = 0$
   - This shows that $\lim_{n\to\infty} \frac{a}{n} = a \cdot \lim_{n\to\infty} \frac{1}{n} = a \cdot 0 = 0$

6. Combining the two results, we get $\lim_{n\to\infty} \frac{n+a}{n} = 1 + 0 = 1$

### Mathematical insight
This theorem establishes a basic limit result in real analysis. It demonstrates that adding a constant to the numerator of a fraction with a growing denominator doesn't affect the limit in the long run. This is intuitive because as $n$ grows large, the contribution of the constant term $a$ becomes negligible compared to $n$.

This result is part of a larger collection of elementary limit theorems and is useful for evaluating limits of rational functions. It illustrates how a rational function behaves asymptotically when the degree of the numerator and denominator are the same (in this case, both degree 1), resulting in a limit equal to the ratio of the leading coefficients.

### Dependencies
- `REALLIM_ADD`: The limit of a sum is the sum of the limits
- `REALLIM_TRANSFORM_EVENTUALLY`: If two sequences are eventually equal, they have the same limit
- `REALLIM_CONST`: The limit of a constant sequence is that constant
- `REALLIM_NULL_LMUL`: If a sequence converges to 0, then multiplying it by a constant also converges to 0
- `REALLIM_1_OVER_N`: The limit of 1/n as n approaches infinity is 0

### Porting notes
When porting this theorem to other systems:
- Ensure that the limit theorems (`REALLIM_ADD`, `REALLIM_NULL_LMUL`, etc.) are available or ported first
- Be aware of how the target system handles the distinction between natural numbers and reals
- The notation `&n` in HOL Light represents the injection from natural numbers to reals, which may be handled differently in other systems
- The sequential limit notation may differ in other proof assistants

---

## REALLIM_N_OVER_NA

### Name of formal statement
REALLIM_N_OVER_NA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_N_OVER_NA = prove
 (`!a. ((\n. &n / (&n + &1)) ---> &1) sequentially`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_NA_OVER_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For any real number $a$, the sequence $\left(\frac{n}{n + 1}\right)_{n=1}^{\infty}$ converges to $1$.

Formally:
$$\forall a.\ \lim_{n \to \infty} \frac{n}{n + 1} = 1$$
where the limit is taken with respect to the sequential topology.

### Informal proof
We prove that $\lim_{n \to \infty} \frac{n}{n + 1} = 1$ by applying the properties of limits.

1. First, we rewrite $\frac{n}{n + 1}$ as $\frac{1}{\frac{n + 1}{n}}$ using the property that $\frac{a}{b} = \frac{1}{\frac{b}{a}}$

2. Next, we rewrite $1$ as $\frac{1}{1}$ to prepare for applying the limit of reciprocal theorem

3. We then use the theorem about the limit of reciprocals: if $\lim_{n \to \infty} f(n) = L$ where $L \neq 0$, then $\lim_{n \to \infty} \frac{1}{f(n)} = \frac{1}{L}$

4. We know from `REALLIM_NA_OVER_N` that $\lim_{n \to \infty} \frac{n + 1}{n} = 1$

5. Therefore, applying the limit of reciprocals theorem, we get $\lim_{n \to \infty} \frac{n}{n + 1} = \lim_{n \to \infty} \frac{1}{\frac{n + 1}{n}} = \frac{1}{1} = 1$

### Mathematical insight
This theorem establishes that the sequence $\frac{n}{n + 1}$ converges to 1, which is a basic result in calculus and analysis. This particular form often appears in various limit calculations and is useful in proving more complex limit results.

The intuition behind this result is that as $n$ grows very large, adding 1 to $n$ in the denominator becomes negligible relative to $n$ itself, so the ratio approaches 1. This is an instance of the more general principle that for any constant $a$, $\lim_{n \to \infty} \frac{n}{n + a} = 1$.

### Dependencies
- Theorems:
  - `REALLIM_NA_OVER_N`: States that $\lim_{n \to \infty} \frac{n + a}{n} = 1$ for any real constant $a$
  - `REALLIM_INV`: Theorem about taking limits of reciprocals
  - `REAL_INV_DIV`: Property that $\frac{1}{a/b} = \frac{b}{a}$
  - `REAL_INV_1`: Property that $\frac{1}{1} = 1$

### Porting notes
When porting this theorem:
1. Ensure that the targeted system has theorems about limits of reciprocals and appropriate algebraic manipulations of fractions.
2. The proof relies on the theorem `REALLIM_NA_OVER_N`, so that should be ported first.
3. The proof uses algebraic rewriting of real fractions, which should be straightforward in most formal systems.

---

## REALLIM_LOG1_OVER_LOG

### Name of formal statement
REALLIM_LOG1_OVER_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_LOG1_OVER_LOG = prove
 (`((\n. log(&n + &1) / log(&n)) ---> &1) sequentially`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. &1 + log(&1 + &1 / &n) / log(&n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_ARITH `&2 <= x ==> &1 < x`;
       REAL_FIELD `&0 < x ==> (&1 + a / x = b / x <=> x + a = b)`] THEN
    ASM_SIMP_TAC[GSYM LOG_MUL; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
                 REAL_LE_DIV; REAL_POS; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
    AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n)` THEN REWRITE_TAC[REALLIM_1_OVER_N] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_LE_INV_EQ; REAL_POS;
                 REAL_ARITH `&0 <= x ==> &1 <= &1 + x`] THEN
    MATCH_MP_TAC LOG_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * log(&2)` THEN
  CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;
```

### Informal statement
The sequence $\left(\frac{\log(n + 1)}{\log(n)}\right)_{n=1}^{\infty}$ converges to $1$.

More precisely, the statement says that:
$\lim_{n \to \infty} \frac{\log(n + 1)}{\log(n)} = 1$

### Informal proof
We prove that $\lim_{n \to \infty} \frac{\log(n + 1)}{\log(n)} = 1$ using the following steps:

1. First, we transform the sequence to show that eventually:
   $\frac{\log(n + 1)}{\log(n)} = 1 + \frac{\log(1 + \frac{1}{n})}{\log(n)}$
   
   This is done by observing that for $n \geq 2$:
   - $\log(n)$ is positive
   - $\log(n+1) = \log(n \cdot (1 + \frac{1}{n})) = \log(n) + \log(1 + \frac{1}{n})$
   - Therefore $\frac{\log(n+1)}{\log(n)} = 1 + \frac{\log(1 + \frac{1}{n})}{\log(n)}$

2. Next, we use the fact that $\lim_{n \to \infty} 1 = 1$ and focus on showing that 
   $\lim_{n \to \infty} \frac{\log(1 + \frac{1}{n})}{\log(n)} = 0$

3. We apply a comparison approach to prove this limit is 0:
   - We show that eventually $\left|\frac{\log(1 + \frac{1}{n})}{\log(n)}\right| \leq \frac{1}{n}$
   - Since $\lim_{n \to \infty} \frac{1}{n} = 0$, this establishes our result by the squeeze theorem

4. In detail, for $n \geq 16$:
   - $|\log(1 + \frac{1}{n})| \leq \frac{1}{n}$ as $\log(1 + x) \leq x$ for $x \geq 0$
   - $\frac{1}{|\log(n)|} \leq 1$ since $\log(n) \geq 2\log(2) \geq 1$ for large enough $n$
   - Therefore $\left|\frac{\log(1 + \frac{1}{n})}{\log(n)}\right| \leq \frac{1}{n}$

5. By the squeeze theorem and $\lim_{n \to \infty} \frac{1}{n} = 0$, we conclude that 
   $\lim_{n \to \infty} \frac{\log(1 + \frac{1}{n})}{\log(n)} = 0$

6. Thus, $\lim_{n \to \infty} \frac{\log(n + 1)}{\log(n)} = 1 + 0 = 1$

### Mathematical insight
This result shows that for large values of $n$, the logarithms of consecutive integers become arbitrarily close, proportionally speaking. This is a specific case of a more general phenomenon: as $n$ grows, the logarithmic function flattens out, making the relative difference between $\log(n+1)$ and $\log(n)$ approach zero.

The result is used in various asymptotic analyses, particularly in number theory and algorithm analysis where logarithmic growth rates are important. It shows that for large $n$, we can essentially treat $\log(n+1)$ and $\log(n)$ as equal for many asymptotic calculations.

### Dependencies
- `LOG_2_BOUNDS`: The theorem that $\frac{1}{2} \leq \log(2) \leq 1$
- HOL Light standard library functions: `REALLIM_TRANSFORM_EVENTUALLY`, `REALLIM_ADD`, `REALLIM_CONST`, `REALLIM_NULL_COMPARISON`, `REALLIM_1_OVER_N`
- Properties of logarithms: `LOG_POS_LT`, `LOG_MUL`, `LOG_LE`, `LOG_MONO_LE_IMP`, `LOG_POW`

### Porting notes
When porting this theorem to another system:
1. Ensure that the target system has well-developed libraries for limits of sequences and logarithmic functions.
2. The proof relies on several properties of logarithms and limits, so make sure these basic properties are available.
3. The transformation step and comparison approach are standard mathematical techniques that should translate well across systems.
4. The particular bound used ($\log(n) \geq 2\log(2)$ for $n \geq 16$) may need adjustment depending on the exact logarithm properties available in the target system.

---

## REALLIM_LOG_OVER_LOG1

### Name of formal statement
REALLIM_LOG_OVER_LOG1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_LOG_OVER_LOG1 = prove
 (`((\n. log(&n) / log(&n + &1)) ---> &1) sequentially`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_LOG1_OVER_LOG] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
This theorem states that the sequence $\left(\frac{\log(n)}{\log(n+1)}\right)_{n=1}^{\infty}$ converges to $1$ as $n$ approaches infinity.

Mathematically, it asserts:
$$\lim_{n \to \infty} \frac{\log(n)}{\log(n+1)} = 1$$

### Informal proof
The proof proceeds as follows:

1. First, we rewrite the expression using the fact that $\frac{a}{b} = \frac{1}{\frac{b}{a}}$ for $a \neq 0$:
   $$\frac{\log(n)}{\log(n+1)} = \frac{1}{\frac{\log(n+1)}{\log(n)}}$$

2. We then use the fact that if a sequence $a_n$ converges to $L$, then $\frac{1}{a_n}$ converges to $\frac{1}{L}$ (provided $L \neq 0$).

3. We apply this to the sequence $\frac{\log(n+1)}{\log(n)}$, which converges to $1$ as shown by the theorem `REALLIM_LOG1_OVER_LOG`.

4. Since $\frac{1}{1} = 1$, we conclude that $\frac{\log(n)}{\log(n+1)}$ converges to $1$.

### Mathematical insight
This theorem establishes that the logarithm functions of consecutive natural numbers become asymptotically equivalent as $n$ grows large. This is an example of how logarithmic growth rates become increasingly similar for large inputs, which is a fundamental concept in asymptotic analysis.

The result is a companion to `REALLIM_LOG1_OVER_LOG`, which establishes the convergence of the reciprocal ratio $\frac{\log(n+1)}{\log(n)} \to 1$. Together, they show that $\log(n)$ and $\log(n+1)$ become essentially interchangeable for asymptotic analyses.

### Dependencies
#### Theorems
- `REALLIM_LOG1_OVER_LOG`: Establishes that $\lim_{n \to \infty} \frac{\log(n+1)}{\log(n)} = 1$
- `REALLIM_INV`: If $a_n \to L \neq 0$, then $\frac{1}{a_n} \to \frac{1}{L}$
- `REAL_INV_DIV`: $\frac{1}{\frac{a}{b}} = \frac{b}{a}$ (for $a \neq 0$)
- `REAL_INV_1`: $\frac{1}{1} = 1$

### Porting notes
When porting this theorem, ensure that the underlying theorems about limits and logarithms are already available. The proof is straightforward and should translate well to other systems, as it relies on basic properties of limits and logarithms rather than on HOL Light-specific tactics.

---

## ADHOC_BOUND_LEMMA

### Name of formal statement
ADHOC_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ADHOC_BOUND_LEMMA = prove
 (`!k. 1 <= k ==> abs((&k + &1) * (log(&k + &1) - log(&k)) - &1)
                  <= &2 / &k`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then clog z
           else if n = 1 then inv z
           else --inv(z pow 2)`;
    `Cx(&k + &1)`; `Cx(&k)`; `1`]
        COMPLEX_TAYLOR_MVT) THEN
  REWRITE_TAC[ARITH; ADD_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_DIV_1; complex_pow; COMPLEX_POW_1; COMPLEX_VEC_0] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_ADD_RID;
              REAL_ARITH `k - (k + &1) = -- &1`] THEN
  REWRITE_TAC[CX_SUB; CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG;
              COMPLEX_NEG_NEG; COMPLEX_MUL_RID] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN
    REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH] THEN
    COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; complex_div; COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k /\ &0 < &k + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[RE_ADD] THEN
  ONCE_REWRITE_TAC[REAL_RING `w:real = z + u <=> w - z = u`] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_INV; GSYM CX_ADD; GSYM CX_SUB;
               GSYM CX_NEG; RE_CX] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (&k + &1)`) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < x ==> x * (y - (z + --inv x)) = &1 - x * (z - y)`] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
  REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_MUL; GSYM CX_POW; GSYM CX_INV; RE_CX] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_POW_INV; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d = (a * b:real) * (c * d)`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_LE_LDIV_EQ;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $k$ such that $1 \leq k$, the following inequality holds:
$$\left| (k + 1) \cdot (\ln(k + 1) - \ln(k)) - 1 \right| \leq \frac{2}{k}$$

### Informal proof
This theorem is proved using Taylor's Mean Value Theorem (TMVT) from complex analysis.

1. First, we set up the application of Complex Taylor's Mean Value Theorem with:
   - Function $f$ defined piecewise as:
     - $f(0,z) = \ln(z)$
     - $f(1,z) = 1/z$
     - $f(n,z) = -1/z^2$ for $n > 1$
   - Points $z_1 = k+1$ and $z_0 = k$ 
   - Order $n = 1$

2. After setting up the TMVT, we verify that $f$ is differentiable on the segment between $k$ and $k+1$, noting that both points are positive real numbers.

3. By the TMVT, there exists a point $z$ on the line segment between $k$ and $k+1$ such that:
   $$\ln(k+1) - \ln(k) = \frac{1}{z} \cdot (k+1 - k) = \frac{1}{z}$$

4. Multiplying both sides by $(k+1)$:
   $$(k+1)(\ln(k+1) - \ln(k)) = \frac{k+1}{z}$$

5. We observe that $(k+1)(\ln(k+1) - \ln(k)) - 1 = \frac{k+1}{z} - 1$

6. Since $z$ lies on the segment between $k$ and $k+1$, we can express $z = k + t(k+1-k) = k + t$ for some $t \in [0,1]$.

7. Computing the absolute difference:
   $$\left|\frac{k+1}{z} - 1\right| = \left|\frac{k+1 - z}{z}\right| = \left|\frac{k+1 - (k+t)}{k+t}\right| = \left|\frac{1-t}{k+t}\right|$$

8. Since $z = k+t$ where $0 \leq t \leq 1$ and $k \geq 1$, we know that $k+t \geq k \geq 1$ and $|1-t| \leq 1$.

9. Therefore:
   $$\left|\frac{1-t}{k+t}\right| \leq \frac{1}{k} \cdot \frac{k}{k+t} \leq \frac{1}{k} \cdot 1 = \frac{1}{k}$$

10. The proof continues with further refinement of the bounds, ultimately showing that the absolute difference is at most $\frac{2}{k}$.

### Mathematical insight
This lemma establishes a bound on how close $(k+1)(\ln(k+1) - \ln(k))$ is to 1. This quantity is particularly significant as $\ln(k+1) - \ln(k)$ is the difference of logarithms, which approximates the derivative of the natural logarithm function at $k$ (i.e., $\frac{1}{k}$).

The result shows that as $k$ gets larger, this approximation becomes increasingly accurate, with the error bounded by $\frac{2}{k}$. This is an example of a technical lemma that would be used in analysis to establish convergence rates or error bounds.

The proof technique uses complex analysis (Taylor's Mean Value Theorem) to establish a real-valued inequality, which is a common approach in analysis.

### Dependencies
- **Theorems:**
  - `COMPLEX_TAYLOR_MVT`: Complex Taylor's Mean Value Theorem
  - Various arithmetic, logic and real number theorems

- **Definitions:**
  - Complex logarithm (`clog`)
  - Complex functions and operations

### Porting notes
When porting this proof to other systems:
1. Ensure that the target system has an equivalent of the Complex Taylor's Mean Value Theorem
2. The proof heavily relies on real arithmetic simplifications - these may need different tactics in other systems
3. Note the piecewise definition of the function used in the Taylor MVT application
4. The proof uses complex numbers to prove a real-valued result, so ensure that the target system has good support for complex analysis

---

## REALLIM_MUL_SERIES

### REALLIM_MUL_SERIES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REALLIM_MUL_SERIES = prove
 (`!x y z B.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        eventually (\n. abs(sum (1..n) x / z(n)) <= B) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REWRITE_TAC[CONJ_ASSOC; GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[tendsto_real] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ASSUME
   `eventually (\n. &0 < x n /\ &0 < y n /\ &0 < z n) sequentially`) THEN
  MP_TAC(ASSUME `((\n. y n / x n) ---> &0) sequentially`) THEN
  REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&1 + abs B))`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_HALF; IMP_IMP; GSYM EVENTUALLY_AND] THEN
  GEN_REWRITE_TAC LAND_CONV [EVENTUALLY_SEQUENTIALLY] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `((\n. inv (z n)) ---> &0) sequentially`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `e / (&2 * (&1 + abs B)) * abs(sum(1..N) x) + abs(sum(1..N) y)`) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MP_TAC(ASSUME
   `eventually (\n. abs (sum (1..n) x / z n) <= B) sequentially`) THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `!x. abs(x) / z(n:num) = abs(x / z n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM real_div] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y'. abs(y) <= y' /\ abs(x) + y' < e ==> abs(x + y) < e`) THEN
  EXISTS_TAC `e / (&2 * (&1 + abs B)) * sum(N+1..n) x / z n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ABS_MUL; REAL_ABS_INV;
                 REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`;
                 REAL_LE_RMUL_EQ; REAL_LT_INV_EQ; REAL_MUL_ASSOC;
                 GSYM REAL_LE_LDIV_EQ] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ abs x < y ==> x <= y`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(d * abs xN + abs yN) < e / &2
    ==> d * abs xN = abs(d * xN) /\ abs(d * xN + xn) <= e / &2
        ==> abs(yN) + xn < e`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM;
              GSYM REAL_ADD_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`;
               REAL_ARITH `abs(&1 + abs B) = &1 + abs B`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(e * inv(&2) * i) * x = (e * inv(&2)) * x * i`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs B`] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
Let $x_n$, $y_n$, and $z_n$ be sequences of positive real numbers, and let $B$ be a real number. If:
1. $(x_n)$, $(y_n)$, and $(z_n)$ are eventually positive sequences
2. $\frac{1}{z_n} \to 0$ as $n \to \infty$
3. Eventually, $\left|\frac{\sum_{i=1}^n x_i}{z_n}\right| \leq B$ for all sufficiently large $n$
4. $\frac{y_n}{x_n} \to 0$ as $n \to \infty$

Then:
$\frac{\sum_{i=1}^n y_i}{z_n} \to 0$ as $n \to \infty$

### Informal proof
We need to show that for any $\varepsilon > 0$, there exists $N$ such that for all $n \geq N$, $\left|\frac{\sum_{i=1}^n y_i}{z_n}\right| < \varepsilon$.

1. Since $(x_n)$, $(y_n)$, and $(z_n)$ are eventually positive, there exists some index where all three sequences maintain positive values.

2. From the assumption that $\frac{y_n}{x_n} \to 0$, we can choose $N_1$ such that for all $n \geq N_1$:
   $\left|\frac{y_n}{x_n}\right| < \frac{\varepsilon}{2(1+|B|)}$

3. Since $\frac{1}{z_n} \to 0$, we can utilize this to show that 
   $\frac{1}{z_n} \cdot \left(\frac{\varepsilon}{2(1+|B|)} \cdot \left|\sum_{i=1}^{N_1} x_i\right| + \left|\sum_{i=1}^{N_1} y_i\right|\right) \to 0$

4. This means we can choose $N_2$ such that for all $n \geq N_2$:
   $\frac{1}{z_n} \cdot \left(\frac{\varepsilon}{2(1+|B|)} \cdot \left|\sum_{i=1}^{N_1} x_i\right| + \left|\sum_{i=1}^{N_1} y_i\right|\right) < \frac{\varepsilon}{2}$

5. From the assumption that $\left|\frac{\sum_{i=1}^n x_i}{z_n}\right| \leq B$ eventually, let $N_3$ be such that this holds for all $n \geq N_3$.

6. Let $N = \max(N_1+1, N_2, N_3)$. For any $n \geq N$, we can split the sum:
   $\frac{\sum_{i=1}^n y_i}{z_n} = \frac{\sum_{i=1}^{N_1} y_i}{z_n} + \frac{\sum_{i=N_1+1}^n y_i}{z_n}$

7. For the second term, we can show:
   $\left|\frac{\sum_{i=N_1+1}^n y_i}{z_n}\right| \leq \frac{\varepsilon}{2(1+|B|)} \cdot \frac{\sum_{i=N_1+1}^n x_i}{z_n}$
   
   This follows because $\left|\frac{y_i}{x_i}\right| < \frac{\varepsilon}{2(1+|B|)}$ for $i \geq N_1$.

8. Using our bound on $\left|\frac{\sum_{i=1}^n x_i}{z_n}\right| \leq B$ and the bound from step 4, we conclude:
   $\left|\frac{\sum_{i=1}^n y_i}{z_n}\right| < \varepsilon$

Therefore, $\frac{\sum_{i=1}^n y_i}{z_n} \to 0$ as $n \to \infty$.

### Mathematical insight
This theorem provides a useful criterion for determining when a ratio of sums approaches zero. It's particularly valuable in analysis when dealing with series and their convergence properties. The theorem shows that if one sequence $(y_n)$ grows much slower than another sequence $(x_n)$ (in the sense that $\frac{y_n}{x_n} \to 0$), and if the sum of $x_n$ normalized by $z_n$ remains bounded, then the sum of $y_n$ normalized by the same $z_n$ must approach zero.

This result can be seen as a generalization of comparison tests for series, where we compare the behavior of one series to another with known properties. It's particularly useful for analyzing behavior of complicated sequences defined by summations.

### Dependencies
The proof uses standard results from real analysis, including:
- Properties of limits
- Arithmetic of real numbers
- Triangle inequality
- Properties of absolute values
- Properties of sums and series

### Porting notes
When implementing this theorem in another proof assistant:
- Ensure that the "eventually" predicate is properly defined to mean "for all sufficiently large n"
- The proof heavily relies on algebraic manipulation of real numbers and inequalities
- The splitting of sums at index N is a key technique in the proof that might require different approaches in different systems
- Pay attention to the handling of the absolute value function, especially with fractions

---

## REALLIM_MUL_SERIES_LIM

### Name of formal statement
REALLIM_MUL_SERIES_LIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REALLIM_MUL_SERIES_LIM = prove
 (`!x y z l.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        ((\n. sum (1..n) x / z(n)) ---> l) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_MUL_SERIES THEN
  EXISTS_TAC `x:num->real` THEN
  MP_TAC(MATCH_MP REAL_CONVERGENT_IMP_BOUNDED
   (ASSUME `((\n. sum (1..n) x / z n) ---> l) sequentially`)) THEN
  REWRITE_TAC[real_bounded] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[ALWAYS_EVENTUALLY; FORALL_IN_IMAGE; IN_UNIV]);;
```

### Informal statement
For sequences of real-valued functions $x$, $y$, and $z$, if:
1. Eventually, $x(n) > 0$ for all $n$ (with respect to the sequential filter)
2. Eventually, $y(n) > 0$ for all $n$
3. Eventually, $z(n) > 0$ for all $n$
4. $\frac{1}{z(n)} \to 0$ as $n \to \infty$
5. $\frac{\sum_{i=1}^{n}x(i)}{z(n)} \to l$ as $n \to \infty$ for some real number $l$
6. $\frac{y(n)}{x(n)} \to 0$ as $n \to \infty$

Then $\frac{\sum_{i=1}^{n}y(i)}{z(n)} \to 0$ as $n \to \infty$.

### Informal proof
The proof applies the theorem `REALLIM_MUL_SERIES` which requires a similar set of hypotheses but additionally requires that $\frac{\sum_{i=1}^{n}x(i)}{z(n)}$ is bounded by some constant.

Since we have the stronger condition that $\frac{\sum_{i=1}^{n}x(i)}{z(n)}$ converges to $l$, we can use `REAL_CONVERGENT_IMP_BOUNDED` to establish that this sequence is indeed bounded. 

We pass the existing $x$ to `REALLIM_MUL_SERIES` along with the bound obtained from the convergence property, which completes the proof.

### Mathematical insight
This theorem generalizes a convergence result for series. It shows that if one series $\sum x(i)$ has a nice asymptotic behavior when normalized by $z(n)$, and if $y(i)$ is asymptotically smaller than $x(i)$ in a pointwise sense, then the normalized series $\frac{\sum y(i)}{z(n)}$ converges to zero.

The result is particularly useful in analysis when dealing with comparison tests for series where the terms decrease at different rates. It provides conditions under which we can transfer convergence properties from one series to another.

The key insight is that we're exploiting both the behavior of individual terms (via $\frac{y(n)}{x(n)} \to 0$) and the normalized partial sums (via $\frac{\sum x(i)}{z(n)} \to l$).

### Dependencies
- Theorems:
  - `REALLIM_MUL_SERIES`: A theorem about the convergence of normalized series under certain conditions
  - `REAL_CONVERGENT_IMP_BOUNDED`: States that convergent real sequences are bounded

### Porting notes
When porting this theorem, note that:
1. The handling of "eventually" conditions (filter-based approach) may differ between systems
2. The notation for sequences and limits might require adaptation
3. The underlying real analysis library structure could differ substantially between systems

Assistant systems will need appropriate theorems about convergence and boundedness of real sequences.

---

## PNT

### PNT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem (proved via `prove`)

### Formal Content
```ocaml
let PNT = prove
 (`((\n. &(CARD {p | prime p /\ p <= n}) / (&n / log(&n)))
    ---> &1) sequentially`,
  REWRITE_TAC[PNT_PARTIAL_SUMMATION] THEN
  REWRITE_TAC[SUM_PARTIAL_PRE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; SUB_REFL; CONJUNCT1 LE] THEN
  SUBGOAL_THEN `{p | prime p /\ p = 0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) *
         sum {p | prime p /\ p <= n} (\p. log(&p) / &p) -
         sum (1..n)
         (\k. sum {p | prime p /\ p <= k} (\p. log(&p) / &p) *
              ((&k + &1) / log(&k + &1) - &k / log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * log(&n) -
         sum (1..n)
         (\k. log(&k) * ((&k + &1) / log(&k + &1) - &k / log(&k)))) /
        (&n / log(&n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(a * x - s) / b - (a * x' - s') / b:real =
      ((s' - s) - (x' - x) * a) / b`] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC SUM_PARTIAL_LIMIT_ALT THEN
    EXISTS_TAC `&1` THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `16` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[MERTENS_LIMIT] THEN REWRITE_TAC[REAL_INV_DIV] THEN
    SIMP_TAC[REAL_LT_DIV; LOG_POS_LT; REAL_OF_NUM_LT;
             ARITH_RULE `16 <= n ==> 0 < n /\ 1 < n`] THEN
    REWRITE_TAC[REALLIM_LOG_OVER_N] THEN CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
      REWRITE_TAC[REAL_MUL_AC]] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`\z. z / clog z`; `\z. inv(clog z) - inv(clog z) pow 2`;
                  `Cx(&n)`; `Cx(&n + &1)`]
                COMPLEX_MVT_LINE) THEN
    REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
    REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
       [SUBGOAL_THEN `~(z = Cx(&0))` MP_TAC THENL
         [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
        REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
      REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_ARITH `&16 <= x ==> &0 < x`] THEN
      REWRITE_TAC[CX_INJ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
    REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 < Re z /\ &0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_POW; GSYM CX_INV; GSYM CX_SUB;
                 GSYM CX_DIV; RE_CX; GSYM CX_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_SUB; REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH `x pow 2 <= x <=> x * x <= x * &1`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN ONCE_REWRITE_TAC[SUM_PARTIAL_SUC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * (log(&n) - log(&n + &1)) +
         sum(1..n) (\k. (&k + &1) / log(&k + &1) *
                        (log(&k + &1) - log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_OF_NUM_ADD; LOG_1; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC i`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a * (x - y) + s + a * (y - x):real = s`] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. sum(1..n) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) /
        ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
    EXISTS_TAC `\n. ((&n + &2) / log (&n + &2) +
                   (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &17 / log (&17))) / ((&n + &1) / log (&n + &1))` THEN
    EXISTS_TAC `\n.  ((&n + &1) / log(&n + &1) +
                (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &16 / log (&16))) / ((&n + &1) / log (&n + &1))` THEN
    MP_TAC(GEN `n:num` (ISPECL
     [`\z. Cx(&1) / clog(z + Cx(&1)) - Cx(&1) / (clog(z + Cx(&1))) pow 2`;
      `\z. (z + Cx(&1)) / clog(z + Cx(&1))`;
      `16`; `n:num`]
     SUM_INTEGRAL_BOUNDS_DECREASING)) THEN
    MATCH_MP_TAC(MESON[]
     `(!n. P n ==> Q n) /\ ((!n. P n ==> R n) ==> s)
      ==> (!n. P n /\ Q n ==> R n) ==> s`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
        STRIP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        COMPLEX_DIFF_TAC THEN
        REWRITE_TAC[RE_ADD; RE_CX; GSYM CONJ_ASSOC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
         [SUBGOAL_THEN `~(z + Cx(&1) = Cx(&0))` MP_TAC THENL
           [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
          DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN SIMP_TAC[RE_ADD; RE_CX] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
        REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX; REAL_CX;
                     REAL_ARITH `&15 <= z ==> &0 < z + &1`; CX_INJ] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&15 <= y` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX;
                   REAL_ARITH `&15 <= x ==> &0 < x + &1`] THEN
      REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX; GSYM CX_POW] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
      REWRITE_TAC[REAL_ARITH
       `x - x pow 2 <= y - y pow 2 <=>
          (x + y) * (y - x) <= &1 * (y - x)`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= inv(&2) /\ y <= x
        ==> y + x <= &1 /\ &0 <= x - y`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
        CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
        REWRITE_TAC[REAL_MUL_LID] THEN
        DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
        REWRITE_TAC[REAL_MUL_AC];
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
        EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN X_GEN_TAC `n:num` THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `&0 < log(&n + &1)` ASSUME_TAC THENL
         [ALL_TAC; POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD] THEN
        MATCH_MP_TAC LOG_POS_LT THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &1 / log(&k + &1) pow 2 +
                                 &2 / (&k * log(&k + &1))) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ abs(a - b) <= y ==> abs(a - x - b) <= x + y`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `&1 / l - m1 / l * x:real = --((m1 * x - &1) / l)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; ADHOC_BOUND_LEMMA] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &3 / log(&k + &1) pow 2) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ y <= x
      ==> abs(&1 * x + &2 * y) <= &3 * x`) THEN
    SUBGOAL_THEN `&0 < log(&m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_MP_TAC LOG_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC REALLIM_MUL_SERIES_LIM THEN
  MAP_EVERY EXISTS_TAC
   [`\n. &1 / log(&n + &1) - &1 / log(&n + &1) pow 2`; `&1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LID; REAL_SUB_LT] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    SUBGOAL_THEN `&1 < log(&n + &1)`
     (fun th -> SIMP_TAC[th; REAL_ARITH `&1 < x ==> &0 < x`; REAL_SUB_LT;
             REAL_LT_MUL; REAL_ARITH `x < x pow 2 <=> &0 < x * (x - &1)`]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE;
             REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`];
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
    REWRITE_TAC[REAL_INV_DIV; GSYM REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &2 / log(&n + &1)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_1_OVER_LOG)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `42` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 < log(&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_INV; REAL_ABS_POW;
               REAL_ARITH `&2 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT;
               REAL_ARITH `&2 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&2 < l ==> (inv(l) * &2) * l pow 2 = inv(inv(&2 * l))`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_MUL; real_div; GSYM REAL_POW_INV; REAL_MUL_LID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `l pow 2 <= l / &2
    ==> inv(&2) * l <= abs(l - l pow 2)`) THEN
  REWRITE_TAC[REAL_ARITH `l pow 2 <= l / &2 <=> &0 <= (&1 / &2 - l) * l`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_SUB_LE;
               ARITH_RULE `&2 < x ==> &0 <= x`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement

The Prime Number Theorem states that:

$$\lim_{n \to \infty} \frac{\pi(n)}{\frac{n}{\log(n)}} = 1$$

where $\pi(n)$ is the prime counting function, i.e., the number of primes less than or equal to $n$. In HOL Light notation, this is expressed as the sequence $\lambda n. \frac{|\{p \mid \text{prime}(p) \land p \leq n\}|}{\frac{n}{\log(n)}}$ converging to $1$.

### Informal proof

The proof proceeds through several main steps:

1. First, we apply `PNT_PARTIAL_SUMMATION` to rewrite the prime counting function in terms of a sum involving the Mangoldt function:
   $$|\{p \mid \text{prime}(p) \land p \leq n\}| = \sum_{k=1}^{n} \frac{k}{\log(k)} \left( \sum_{p \leq k} \frac{\log(p)}{p} - \sum_{p \leq k-1} \frac{\log(p)}{p} \right)$$

2. We use partial summation to rewrite this expression in a more tractable form, using `SUM_PARTIAL_PRE` and simplifying.

3. The proof then applies the Mertens theorem (`MERTENS_LIMIT`), which states that the sum $\sum_{p \leq n} \frac{\log(p)}{p} - \log(n)$ converges to a constant.

4. Through a series of analytical manipulations and limit theorems, we establish bounds for various terms and show that certain error terms converge to 0.

5. A key step involves applying `SUM_PARTIAL_LIMIT_ALT` to handle the limiting behavior of certain weighted sums.

6. We use properties of logarithms (like `REALLIM_LOG_OVER_LOG1`) to show that $\frac{\log(n)}{\log(n+1)} \to 1$.

7. For the more technical parts, we establish bounds like `ADHOC_BOUND_LEMMA` to control error terms and use `REALLIM_MUL_SERIES_LIM` to analyze the limiting behavior of certain products.

8. Finally, we show that all error terms vanish in the limit, completing the proof that $\frac{\pi(n)}{\frac{n}{\log(n)}} \to 1$.

### Mathematical insight

The Prime Number Theorem (PNT) is one of the most important results in analytic number theory. It provides an asymptotic distribution law for the prime numbers, showing that the number of primes up to $n$ is asymptotically equivalent to $\frac{n}{\log(n)}$.

This result explains the approximate density of primes among natural numbers and confirms what had been observed empirically - primes become less frequent as numbers get larger, but in a very precise way. The function $\frac{n}{\log(n)}$ is called the "prime number density" or "logarithmic integral approximation."

The formal proof in HOL Light follows the analytic approach using properties of the summatory function of the Mangoldt function and partial summation techniques. This avoids complex analysis, which is used in some traditional proofs (via the properties of the Riemann zeta function).

This theorem has profound implications in number theory, cryptography, and other fields. For example, many cryptographic protocols rely on the difficulty of factoring large numbers, which is related to the distribution of primes.

### Dependencies

**Main theorems:**
- `PNT_PARTIAL_SUMMATION`: Expresses the prime counting function using partial summation and the Mangoldt function
- `MERTENS_LIMIT`: States that the sum of $\frac{\log(p)}{p}$ over primes $p \leq n$ minus $\log(n)$ converges to a constant
- `SUM_PARTIAL_LIMIT_ALT`: Theorem about the limiting behavior of weighted partial sums
- `ADHOC_BOUND_LEMMA`: Provides a specific bound needed for error term analysis
- `REALLIM_LOG_OVER_LOG1`: Shows that $\frac{\log(n)}{\log(n+1)}$ converges to 1
- `REALLIM_NA_OVER_N`: Shows that $\frac{n+a}{n}$ converges to 1
- `REALLIM_MUL_SERIES_LIM`: Handles limit behavior of certain product series
- `LOG_2_BOUNDS`: Provides bounds for $\log(2)$

### Porting notes

When porting this theorem:

1. Most proof assistants will have established libraries for real analysis, so many of the limit operations should have direct equivalents.

2. The prime counting function might be defined differently in different libraries, so ensure consistency with existing number theory formalizations.

3. The proof relies heavily on the properties of logarithms, summations, and limits, which are standard in mathematical libraries but might have slightly different formulations.

4. Some of the more technical lemmas (like `ADHOC_BOUND_LEMMA`) might need to be ported or re-proved depending on the available machinery for real analysis.

5. The partial summation technique is crucial to this proof, so ensure your target system has a good formalization of this concept.

---

