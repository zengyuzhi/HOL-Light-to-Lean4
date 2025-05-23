# triangular.ml

## Overview

Number of statements: 5

This file formalizes a proof that the sum of the reciprocals of triangular numbers equals 2. It establishes the key result that the infinite sum ∑(1/n(n+1)) = 2 by using analysis techniques from the `analysis.ml` library. The proof likely involves expressing triangular numbers in the form n(n+1)/2 and manipulating infinite series.

## triangle

### Name of formal statement
triangle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let triangle = new_definition
 `triangle n = (n * (n + 1)) DIV 2`;;
```

### Informal statement
The function $\text{triangle}: \mathbb{N} \rightarrow \mathbb{N}$ is defined as:

$$\text{triangle}(n) = \frac{n(n+1)}{2}$$

This defines the $n$-th triangular number, which equals the sum of the first $n$ positive integers.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
Triangular numbers are a classic sequence in mathematics (1, 3, 6, 10, 15, ...) that count the number of objects that can be arranged in an equilateral triangle. The $n$-th triangular number equals the sum of the first $n$ positive integers: $1 + 2 + ... + n = \frac{n(n+1)}{2}$.

These numbers appear in various combinatorial problems and are named "triangular" because they can be represented as triangular arrangements of points. For example, the 4th triangular number (10) can be visualized as:
```
   •
  • •
 • • •
• • • •
```

The formula $\frac{n(n+1)}{2}$ is a well-known closed-form expression for calculating these numbers efficiently.

### Dependencies
No dependencies are listed for this definition.

### Porting notes
When porting this definition:
- Note that in HOL Light, `DIV` represents integer division
- Ensure that the target system handles division appropriately (especially if it distinguishes between integer and real division)
- Some systems might represent this directly as `n * (n + 1) / 2` where `/` is interpreted appropriately for natural numbers

---

## REAL_TRIANGLE

### Name of formal statement
REAL_TRIANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_TRIANGLE = prove
 (`&(triangle n) = (&n * (&n + &1)) / &2`,
  MATCH_MP_TAC(REAL_ARITH `&2 * x = y ==> x = y / &2`) THEN
  REWRITE_TAC[triangle; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
   [REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH] THEN CONV_TAC TAUT;
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC[ARITH]]);;
```

### Informal statement
The real value of the $n$-th triangle number equals $\frac{n(n+1)}{2}$. In mathematical notation:
$$\mathbb{R}(\text{triangle}(n)) = \frac{n(n+1)}{2}$$

where $\mathbb{R}(\cdot)$ represents the mapping of a natural number to its real value.

### Informal proof
The proof proceeds by establishing that $2 \cdot \mathbb{R}(\text{triangle}(n)) = n(n+1)$, which implies $\mathbb{R}(\text{triangle}(n)) = \frac{n(n+1)}{2}$.

- First, we apply a lemma stating that if $2x = y$ then $x = \frac{y}{2}$.
- We then rewrite according to the definition of triangle numbers and convert numeric operations to their real counterparts.
- Next, we establish that $n(n+1)$ is always even:
  - This follows because either $n$ or $n+1$ must be even, making their product even.
- Since $n(n+1)$ is even, we can express it as $n(n+1) = 2k$ for some integer $k$.
- Finally, we show that $k = \text{triangle}(n)$ by using the definition of integer division, specifically that $\frac{n(n+1)}{2}$ is an exact division without remainder.

### Mathematical insight
Triangle numbers are the sum of the first $n$ natural numbers: $\text{triangle}(n) = 1 + 2 + \ldots + n$. The theorem confirms the well-known closed-form formula $\frac{n(n+1)}{2}$ for triangle numbers in the context of real arithmetic.

This theorem bridges the gap between natural number arithmetic and real number arithmetic for triangle numbers, showing that the division by 2 is exact when working with reals. This is useful when embedding discrete structures like triangle numbers into continuous mathematical frameworks.

### Dependencies
- The theorem relies on the definition of `triangle` numbers
- Uses basic arithmetic properties and real number conversion theorems

### Porting notes
When porting this theorem:
- Ensure that the host system has a clear distinction between natural numbers and reals
- The proof relies on the fact that for any natural number n, either n or n+1 is even, which may need to be explicitly stated in some systems
- The exact division property (DIV_MULT) may require different handling in systems with different representations of division

---

## TRIANGLE_FINITE_SUM

### Name of formal statement
TRIANGLE_FINITE_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_FINITE_SUM = prove
 (`!n. sum(1..n) (\k. &1 / &(triangle k)) = &2 - &2 / (&n + &1)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_TRIANGLE; GSYM REAL_OF_NUM_SUC] THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $n$, the sum
$$\sum_{k=1}^n \frac{1}{\text{triangle}(k)} = 2 - \frac{2}{n + 1}$$
where $\text{triangle}(k)$ represents the $k$-th triangular number.

### Informal proof
This theorem is proved by induction on $n$.

**Base case**: When $n = 0$:
- The sum is empty since the range $1..0$ contains no elements.
- The right-hand side evaluates to $2 - \frac{2}{0 + 1} = 2 - 2 = 0$.
- These are equal, satisfying the base case.

**Inductive step**: Assuming the formula holds for $n$, we prove it for $n+1$:
- We use `SUM_CLAUSES_NUMSEG` to separate the sum as:
  $$\sum_{k=1}^{n+1} \frac{1}{\text{triangle}(k)} = \sum_{k=1}^{n} \frac{1}{\text{triangle}(k)} + \frac{1}{\text{triangle}(n+1)}$$
- By the induction hypothesis, the first term equals $2 - \frac{2}{n + 1}$
- We use `REAL_TRIANGLE` to substitute the value of $\text{triangle}(n+1) = \frac{(n+1)(n+2)}{2}$
- After substituting and algebraic manipulation with `REAL_FIELD`:
  $$\left(2 - \frac{2}{n + 1}\right) + \frac{1}{\frac{(n+1)(n+2)}{2}} = 2 - \frac{2}{(n+1) + 1}$$
  $$2 - \frac{2}{n + 1} + \frac{2}{(n+1)(n+2)} = 2 - \frac{2}{n + 2}$$
- This simplifies to the required formula, completing the proof.

### Mathematical insight
This theorem provides a closed-form expression for the sum of reciprocals of triangular numbers, which is a special case of a harmonic series with triangular denominators. The result shows that this sum approaches 2 as $n$ approaches infinity.

The proof technique demonstrates how induction combined with algebraic manipulation can be used to establish closed-form expressions for finite sums.

This result is related to telescoping series techniques, as the difference between consecutive terms of the form $\frac{2}{n+1}$ leads to the elegant closed-form solution.

### Dependencies
- Theorems:
  - `sum`: Recursive definition of sum
  - `SUM_CLAUSES_NUMSEG`: Properties of sums over numeric ranges
  - `REAL_TRIANGLE`: Definition of triangular numbers
  - `REAL_OF_NUM_SUC`: Conversion between successor function and numeric addition
  - `ARITH_RULE`, `ARITH_EQ`: Arithmetic simplification rules
  - `REAL_RAT_REDUCE_CONV`, `REAL_FIELD`: Conversion tactics for real number algebraic manipulation

### Porting notes
When porting this theorem:
- Ensure the target system has a definition for triangular numbers that matches HOL Light's `triangle k = (k * (k + 1)) DIV 2`
- The proof relies heavily on algebraic manipulation of real numbers and fractions, so the target system should have good automation for such simplifications
- In systems with stronger typing, explicit type casts between natural numbers and reals (represented by `&` in HOL Light) may need to be handled differently

---

## TRIANGLE_CONVERGES

### Name of formal statement
TRIANGLE_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_CONVERGES = prove
 (`!e. &0 < e
       ==> ?N. !n. n >= N
                   ==> abs(sum(1..n) (\k. &1 / &(triangle k)) - &2) < e`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N + 1` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TRIANGLE_FINITE_SUM; REAL_ARITH `abs(x - y - x) = abs y`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
For all $\epsilon > 0$, there exists a natural number $N$ such that for all $n \geq N$, 
$$\left|\sum_{k=1}^{n} \frac{1}{k(k+1)/2} - 2\right| < \epsilon$$

This theorem states that the sum of reciprocals of triangular numbers converges to 2.

### Informal proof
The proof proceeds as follows:

* First, we use the real archimedean property for inverses (`REAL_ARCH_INV`), which states that for any positive real number $\epsilon$, there exists a natural number $N$ such that $\frac{1}{N} < \epsilon$.

* We then choose $N' = 2N + 1$ as our witness for the existential quantifier.

* The proof uses `TRIANGLE_FINITE_SUM`, which establishes that $\sum_{k=1}^{n} \frac{1}{k(k+1)/2} = 2 - \frac{2}{n+1}$.

* Substituting this, the goal becomes to show $\left|-(2/(n+1))\right| < \epsilon$, which equals $\left|2/(n+1)\right| < \epsilon$.

* Since $n \geq 2N + 1$, we have $n + 1 \geq 2N + 2 > 2N$, so $1/(n+1) < 1/(2N) = (1/2) \cdot (1/N)$.

* Therefore, $|2/(n+1)| < 2 \cdot (1/2) \cdot (1/N) = 1/N < \epsilon$.

### Mathematical insight
This theorem establishes that the sum of reciprocals of triangular numbers converges to 2. Triangular numbers are defined as $T_n = \frac{n(n+1)}{2}$, representing the number of objects needed to form an equilateral triangle.

The result is part of a broader set of convergence results for reciprocals of special number sequences. The convergence to exactly 2 can be understood through a telescoping series approach, as the reciprocal of a triangular number can be expressed as $\frac{2}{n(n+1)} = \frac{2}{n} - \frac{2}{n+1}$.

### Dependencies
- Theorems:
  - `sum`: Basic properties of finite sums
  - `TRIANGLE_FINITE_SUM`: A theorem (not in the dependency list) that establishes the closed form for the sum of reciprocals of triangular numbers
- Others used in proof:
  - `REAL_ARCH_INV`: Real archimedean property for inverses
  - Various arithmetic and inequality theorems

### Porting notes
When porting this theorem:
- Ensure the definition of triangular numbers $T_n = n(n+1)/2$ is available
- The proof relies on the closed form for the sum given by `TRIANGLE_FINITE_SUM`, which should be ported first
- The approach using the archimedean property is standard and should translate well to other proof assistants

---

## TRIANGLE_CONVERGES'

### TRIANGLE_CONVERGES'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_CONVERGES' = prove
 (`(\n. sum(1..n) (\k. &1 / &(triangle k))) --> &2`,
  REWRITE_TAC[SEQ; TRIANGLE_CONVERGES]);;
```

### Informal statement
The sequence of partial sums $\left(\sum_{k=1}^{n} \frac{1}{T(k)}\right)_{n=1}^{\infty}$ converges to $2$, where $T(k)$ denotes the $k$-th triangular number.

### Informal proof
The proof simply applies the theorem `TRIANGLE_CONVERGES` and rewrites it using the standard definition of sequential convergence (`SEQ`).

The theorem `SEQ` states that a sequence $x$ converges to a limit $x_0$ if and only if for all $\varepsilon > 0$, there exists an $N$ such that for all $n \geq N$, we have $|x(n) - x_0| < \varepsilon$.

`TRIANGLE_CONVERGES` would have established the same result in a possibly different form, and this theorem reformulates it in terms of standard sequential convergence notation.

### Mathematical insight
This theorem states that the sum of reciprocals of triangular numbers $T(k) = \frac{k(k+1)}{2}$ converges to exactly 2. This is an interesting result related to the harmonic series and is part of a broader family of convergent series involving figurate numbers.

The triangular numbers grow quadratically, making their reciprocals decrease quickly enough to ensure convergence. The fact that they converge to precisely 2 is a neat mathematical result.

### Dependencies
#### Theorems
- `sum`: Defines the sum operation recursively with `sum(n,0) f = 0` and `sum(n,SUC m) f = sum(n,m) f + f(n + m)`.
- `SEQ`: Defines sequential convergence: $(x \to x_0) \iff \forall \varepsilon > 0, \exists N, \forall n \geq N, |x(n) - x_0| < \varepsilon$.
- `TRIANGLE_CONVERGES`: This would establish the convergence of the sum of reciprocals of triangular numbers to 2.

### Porting notes
When porting this theorem, one would need to:
1. First port `TRIANGLE_CONVERGES`, which likely contains the main proof substance.
2. Ensure that the definition of triangular numbers is consistent.
3. Match the notation for sequential convergence in the target system.
4. This theorem appears to be just a reformulation, so the main mathematical work is in porting its dependencies.

---

