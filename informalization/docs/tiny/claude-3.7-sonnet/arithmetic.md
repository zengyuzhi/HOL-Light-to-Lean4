# arithmetic.ml

## Overview

Number of statements: 2

The `arithmetic.ml` file provides formalization of arithmetic series in HOL Light. It defines and proves theorems about the sum of arithmetic sequences, offering the mathematical foundation and key properties of arithmetic progressions. This file stands as a self-contained module without external dependencies, serving as a basic building block for numerical reasoning in the HOL Light theorem proving system.

## ARITHMETIC_PROGRESSION_LEMMA

### ARITHMETIC_PROGRESSION_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARITHMETIC_PROGRESSION_LEMMA = prove
 (`!n. nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the sum of an arithmetic progression from index $0$ to $n$ with first term $a$ and common difference $d$ is given by:

$$\sum_{i=0}^{n} (a + d \cdot i) = \frac{(n + 1)(2a + n \cdot d)}{2}$$

where the right side uses integer division (DIV 2).

### Informal proof
The proof proceeds by induction on $n$.

- Base case ($n = 0$): 
  The sum reduces to just the first term $a$, and the right-hand side becomes $(1 \cdot (2a + 0 \cdot d)) \div 2 = 2a \div 2 = a$.

- Inductive case: 
  Assuming the formula holds for some $n$, we prove it for $n+1$.
  * The sum for $n+1$ is the sum for $n$ plus the additional term $a + d(n+1)$
  * Using the induction hypothesis and simplifying algebraically:
    $$\sum_{i=0}^{n+1} (a + di) = \frac{(n+1)(2a + nd)}{2} + (a + d(n+1))$$
    $$= \frac{(n+1)(2a + nd) + 2a + 2d(n+1)}{2}$$
    $$= \frac{(n+1)(2a + nd) + 2a + 2d(n+1)}{2}$$
    $$= \frac{(n+2)(2a + (n+1)d)}{2}$$

The last step is handled by `ARITH_TAC`, which performs the necessary arithmetic simplifications to show that the expressions are equivalent.

### Mathematical insight
This theorem provides the well-known formula for the sum of an arithmetic progression. It's a fundamental result used extensively in discrete mathematics, number theory, and combinatorial problems.

The formula elegantly captures that the sum equals the average of the first and last terms multiplied by the number of terms. This can be visualized by pairing terms from opposite ends of the sequence, where each pair sums to the same value.

Note that the formula uses integer division (DIV 2) rather than fractions, which ensures the result is always an integer when $a$ and $d$ are integers.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`: Defines how to compute the sum over a numeric segment recursively
- `INDUCT_TAC`: Induction tactic for natural numbers
- `ASM_REWRITE_TAC`: Rewriting tactic using assumptions
- `ARITH_TAC`: Automated arithmetic reasoning tactic

### Porting notes
When porting to other proof assistants:
- Ensure that the notation for summation over ranges is properly handled
- The division operation might need special attention in type-theoretic systems to ensure it represents integer division
- Some systems might require explicit treatment of cases where $n = 0$ or separate handling of the arithmetic simplifications that HOL Light handles with `ARITH_TAC`

---

## ARITHMETIC_PROGRESSION

### Name of formal statement
ARITHMETIC_PROGRESSION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARITHMETIC_PROGRESSION = prove
 (`!n. 1 <= n
       ==> nsum(0..n-1) (\i. a + d * i) = (n * (2 * a + (n - 1) * d)) DIV 2`,
  INDUCT_TAC THEN REWRITE_TAC[ARITHMETIC_PROGRESSION_LEMMA; SUC_SUB1] THEN
  ARITH_TAC);;
```

### Informal statement
For any natural number $n$ such that $1 \leq n$, the sum of an arithmetic progression from $0$ to $n-1$ with first term $a$ and common difference $d$ is equal to $\frac{n(2a + (n-1)d)}{2}$.

Formally, for any $n \in \mathbb{N}$ with $1 \leq n$:
$$\sum_{i=0}^{n-1} (a + d \cdot i) = \frac{n(2a + (n-1)d)}{2}$$

Where $\frac{x}{2}$ is represented as $x \text{ DIV } 2$ in the formal statement.

### Informal proof
The proof uses induction on the natural number $n$.

* **Base case**: For $n = 0$, the hypothesis $1 \leq n$ is false, so the statement holds vacuously.

* **Inductive case**: Assume the statement holds for some $n$. We need to prove it for $n+1$.

  The proof applies the following:
  - `ARITHMETIC_PROGRESSION_LEMMA`, which states that the sum of the arithmetic progression from $0$ to $n$ is $\frac{(n+1)(2a + nd)}{2}$.
  - `SUC_SUB1`, which states that $\text{SUC}(m) - 1 = m$ for any natural number $m$.
  
  After applying these lemmas, the proof is completed with `ARITH_TAC`, which handles the remaining arithmetic reasoning.

### Mathematical insight
This theorem provides the well-known formula for the sum of an arithmetic progression. It is particularly formulated to sum from $0$ to $n-1$, which is often a useful form in computer science and discrete mathematics applications.

The formula can be derived from the general arithmetic progression sum formula:
$$S_n = \frac{n}{2}(a_1 + a_n)$$

where $a_1$ is the first term and $a_n$ is the last term. In this case, $a_1 = a$ and $a_n = a + d(n-1)$, which gives the formula in the theorem.

This result is fundamental in discrete mathematics and has numerous applications in algorithm analysis, numerical methods, and combinatorics.

### Dependencies
- `ARITHMETIC_PROGRESSION_LEMMA` - The lemma that gives the sum of an arithmetic progression from $0$ to $n$.
- `SUC_SUB1` - The property that $\text{SUC}(m) - 1 = m$ for natural numbers.
- Various arithmetic tactics and definitions used by `ARITH_TAC`.

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that DIV is properly defined as integer division.
- The induction tactic used in HOL Light may need to be adapted to the target system's induction mechanism.
- The `ARITH_TAC` automated reasoning might need to be replaced with more explicit arithmetic reasoning in systems with less powerful automation.

---

