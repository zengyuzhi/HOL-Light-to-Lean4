# pythagoras.ml

## Overview

Number of statements: 2

The `pythagoras.ml` file contains a formal proof of the Pythagorean theorem in HOL Light's multivariate analysis library. It builds on vector operations defined in the vectors.ml file to establish the relationship between the sides of a right-angled triangle. While the theorem is implicitly related to vector norm definitions, this file provides an explicit formalization of the classic result, demonstrating how it follows from the fundamental properties of vectors and inner products.

## PYTHAGORAS

### PYTHAGORAS

### Type of formal statement
theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any three points $A$, $B$, and $C$ in $\mathbb{R}^2$, if the vectors $A - B$ and $C - B$ are orthogonal, then:

$$\|C - A\|^2 = \|B - A\|^2 + \|C - B\|^2$$

This is a vector-based formulation of the Pythagorean theorem, where $B$ forms a right angle.

### Informal proof
The proof uses the relationship between the squared norm of a vector and its dot product with itself.

First, we rewrite all squared norms using the theorem `NORM_POW_2`, which states that $\|v\|^2 = v \cdot v$ for any vector $v$. We also expand the definition of orthogonality, which means $(A - B) \cdot (C - B) = 0$.

Then, we expand the dot products using the properties of dot products with respect to vector subtraction (`DOT_LSUB`, `DOT_RSUB`) and symmetry of dot products (`DOT_SYM`).

Finally, we apply algebraic simplification using `REAL_RING` to complete the proof. The algebraic manipulation essentially shows:

$$(C - A) \cdot (C - A) = (B - A) \cdot (B - A) + (C - B) \cdot (C - B)$$

given that $(A - B) \cdot (C - B) = 0$.

### Mathematical insight
This theorem is the vector form of the Pythagorean theorem. When points $A$, $B$, and $C$ form a right triangle with the right angle at $B$, the theorem states that the square of the length of the hypotenuse ($\|C - A\|^2$) equals the sum of the squares of the other two sides ($\|B - A\|^2 + \|C - B\|^2$).

The vector approach makes the proof remarkably concise and generalizable. While this theorem is stated for $\mathbb{R}^2$, the comment in the HOL Light code notes that the proof works equally well for any dimension, showing the power of the vector formulation.

The orthogonality condition $(A - B) \cdot (C - B) = 0$ is precisely what defines a right angle in vector terms, making this a direct translation of Pythagoras's theorem into the language of vectors.

### Dependencies
- **Theorems**:
  - `NORM_POW_2`: For any vector $x$, $\|x\|^2 = x \cdot x$
  - `DOT_LSUB`, `DOT_RSUB`: Properties of dot products with respect to vector subtraction
  - `DOT_SYM`: The dot product is symmetric ($x \cdot y = y \cdot x$)
  - `DOT_POS_LE`: (indirectly used) The dot product of a vector with itself is non-negative

- **Definitions**:
  - `orthogonal`: Two vectors $x$ and $y$ are orthogonal if and only if $x \cdot y = 0$

### Porting notes
When porting this theorem to another system:
1. Ensure that the vector operations (norm, dot product) and their basic properties are defined
2. The proof relies on algebraic manipulation of real expressions, so the target system needs an equivalent of `REAL_RING` for automated algebraic simplification
3. The generalization to n-dimensional spaces should be straightforward and would only require changing the type from `real^2` to `real^N`

---

## PYTHAGORAS

### PYTHAGORAS
- `PYTHAGORAS`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; dot; SUM_2; DIMINDEX_2;
           VECTOR_SUB_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any three points $A$, $B$, and $C$ in $\mathbb{R}^2$, if the vectors $A - B$ and $C - B$ are orthogonal, then:

$$\|C - A\|^2 = \|B - A\|^2 + \|C - B\|^2$$

where $\|\cdot\|$ denotes the Euclidean norm.

### Informal proof
The proof proceeds by transforming the statement into an algebraic identity using vector dot products:

* First, we use the fact that the square of the norm equals the dot product of a vector with itself: $\|v\|^2 = v \cdot v$ (from `NORM_POW_2`).

* We then express the condition of orthogonality using the dot product: vectors are orthogonal when their dot product is zero (from the definition of `orthogonal`).

* For vectors in $\mathbb{R}^2$, the dot product is calculated as $x \cdot y = \sum_{i=1}^{2} x_i y_i = x_1 y_1 + x_2 y_2$.

* Using component-wise properties of vector subtraction (from `VECTOR_SUB_COMPONENT`), we expand the expressions $(C-A) \cdot (C-A)$, $(B-A) \cdot (B-A)$, and $(C-B) \cdot (C-B)$.

* The result then follows from algebraic manipulation of these expanded dot products, utilizing the orthogonality condition $(A-B) \cdot (C-B) = 0$.

* The final algebraic verification is handled by the `REAL_RING` converter, which completes the proof by establishing the identity through standard ring properties of real numbers.

### Mathematical insight
This theorem is a specialized form of the Pythagorean theorem for vectors in $\mathbb{R}^2$. The theorem states that if we have a right angle at B (i.e., vectors $A-B$ and $C-B$ are orthogonal), then the square of the distance from $A$ to $C$ equals the sum of squares of the distances from $A$ to $B$ and from $B$ to $C$.

This result generalizes the familiar Pythagorean theorem from plane geometry to vector spaces. It's particularly useful in computational geometry and applications involving distance calculations in the plane.

### Dependencies
- **Theorems**:
  - `VECTOR_SUB_COMPONENT`: Component-wise property of vector subtraction: $(x - y)_i = x_i - y_i$
  - `NORM_POW_2`: Square of the norm equals the dot product: $\|x\|^2 = x \cdot x$
- **Definitions**:
  - `dot`: Dot product of vectors in $\mathbb{R}^N$: $x \cdot y = \sum_{i=1}^{\text{dimindex}(N)} x_i y_i$
  - `orthogonal`: Two vectors are orthogonal if their dot product is zero: $\text{orthogonal}(x, y) \iff x \cdot y = 0$

### Porting notes
When porting this theorem:
- Ensure that the vector space implementation supports dot products and norms
- The proof relies on algebraic manipulations that might be handled differently in other systems
- The `REAL_RING` tactic in HOL Light has counterparts in other systems (e.g., `ring` in Coq, `ring` in Lean) that can automate the algebraic part of the proof

---

