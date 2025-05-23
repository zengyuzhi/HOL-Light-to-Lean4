# thales.ml

## Overview

Number of statements: 6

This file formalizes Thales's theorem in Euclidean geometry, which states that if a point lies on a semicircle, then the angle at that point is a right angle. The formalization builds on multivariate analysis and convex geometry concepts, and appears to use sum-of-squares techniques for the proof. It likely contains the formal statement of the theorem, supporting lemmas, and a complete proof in the HOL Light theorem prover.

## BETWEEN_THM

### BETWEEN_THM
- Exact name: `BETWEEN_THM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BETWEEN_THM = prove
 (`between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`,
  REWRITE_TAC[BETWEEN_IN_CONVEX_HULL] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2_ALT; IN_ELIM_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  AP_TERM_TAC THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For points $a$, $b$, and $x$ in $\mathbb{R}^N$, the point $x$ lies between $a$ and $b$ if and only if there exists a real number $u$ such that $0 \leq u \leq 1$ and $x = u \cdot a + (1-u) \cdot b$.

### Informal proof
The proof works by using the fact that a point lies between two other points exactly when it belongs to the convex hull of those points (theorem `BETWEEN_IN_CONVEX_HULL`).

- We start by rewriting using `BETWEEN_IN_CONVEX_HULL` to convert "between x (a,b)" to "x IN convex hull {a,b}".
- We then apply the set theory rule to rewrite "{a,b}" as "{b,a}" (since order doesn't matter in sets).
- Using `CONVEX_HULL_2_ALT`, we express the convex hull as the set of points $a + u \cdot (b - a)$ where $0 \leq u \leq 1$.
- After eliminating the set membership relation and applying some term manipulation, we use vector arithmetic to show this is equivalent to $x = u \cdot a + (1-u) \cdot b$.

### Mathematical insight
This theorem provides a parametric characterization of points lying between two given points in Euclidean space. It expresses the "betweenness" relation in terms of convex combinations, which is fundamental in projective and affine geometry. 

The parameter $u$ represents how far along the line segment from $b$ to $a$ the point $x$ lies:
- When $u = 0$, we get $x = b$
- When $u = 1$, we get $x = a$
- When $0 < u < 1$, we get points strictly between $a$ and $b$

This is essentially Thales's theorem in vector form, which is a foundational result in coordinate geometry.

### Dependencies
- Theorems:
  - `BETWEEN_IN_CONVEX_HULL`: Relates the betweenness relation to convex hull membership
  - `CONVEX_HULL_2_ALT`: Provides an alternative characterization of the convex hull of two points

### Porting notes
When porting this theorem to other systems:
- Ensure the "between" relation is properly defined first
- The convex hull concept must be available
- Different proof assistants might have different ways to handle set membership and vector arithmetic
- The proof relies on vector arithmetic simplification, which might require different tactics in other systems

Mathematical Vector notation should be preserved, including the scalar multiplication operator "%" in HOL Light which corresponds to "$\cdot$" in standard mathematical notation.

---

## length_def

### Name of formal statement
length_def

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let length_def = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;
```

### Informal statement
The length between two points $A$ and $B$ in $\mathbb{R}^2$ is defined as the norm of their difference:

$$\text{length}(A, B) = \|B - A\|$$

where $A$ and $B$ are points in $\mathbb{R}^2$ and $\|\cdot\|$ represents the Euclidean norm.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition formalizes the intuitive notion of the distance between two points in a two-dimensional Euclidean space. It uses the norm of the difference vector between the points, which corresponds to the standard Euclidean distance.

The definition is canonical in geometry and follows directly from the Pythagorean theorem. For two points $(x_1, y_1)$ and $(x_2, y_2)$ in $\mathbb{R}^2$, the length (or distance) is given by:

$$\text{length}((x_1, y_1), (x_2, y_2)) = \sqrt{(x_2 - x_1)^2 + (y_2 - y_1)^2}$$

This definition serves as a fundamental building block for many geometric constructions and theorems.

### Dependencies
None explicitly mentioned in the provided information.

### Porting notes
When porting this definition to other proof assistants:
- Ensure that the target system has an appropriate definition of the Euclidean norm for vectors.
- Check how the target system represents points in $\mathbb{R}^2$ (as vectors, pairs, etc.) and adjust the definition accordingly.
- Some systems might already have built-in distance functions that could be used instead of defining a new one.

---

## is_midpoint

### Name of formal statement
is_midpoint

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_midpoint = new_definition
 `is_midpoint (m:real^2) (a,b) <=> m = (&1 / &2) % (a + b)`;;
```

### Informal statement
A point $m \in \mathbb{R}^2$ is the midpoint of a pair of points $(a, b)$ if and only if $m = \frac{1}{2}(a + b)$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the standard notion of a midpoint in Euclidean geometry. The midpoint of two points is the point that lies exactly halfway between them. In vector terms, this is expressed as the average of the two position vectors: $\frac{1}{2}(a + b)$.

The midpoint concept is fundamental in geometry and is used in many constructions and proofs, such as:
- Finding the center of a line segment
- Constructing the midpoint of a side in triangle theorems
- As a basis for more complex geometric constructions

In HOL Light's vector representation, the formula $\frac{1}{2}(a + b)$ captures this concept precisely, where `&1 / &2` represents the scalar $\frac{1}{2}$ and `%` represents scalar multiplication.

### Dependencies
No significant dependencies were provided for this definition.

### Porting notes
When porting to other proof assistants:
- Ensure the target system has appropriate vector operations (addition and scalar multiplication)
- Check how real numbers and fractions are represented (HOL Light uses `&1` for the natural number 1 as a real)
- The vector type `real^2` represents 2D Euclidean space; ensure equivalent typing in the target system

---

## THALES

### THALES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let THALES = prove
 (`!centre radius a b c.
        length(a,centre) = radius /\
        length(b,centre) = radius /\
        length(c,centre) = radius /\
        is_midpoint centre (a,b)
        ==> orthogonal (c - a) (c - b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[length_def; BETWEEN_THM; is_midpoint] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  REWRITE_TAC[NORM_POW_2] THEN FIRST_ASSUM(MP_TAC o SYM) THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
The theorem states that given a circle with a center point `centre` and radius `radius`, and three points `a`, `b`, and `c` on the circle (i.e., all at distance `radius` from `centre`), if `centre` is the midpoint of the line segment from `a` to `b`, then the vectors `c - a` and `c - b` are orthogonal.

Mathematically, if:
- $\|a - \text{centre}\| = \text{radius}$
- $\|b - \text{centre}\| = \text{radius}$
- $\|c - \text{centre}\| = \text{radius}$
- $\text{centre} = \frac{a + b}{2}$ (centre is the midpoint of $a$ and $b$)

Then: $(c - a) \cdot (c - b) = 0$ (the vectors are orthogonal)

### Informal proof
The proof proceeds as follows:

- We first expand the definitions of `length` and `is_midpoint` in the hypotheses.
- For each equation $\|v - \text{centre}\| = \text{radius}$, we apply the operation $x \mapsto x^2$ to both sides, giving us $\|v - \text{centre}\|^2 = \text{radius}^2$.
- We introduce the abbreviation $\text{rad} = \text{radius}^2$ for convenience.
- The dot product $(c - a) \cdot (c - b)$ is expanded in terms of the components of the vectors in 2D space.
- The proof is completed using algebraic manipulation of the resulting equations, specifically using the `REAL_RING` conversion which solves the resulting algebraic problem.

The key insight is that when the center of the circle is the midpoint of chord $ab$, then from any point $c$ on the circle, the vectors to the endpoints of the chord ($c-a$ and $c-b$) are perpendicular.

### Mathematical insight
This theorem is a formalization of Thales' theorem, a fundamental result in Euclidean geometry. The theorem states that if a triangle is inscribed in a circle with one side being a diameter of the circle, then the triangle is a right triangle.

In this formalization, we have a slightly different perspective: if points $a$ and $b$ are on opposite ends of a diameter (which is equivalent to the center being their midpoint), then from any other point $c$ on the circle, the angle $acb$ is a right angle. This is equivalent to saying that vectors $c-a$ and $c-b$ are orthogonal.

Thales' theorem is one of the earliest recorded mathematical proofs and forms a cornerstone of circle geometry. It relates the concept of perpendicularity to points on a circle, establishing a fundamental property that has numerous applications in geometry and beyond.

### Dependencies
- **Definitions**:
  - `length_def`: Definition of the Euclidean distance between two points
  - `is_midpoint`: Definition specifying when a point is the midpoint of two other points
  - `orthogonal`: Definition of orthogonality between vectors (zero dot product)
  - `dot`: Definition of the dot product of vectors
  
- **Theorems**:
  - `BETWEEN_THM`: Theorem about points lying between other points
  - `NORM_POW_2`: Theorem relating squared norm to dot product
  - Various vector component and arithmetic theorems

### Porting notes
When porting this theorem:
1. Ensure that the vector operations (subtraction, dot product) are correctly defined in the target system
2. The 2D nature of the vectors is used explicitly in the proof (with `DIMINDEX_2`), so ensure the ported version handles the dimensionality correctly
3. The final step uses `REAL_RING` for algebraic simplification - an equivalent automated algebraic solver may be needed in the target system

---

## MIDPOINT

### Name of formal statement
MIDPOINT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MIDPOINT = prove
 (`!m a b. between m (a,b) /\ length(a,m) = length(b,m)
           ==> is_midpoint m (a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[length_def; BETWEEN_THM; is_midpoint; NORM_EQ] THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_SOS);;
```

### Informal statement
For any points $a$, $b$, and $m$ in a Euclidean space, if $m$ is between $a$ and $b$ and the distance from $a$ to $m$ equals the distance from $m$ to $b$, then $m$ is the midpoint of $a$ and $b$.

Formally:
$$\forall m, a, b. \text{between}(m, (a, b)) \land \text{length}(a, m) = \text{length}(m, b) \Rightarrow \text{is\_midpoint}(m, (a, b))$$

### Informal proof
The proof shows that a point equidistant from two endpoints and lying on the line segment between them is indeed the midpoint of those points.

- Begin by expanding the definitions of `length`, `between`, `is_midpoint`, and `NORM_EQ` to express the problem in terms of coordinates and vector operations.
- Simplify using dot product properties and vector component calculations for 2D Euclidean space.
- The condition `between m (a,b)` means that $m$ lies on the line segment from $a$ to $b$.
- The condition `length(a,m) = length(b,m)` means that the distances from $m$ to both $a$ and $b$ are equal.
- Apply substitutions from the assumptions to establish the required vector equality.
- The final step uses the Sum-of-Squares (SOS) real arithmetic decision procedure (`REAL_SOS`) to complete the proof, showing that the only point between $a$ and $b$ that is equidistant from both must be their midpoint.

### Mathematical insight
This theorem confirms a fundamental geometric intuition: if a point lies on a line segment connecting two points and is equidistant from both endpoints, then it must be exactly halfway between them (i.e., their midpoint). 

The proof relies on real algebraic geometry, specifically the Sum-of-Squares (SOS) technique, to solve the underlying algebraic constraints. This approach is necessary because the theorem connects the betweenness relation with the metric notion of equidistance, requiring real algebraic manipulation to establish the equality.

This result is important in Euclidean geometry as it establishes an alternative characterization of midpoints that can be useful in various geometric proofs.

### Dependencies
- **Definitions**:
  - `length_def`: The definition of length (distance) between points
  - `BETWEEN_THM`: The theorem defining when a point is between two others
  - `is_midpoint`: The definition of a midpoint
  - `NORM_EQ`: Condition for equality of norms
  - `dot`: Definition of the dot product
  - `orthogonal`: Definition of orthogonality
  - `VECTOR_SUB_COMPONENT`, `VECTOR_ADD_COMPONENT`, `VECTOR_MUL_COMPONENT`: Vector operations by components

- **Theorems**:
  - `SUM_2`: Theorem about summation with two terms
  - `DIMINDEX_2`: The dimension index for 2D space
  - `CART_EQ`: Equality of Cartesian vectors
  - `FORALL_2`: Universal quantification over pairs

- **Tools**:
  - `REAL_SOS`: Sum-of-Squares decision procedure for real arithmetic

### Porting notes
When porting this theorem:
1. You'll need a Sum-of-Squares (SOS) decision procedure for real arithmetic or an equivalent real algebraic solver.
2. The vector operations and Euclidean space definitions need to be compatible with your target system.
3. The proof leverages 2D vector properties; ensure your vector library properly handles component-wise operations.
4. If your system doesn't have a direct equivalent to `REAL_SOS`, you may need to expand the algebraic reasoning into more explicit steps.

---

## THALES

### Name of formal statement
THALES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THALES = prove
 (`!centre radius a b c:real^2.
        length(a,centre) = radius /\
        length(b,centre) = radius /\
        length(c,centre) = radius /\
        between centre (a,b)
        ==> orthogonal (c - a) (c - b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `is_midpoint centre (a,b)` MP_TAC THENL
   [MATCH_MP_TAC MIDPOINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `between (centre:real^2) (a,b)` (K ALL_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  REWRITE_TAC[length_def; is_midpoint; orthogonal; NORM_POW_2] THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any points $a$, $b$, $c$ in $\mathbb{R}^2$ that lie on a circle with center $\text{centre}$ and radius $\text{radius}$, if the center $\text{centre}$ lies between points $a$ and $b$ (i.e., $a$ and $b$ are on opposite sides of a diameter), then the vectors $c - a$ and $c - b$ are orthogonal.

### Informal proof
The proof proceeds as follows:

* First, we show that if $\text{centre}$ lies between $a$ and $b$, then $\text{centre}$ is the midpoint of the segment $[a,b]$. This is done by applying the `MIDPOINT` theorem and using our assumptions.

* We then discard the assumption that $\text{centre}$ lies between $a$ and $b$ since we've established the midpoint relationship.

* For each of the distance conditions (that $a$, $b$, and $c$ are at distance $\text{radius}$ from $\text{centre}$), we rewrite them in terms of squared distances.

* We introduce the abbreviation $\text{rad} = \text{radius}^2$ to simplify the expressions.

* The orthogonality of vectors $c - a$ and $c - b$ is equivalent to their dot product being zero. Using the dot product definition in $\mathbb{R}^2$ and properties of vector operations, we express this condition in terms of vector components.

* The proof is completed using real arithmetic, showing that the dot product of the vectors $c - a$ and $c - b$ is indeed zero, establishing their orthogonality.

### Mathematical insight
This theorem is a formal statement of Thales' theorem in Euclidean geometry, which states that if three points lie on a circle such that one of the line segments is a diameter of the circle, then the triangle formed by these three points is a right triangle. 

In this formalization, the condition that $\text{centre}$ lies between $a$ and $b$ means that the line segment from $a$ to $b$ passes through the center, making it a diameter. The conclusion that vectors $c - a$ and $c - b$ are orthogonal is equivalent to saying that the angle at vertex $c$ in the triangle $abc$ is a right angle.

This theorem provides a fundamental relationship in circle geometry and has applications in various areas of mathematics and computer graphics.

### Dependencies
#### Theorems
- `MIDPOINT`: Shows that if a point lies between two other points, it is their midpoint

#### Definitions
- `between`: Defines when a point lies between two other points
- `orthogonal`: Defines when two vectors are perpendicular
- `length`: Computes the Euclidean distance between two points
- `is_midpoint`: Defines when a point is the midpoint of two others

### Porting notes
When porting this theorem:
- Ensure that the library has appropriate definitions for geometric concepts like "between", "orthogonal", and "is_midpoint"
- The proof relies on expressing geometric conditions algebraically and then using real arithmetic
- Different proof assistants may have different ways of handling the vector algebra and real arithmetic
- Special attention should be paid to the representation of points in $\mathbb{R}^2$ and vector operations

---

