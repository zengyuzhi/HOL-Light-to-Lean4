# ptolemy.ml

## Overview

Number of statements: 3

This file formalizes Ptolemy's theorem from Euclidean geometry, which relates the lengths of diagonals and sides of cyclic quadrilaterals. It builds on transcendental functions from the Multivariate library, likely providing formal definitions, key lemmas, and a complete proof of the theorem. The file appears to be a standalone formalization of this classic result rather than serving as a foundation for other developments.

## DOT_VECTOR

### Name of formal statement
DOT_VECTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DOT_VECTOR = prove
 (`(vector [x1;y1] :real^2) dot (vector [x2;y2]) = x1 * x2 + y1 * y2`,
  REWRITE_TAC[dot; DIMINDEX_2; SUM_2; VECTOR_2]);;
```

### Informal statement
The dot product of two 2-dimensional real vectors $\vec{v}_1 = (x_1, y_1)$ and $\vec{v}_2 = (x_2, y_2)$ is equal to the sum of the products of their corresponding components:

$$\vec{v}_1 \cdot \vec{v}_2 = x_1 x_2 + y_1 y_2$$

### Informal proof
The proof uses the definition of the dot product and specific properties of 2-dimensional vectors:

1. Apply the definition of dot product (`dot`), which is the sum of products of corresponding components.

2. Use `DIMINDEX_2` to establish that the dimension index for $\mathbb{R}^2$ is 2.

3. Apply `SUM_2` to expand the summation in the dot product formula for 2-dimensional vectors.

4. Use `VECTOR_2` to access the components of the 2-dimensional vectors.

These steps together simplify the general dot product formula to the specific case for 2-dimensional vectors, resulting in $x_1 x_2 + y_1 y_2$.

### Mathematical insight
This theorem provides the explicit formula for the dot product in the specific case of 2-dimensional vectors. While the general dot product definition works for vectors of any dimension as the sum of products of corresponding components, this theorem gives the simplified, concrete form for the common case of vectors in $\mathbb{R}^2$.

The explicit formula is particularly useful in plane geometry and many physics applications where 2D vectors are common. It serves as a building block for calculations involving angles between vectors, projections, and other geometric properties in the plane.

### Dependencies
- Definitions:
  - `dot`: The general definition of the dot product
  - `DIMINDEX_2`: Definition that the dimension of $\mathbb{R}^2$ is 2
  - `SUM_2`: The expansion of a sum over two elements 
  - `VECTOR_2`: The representation of 2-dimensional vectors

### Porting notes
When porting this theorem:
1. Ensure that the target system has a compatible representation of vectors and dot products
2. Check if the target system handles vector indexing similarly to HOL Light's `vector` function
3. If the target system has built-in vector operations, you might be able to use those directly instead of the explicit component-wise calculation

---

## DIST_SEGMENT_LEMMA

### Name of formal statement
DIST_SEGMENT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIST_SEGMENT_LEMMA = prove
 (`!a1 a2. &0 <= a1 /\ a1 <= a2 /\ a2 <= &2 * pi /\ &0 <= radius
           ==> dist(centre + radius % vector [cos(a1);sin(a1)] :real^2,
                    centre + radius % vector [cos(a2);sin(a2)]) =
               &2 * radius *  sin((a2 - a1) / &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist; vector_norm] THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIN_POS_PI_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(c + r % x) - (c + r % y) = r % (x - y)`] THEN
  REWRITE_TAC[VECTOR_ARITH `(r % x) dot (r % x) = (r pow 2) * (x dot x)`] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_VECTOR] THEN
  SUBST1_TAC(REAL_ARITH `a1 = &2 * a1 / &2`) THEN
  SUBST1_TAC(REAL_ARITH `a2 = &2 * a2 / &2`) THEN
  REWRITE_TAC[REAL_ARITH `(&2 * x - &2 * y) / &2 = x - y`] THEN
  REWRITE_TAC[SIN_SUB; SIN_DOUBLE; COS_DOUBLE] THEN
  MP_TAC(SPEC `a1 / &2` SIN_CIRCLE) THEN MP_TAC(SPEC `a2 / &2` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any real numbers $a_1, a_2$ and $\text{radius}$ such that $0 \leq a_1 \leq a_2 \leq 2\pi$ and $0 \leq \text{radius}$, the distance between two points on a circle with center $\text{centre}$ and radius $\text{radius}$ at angles $a_1$ and $a_2$ is given by:

$$\text{dist}(\text{centre} + \text{radius} \cdot \text{vector}[\cos(a_1), \sin(a_1)], \text{centre} + \text{radius} \cdot \text{vector}[\cos(a_2), \sin(a_2)]) = 2 \cdot \text{radius} \cdot \sin\left(\frac{a_2 - a_1}{2}\right)$$

where $\text{vector}[\cos(a), \sin(a)]$ represents a point on the unit circle at angle $a$.

### Informal proof
We need to prove the formula for the distance between two points on a circle with center $\text{centre}$ and radius $\text{radius}$.

- First, we expand the definition of distance as the Euclidean norm of the difference between the points.
- We verify that the right side of the equation is non-negative by showing:
  * $\text{radius} \geq 0$ (given in the hypothesis)
  * $\sin\left(\frac{a_2 - a_1}{2}\right) \geq 0$, which follows from $0 \leq a_2 - a_1 \leq 2\pi$ and using the `SIN_POS_PI_LE` theorem.

- For the main calculation, we express the difference between the points as:
  $$(\text{centre} + \text{radius} \cdot \vec{v}_1) - (\text{centre} + \text{radius} \cdot \vec{v}_2) = \text{radius} \cdot (\vec{v}_1 - \vec{v}_2)$$
  where $\vec{v}_1 = \text{vector}[\cos(a_1), \sin(a_1)]$ and $\vec{v}_2 = \text{vector}[\cos(a_2), \sin(a_2)]$

- Using properties of the dot product:
  $$\|r \cdot \vec{v}\|^2 = r^2 \cdot \|\vec{v}\|^2$$

- We compute the dot product components, substituting $a_1 = 2 \cdot \frac{a_1}{2}$ and $a_2 = 2 \cdot \frac{a_2}{2}$

- We apply the sine and cosine double-angle formulas (`SIN_DOUBLE` and `COS_DOUBLE`) and the sine of difference formula (`SIN_SUB`)

- Finally, we use the Pythagorean identity $\sin^2(x) + \cos^2(x) = 1$ (`SIN_CIRCLE`) for $x = \frac{a_1}{2}$ and $x = \frac{a_2}{2}$

- The proof is completed with algebraic manipulations to arrive at the desired formula: $2 \cdot \text{radius} \cdot \sin\left(\frac{a_2 - a_1}{2}\right)$

### Mathematical insight
This lemma provides a direct formula for the chord length between two points on a circle based on their angular positions. This is a well-known result in Euclidean geometry often referred to as the "chord length formula."

The key insight is that the distance between two points on a circle can be expressed elegantly using the sine function of half the angular difference. This reflects the geometric property that the length of a chord in a circle equals twice the radius times the sine of half the central angle.

This lemma is particularly useful for calculations involving circular arcs and segments, and finds applications in computational geometry, computer graphics, and many physical problems involving circular motion or structures.

### Dependencies
#### Theorems
- `SIN_CIRCLE`: $\forall x. \sin^2(x) + \cos^2(x) = 1$
- `SIN_DOUBLE`: $\forall x. \sin(2x) = 2\sin(x)\cos(x)$
- `COS_DOUBLE`: $\forall x. \cos(2x) = \cos^2(x) - \sin^2(x)$
- `SIN_POS_PI_LE`: $\forall x. 0 \leq x \land x \leq \pi \Rightarrow 0 \leq \sin(x)$
- `SIN_SUB`: $\forall w,z. \sin(w-z) = \sin(w)\cos(z) - \cos(w)\sin(z)$

#### Definitions
- `sin`: The sine function
- `cos`: The cosine function
- `pi`: The constant $\pi$

### Porting notes
When implementing this in other proof assistants:
- Ensure the trigonometric identities (especially half-angle formulas) are available or proven first
- Pay attention to the vector representation - some systems might use different conventions for vectors
- Note that this proof relies on real algebraic simplifications that might need different tactics in other systems
- The core of this proof is algebraic manipulation after applying trigonometric identities, so systems with good algebraic simplification capabilities will make this proof easier

---

## PTOLEMY

### Name of formal statement
PTOLEMY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PTOLEMY = prove
 (`!A B C D:real^2 a b c d centre radius.
        A = centre + radius % vector [cos(a);sin(a)] /\
        B = centre + radius % vector [cos(b);sin(b)] /\
        C = centre + radius % vector [cos(c);sin(c)] /\
        D = centre + radius % vector [cos(d);sin(d)] /\
        &0 <= radius /\
        &0 <= a /\ a <= b /\ b <= c /\ c <= d /\ d <= &2 * pi
        ==> dist(A,C) * dist(B,D) =
            dist(A,B) * dist(C,D) + dist(A,D) * dist(B,C)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl))) THEN
  REPEAT
   (W(fun (asl,w) ->
     let t = find_term
      (fun t -> can (PART_MATCH (lhs o rand) DIST_SEGMENT_LEMMA) t) w in
     MP_TAC (PART_MATCH (lhs o rand) DIST_SEGMENT_LEMMA t) THEN
     ANTS_TAC THENL
      [ASM_REAL_ARITH_TAC;
       DISCH_THEN SUBST1_TAC])) THEN
  REWRITE_TAC[REAL_ARITH `(x - y) / &2 = x / &2 - y / &2`] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`a / &2`; `b / &2`; `c / &2`; `d / &2`] THEN
  REWRITE_TAC[SIN_SUB; SIN_ADD; COS_ADD; SIN_PI; COS_PI] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any points $A, B, C, D \in \mathbb{R}^2$ that lie on a circle with center `centre` and radius `radius` where:
- $A = \text{centre} + \text{radius} \cdot (\cos(a), \sin(a))$
- $B = \text{centre} + \text{radius} \cdot (\cos(b), \sin(b))$
- $C = \text{centre} + \text{radius} \cdot (\cos(c), \sin(c))$
- $D = \text{centre} + \text{radius} \cdot (\cos(d), \sin(d))$

And given that:
- $\text{radius} \geq 0$
- $0 \leq a \leq b \leq c \leq d \leq 2\pi$

Then Ptolemy's theorem holds:
$\text{dist}(A,C) \cdot \text{dist}(B,D) = \text{dist}(A,B) \cdot \text{dist}(C,D) + \text{dist}(A,D) \cdot \text{dist}(B,C)$

where $\text{dist}$ is the Euclidean distance between points.

### Informal proof
To prove Ptolemy's theorem, we:

1. Apply the assumptions about the points $A, B, C, D$ being on the circle.

2. For each distance term $\text{dist}(P,Q)$, apply the `DIST_SEGMENT_LEMMA` to express it in terms of the sine of half the difference of angles:
   - $\text{dist}(A,C) = 2 \cdot \text{radius} \cdot \sin\left(\frac{c-a}{2}\right)$
   - $\text{dist}(B,D) = 2 \cdot \text{radius} \cdot \sin\left(\frac{d-b}{2}\right)$
   - $\text{dist}(A,B) = 2 \cdot \text{radius} \cdot \sin\left(\frac{b-a}{2}\right)$
   - $\text{dist}(C,D) = 2 \cdot \text{radius} \cdot \sin\left(\frac{d-c}{2}\right)$
   - $\text{dist}(A,D) = 2 \cdot \text{radius} \cdot \sin\left(\frac{d-a}{2}\right)$
   - $\text{dist}(B,C) = 2 \cdot \text{radius} \cdot \sin\left(\frac{c-b}{2}\right)$

3. Simplify the expression $\text{dist}(A,C) \cdot \text{dist}(B,D) = \text{dist}(A,B) \cdot \text{dist}(C,D) + \text{dist}(A,D) \cdot \text{dist}(B,C)$:
   - Left side: $4 \cdot \text{radius}^2 \cdot \sin\left(\frac{c-a}{2}\right) \cdot \sin\left(\frac{d-b}{2}\right)$
   - Right side: $4 \cdot \text{radius}^2 \cdot \left[\sin\left(\frac{b-a}{2}\right) \cdot \sin\left(\frac{d-c}{2}\right) + \sin\left(\frac{d-a}{2}\right) \cdot \sin\left(\frac{c-b}{2}\right)\right]$

4. Apply trigonometric identities:
   - Use the identity $\sin^2(x) + \cos^2(x) = 1$ for each angle term.
   - Apply the addition formulas for sine: $\sin(x+y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
   - Apply the subtraction formulas for sine: $\sin(x-y) = \sin(x)\cos(y) - \cos(x)\sin(y)$

5. By algebraic manipulation and these trigonometric identities, the equation reduces to an identity that can be verified with real arithmetic.

### Mathematical insight
Ptolemy's theorem is a fundamental result in Euclidean geometry that relates the products of the lengths of the diagonals and the sides of a cyclic quadrilateral (a quadrilateral whose vertices all lie on a circle).

This theorem has numerous applications in geometry and trigonometry, including:
- It provides a necessary and sufficient condition for a quadrilateral to be cyclic
- It can be used to derive many trigonometric identities
- It generalizes both the law of sines and the Pythagorean theorem

The proof presented here uses a coordinate-based approach, representing points on the circle parametrically and reducing the geometric statement to algebraic manipulations of trigonometric expressions. This approach highlights the deep connection between Euclidean geometry and trigonometry.

### Dependencies
#### Theorems
- `SIN_CIRCLE`: Trigonometric identity $\sin^2(x) + \cos^2(x) = 1$
- `SIN_ADD`: Addition formula for sine $\sin(x+y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
- `SIN_SUB`: Subtraction formula for sine $\sin(x-y) = \sin(x)\cos(y) - \cos(x)\sin(y)$
- `COS_ADD`: Addition formula for cosine $\cos(x+y) = \cos(x)\cos(y) - \sin(x)\sin(y)$
- `COS_PI`: Value of cosine at π: $\cos(\pi) = -1$
- `SIN_PI`: Value of sine at π: $\sin(\pi) = 0$
- `DIST_SEGMENT_LEMMA`: (Not stated but appears to express the distance between two points on a circle in terms of sines)

#### Definitions
- `sin`: The sine function defined as $\sin(x) = \text{Re}(\text{csin}(\text{Cx } x))$
- `cos`: The cosine function defined as $\cos(x) = \text{Re}(\text{ccos}(\text{Cx } x))$
- `pi`: The constant π defined as the smallest positive number where sine is zero

### Porting notes
When porting this theorem:
1. Ensure that the system has a good representation of points on a circle using parametric equations.
2. The proof relies heavily on trigonometric identities, so ensure those are available.
3. The `DIST_SEGMENT_LEMMA` seems crucial - you'll need an equivalent that expresses the distance between points on a circle in terms of the sine of half the angle difference.
4. The final step uses `REAL_RING`, which is an automated simplification for real arithmetic. You may need to decompose this into more explicit algebraic steps in systems with less powerful automation.

---

