# cosine.ml

## Overview

Number of statements: 18

This file formalizes several fundamental results from trigonometry, specifically the law of cosines, the law of sines, and the theorem about the sum of angles in a triangle. Building on the transcendental functions library, it provides formal definitions and proofs of these classical geometric results in the context of Euclidean geometry. These results form essential components for more advanced geometric reasoning within the HOL Light framework.

## vangle

### Name of formal statement
vangle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let vangle = new_definition
 `vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;
```

### Informal statement
The angle between two vectors $x$ and $y$ is defined as:

$$\text{vangle}(x, y) = \begin{cases}
\frac{\pi}{2} & \text{if } x = \vec{0} \text{ or } y = \vec{0} \\
\arccos\left(\frac{x \cdot y}{||x|| \cdot ||y||}\right) & \text{otherwise}
\end{cases}$$

where $x \cdot y$ denotes the dot product, $||x||$ and $||y||$ denote the norms of the vectors, and $\arccos$ is the inverse cosine function.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition provides a standard way to calculate the angle between two vectors. Key features:

- The definition uses the well-known formula $\cos(\theta) = \frac{x \cdot y}{||x|| \cdot ||y||}$ which relates the cosine of the angle between two vectors to their dot product and norms.
- The definition handles the special case where either vector is zero by assigning the angle $\frac{\pi}{2}$ (90 degrees), since the direction of a zero vector is undefined.
- The resulting angle is always in the range $[0, \pi]$, as the arccos function returns values in this range.
- This definition is fundamental for various geometric calculations, including the law of cosines and law of sines mentioned in the comments.

### Dependencies
#### Definitions:
- `pi`: The mathematical constant π, defined as the smallest positive number where sine equals zero
- `acs`: The arccosine function, defined as the real part of the complex arccosine applied to the complex representation of a real number

### Porting notes
When porting this definition:
- Ensure that the ported system has appropriate handling for vector operations (dot product, norm).
- The special case for zero vectors is important to maintain. Some systems might require a different approach to define well-behaved angle calculations when zero vectors are involved.
- Verify that the arccosine function used returns values in $[0, \pi]$, which is the expected range for this angle definition.

---

## angle

### Name of formal statement
angle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let angle = new_definition
 `angle(a,b,c) = vangle (a - b) (c - b)`;;
```

### Informal statement
For points $a$, $b$, and $c$ in a vector space, $\text{angle}(a,b,c)$ is defined as the angle between the vectors $a - b$ and $c - b$, calculated using the $\text{vangle}$ function.

Specifically, $\text{angle}(a,b,c) = \text{vangle}(a - b, c - b)$, where $\text{vangle}$ computes the angle between two vectors, returning a value in the range $[0, \pi]$.

### Informal proof
This is a definition, so no proof is needed.

### Mathematical insight
This definition represents the traditional geometric notion of an angle formed by three points in a vector space, with the second point serving as the vertex.

The function computes the angle between the two rays extending from point $b$ to points $a$ and $c$, respectively. By using vector subtraction ($a - b$ and $c - b$), we create vectors pointing from the vertex $b$ to the other points, and then calculate the angle between these vectors.

The underlying $\text{vangle}$ function ensures that the returned angle is always in the range $[0, \pi]$, which corresponds to the standard convention for unsigned angles in geometry. This means the function doesn't distinguish between clockwise and counterclockwise orientations.

This definition is particularly useful in computational geometry, computer graphics, and formal representations of geometric theorems.

### Dependencies
- `vangle`: Function that calculates the angle between two vectors, returning a value in $[0, \pi]$.

### Porting notes
When porting this definition to another system, ensure that:
1. The underlying vector operations (subtraction) are properly defined.
2. The system has a corresponding definition for `vangle` that computes angles between vectors.
3. Check how the target system handles domain constraints - the implementation should maintain the $[0, \pi]$ range for angles.

---

## VANGLE

### VANGLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VANGLE = prove
 (`!x y:real^N. x dot y = norm(x) * norm(y) * cos(vangle x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; NORM_0; REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO; NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c:real = c * a * b`] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(GSYM COS_ACS) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_LT_MUL] THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any vectors $x, y \in \mathbb{R}^N$, the dot product of $x$ and $y$ is equal to the product of their norms multiplied by the cosine of the angle between them:

$$x \cdot y = \|x\| \cdot \|y\| \cdot \cos(\text{vangle}(x, y))$$

where $\text{vangle}(x, y)$ represents the angle between vectors $x$ and $y$.

### Informal proof
The proof proceeds as follows:

- First, we handle special cases where either vector is the zero vector:
  - If $x = \vec{0}$, then $x \cdot y = 0$ and $\|x\| = 0$, so both sides equal zero.
  - If $y = \vec{0}$, then $x \cdot y = 0$ and $\|y\| = 0$, so both sides equal zero.

- For the case where both vectors are non-zero:
  - We rearrange the terms using commutativity of multiplication to get $\cos(\text{vangle}(x, y)) = \frac{x \cdot y}{\|x\| \cdot \|y\|}$.
  - We apply the `COS_ACS` theorem which states that for any $y$ with $-1 \leq y \leq 1$, we have $\cos(\arccos(y)) = y$.
  - We need to verify that $\frac{x \cdot y}{\|x\| \cdot \|y\|}$ is indeed between $-1$ and $1$.
  - This follows from the Cauchy-Schwarz inequality, which states that $|x \cdot y| \leq \|x\| \cdot \|y\|$.
  - Therefore, $-1 \leq \frac{x \cdot y}{\|x\| \cdot \|y\|} \leq 1$, completing the proof.

### Mathematical insight
This theorem states the fundamental relationship between the dot product of two vectors and the angle between them. This is one of the most important results in vector algebra and serves as the foundation for many geometric concepts in linear algebra.

The formula expresses the geometric interpretation of the dot product: it measures how much two vectors point in the same direction. When the vectors are parallel, the cosine is 1; when they are perpendicular, the cosine is 0; and when they point in opposite directions, the cosine is -1.

This result connects algebraic operations (dot product) with geometric concepts (angles between vectors), making it essential for applications in physics, computer graphics, and many other fields.

### Dependencies
- Theorems:
  - `COS_ACS`: For any $y$ with $-1 \leq y \leq 1$, $\cos(\arccos(y)) = y$
  - `NORM_CAUCHY_SCHWARZ_ABS`: The Cauchy-Schwarz inequality: $|x \cdot y| \leq \|x\| \cdot \|y\|$

- Definitions:
  - `cos`: The cosine function defined as $\cos(x) = \text{Re}(\cos_{\mathbb{C}}(Cx(x)))$
  - `vangle`: The angle between two vectors

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the `vangle` function is defined correctly, typically as $\arccos\left(\frac{x \cdot y}{\|x\| \cdot \|y\|}\right)$ for non-zero vectors.
- Be careful with the special cases where either vector is zero, as the angle is generally undefined in these cases.
- The Cauchy-Schwarz inequality is a standard result available in most mathematical libraries, but its formulation might vary.

---

## VANGLE_RANGE

### Name of formal statement
VANGLE_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VANGLE_RANGE = prove
 (`!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN COND_CASES_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a`) THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;
```

### Informal statement
For any vectors $x, y$ in $\mathbb{R}^N$, the vector angle between $x$ and $y$ satisfies $0 \leq \text{vangle}(x, y) \leq \pi$.

### Informal proof
The proof establishes bounds on the vector angle by considering its definition and using properties of the arc cosine function.

* Begin by expanding the definition of `vangle` and considering two cases.
* In the first case, when either vector is zero, `vangle` is defined to be $\pi$ by convention, and the result follows from $0 < \pi$ (theorem `PI_POS`).
* In the second case, when both vectors are non-zero:
  * Rewrite the negation of the previous case using De Morgan's law
  * Apply `ACS_BOUNDS` which states that $-1 \leq y \leq 1$ implies $0 \leq \arccos(y) \leq \pi$
  * Simplify using properties of division and inequalities (specifically that both norms are positive)
  * Show that the dot product divided by the product of norms has absolute value at most 1
  * Apply the Cauchy-Schwarz inequality: $|x \cdot y| \leq \|x\| \cdot \|y\|$
  * Therefore $\frac{x \cdot y}{\|x\| \cdot \|y\|}$ is between $-1$ and $1$, so $\arccos$ of this value is between $0$ and $\pi$

### Mathematical insight
This theorem establishes the fundamental range constraint for the angle between two vectors. The vector angle is defined as the arc cosine of the normalized dot product of the vectors, with a special case when either vector is zero. This result confirms that vector angles in $\mathbb{R}^N$ behave as expected geometrically, ranging from 0 (same direction) to $\pi$ (opposite direction).

The special case handling for zero vectors is an important aspect of the definition, setting the angle to $\pi$ by convention when either vector is zero.

### Dependencies
- Theorems:
  - `PI_POS`: States that $\pi > 0$
  - `ACS_BOUNDS`: States that if $-1 \leq y \leq 1$, then $0 \leq \arccos(y) \leq \pi$
- Definitions:
  - `pi`: Defined as the smallest positive value where sine is zero
  - `vangle`: (implicit) Angle between two vectors, defined as the arc cosine of their normalized dot product
- Other relevant results:
  - `NORM_CAUCHY_SCHWARZ_ABS`: The Cauchy-Schwarz inequality in terms of vector norms
  - `NORM_POS_LT`: A norm is positive for non-zero vectors

### Porting notes
When porting this theorem:
1. Ensure that the `vangle` function has the same definition, particularly the special case for zero vectors
2. Check how the arc cosine function's range is defined in the target system
3. Verify that the Cauchy-Schwarz inequality is available in the form needed for this proof

---

## ORTHOGONAL_VANGLE

### ORTHOGONAL_VANGLE
- orthogonal_vangle

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ORTHOGONAL_VANGLE = prove
 (`!x y:real^N. orthogonal x y <=> vangle x y = pi / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal; vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
  EQ_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM real_div; GSYM COS_PI2] THEN
    MATCH_MP_TAC ACS_COS THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ;
                 REAL_LT_MUL; NORM_POS_LT] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
    ASM_SIMP_TAC[COS_ACS; COS_PI2] THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_REWRITE_TAC[NORM_EQ_0]]);;
```

### Informal statement
For any vectors $x, y \in \mathbb{R}^N$, they are orthogonal if and only if the angle between them is $\pi/2$ (90 degrees).

Formally: $\forall x,y \in \mathbb{R}^N, \text{orthogonal}(x,y) \iff \text{vangle}(x,y) = \pi/2$

### Informal proof
The proof establishes the equivalence between vector orthogonality and vectors having a right angle between them:

- First, we use the definitions of orthogonality and vector angle.
- We handle special cases when either vector is zero:
  * If $x = \vec{0}$ or $y = \vec{0}$, then the dot product is zero, making them orthogonal.
  
- For the forward direction ($\Rightarrow$):
  * If the vectors are orthogonal, then $x \cdot y = 0$.
  * This means $\cos(\text{vangle}(x,y)) = 0$ (since $\text{vangle}$ is defined using $\cos^{-1}$).
  * But $\cos(\pi/2) = 0$, so $\text{vangle}(x,y) = \pi/2$.
  * We use `ACS_COS` (which states that $\cos^{-1}(\cos(x)) = x$ for $0 \leq x \leq \pi$) to prove this.

- For the reverse direction ($\Leftarrow$):
  * If $\text{vangle}(x,y) = \pi/2$, we need to show that $x \cdot y = 0$.
  * We use the Cauchy-Schwarz inequality which gives us that $|x \cdot y| \leq \|x\| \cdot \|y\|$.
  * This means the value $\frac{x \cdot y}{\|x\| \cdot \|y\|}$ is in $[-1,1]$.
  * Since $\text{vangle}(x,y) = \cos^{-1}(\frac{x \cdot y}{\|x\| \cdot \|y\|}) = \pi/2$, and $\cos(\pi/2) = 0$, 
  * We apply $\cos$ to both sides and use `COS_ACS` to get $\frac{x \cdot y}{\|x\| \cdot \|y\|} = 0$.
  * Since $\|x\|$ and $\|y\|$ are non-zero (we handled zero cases earlier), we conclude $x \cdot y = 0$.

### Mathematical insight
This theorem formally establishes the geometric interpretation of orthogonality in vector spaces. While it may seem intuitively obvious that orthogonal vectors form a right angle, this proof connects the algebraic definition (zero dot product) with the geometric concept (90-degree angle).

This relationship is foundational in linear algebra, geometry, and many applications. The proof carefully manages the edge cases of zero vectors, for which the angle concept is technically undefined but orthogonality still has meaning.

The result is particularly important because it provides a way to translate between analytical properties (orthogonality) and geometric properties (angles), allowing problems to be approached from whichever perspective is most convenient.

### Dependencies
- **Theorems**:
  - `COS_PI2`: $\cos(\pi/2) = 0$
  - `PI_POS`: $0 < \pi$
  - `ACS_COS`: $\forall x. 0 \leq x \land x \leq \pi \Rightarrow \cos^{-1}(\cos(x)) = x$
  - `COS_ACS`: $\forall y. -1 \leq y \land y \leq 1 \Rightarrow \cos(\cos^{-1}(y)) = y$
  
- **Definitions**:
  - `cos`: $\cos(x) = \text{Re}(\cos_\mathbb{C}(\mathbb{C}x))$
  - `pi`: $\pi$ is defined as the smallest positive real number where sine equals zero

### Porting notes
When porting this theorem, consider:
- Different proof assistants may have different ways of handling undefined cases like angles between zero vectors.
- The representation of vector angle may vary between libraries - ensure it's defined consistently with how it's used in this proof.
- The Cauchy-Schwarz inequality is used in the proof and should be available in your target system.
- Some systems might use different names or have different conventions for basic trigonometric functions.

---

## VANGLE_EQ_PI

### Name of formal statement
VANGLE_EQ_PI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VANGLE_EQ_PI = prove
 (`!x y:real^N. vangle x y = pi ==> norm(x) % y + norm(y) % x = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] VANGLE) THEN
  ASM_REWRITE_TAC[COS_PI] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `--y:real^N`] NORM_CAUCHY_SCHWARZ_EQ) THEN
  REWRITE_TAC[NORM_NEG; DOT_RNEG; VECTOR_MUL_RNEG] THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
  VECTOR_ARITH_TAC);;
```

### Informal statement
For any vectors $x, y \in \mathbb{R}^N$, if the vector angle between $x$ and $y$ equals $\pi$ radians, then:
$\|x\| \cdot y + \|y\| \cdot x = \vec{0}$

Where:
- $\|x\|$ denotes the Euclidean norm of vector $x$
- $\cdot$ between a scalar and vector represents scalar multiplication
- $\vec{0}$ is the zero vector

### Informal proof
We prove that when the angle between two vectors $x$ and $y$ is $\pi$ radians (meaning they point in opposite directions), their weighted sum as specified equals the zero vector.

The proof proceeds as follows:

- Apply the `VANGLE` theorem, which relates the vector angle to the dot product:
  $\cos(\text{vangle}(x, y)) = \frac{x \cdot y}{\|x\| \cdot \|y\|}$
  
- Since we know $\text{vangle}(x, y) = \pi$, we substitute this value and use the fact that $\cos(\pi) = -1$ (from the `COS_PI` theorem)

- This gives us $\frac{x \cdot y}{\|x\| \cdot \|y\|} = -1$, which implies $x \cdot y = -\|x\| \cdot \|y\|$

- Next, we apply the equality case of the Cauchy-Schwarz inequality (`NORM_CAUCHY_SCHWARZ_EQ`) to the vectors $x$ and $-y$

- The Cauchy-Schwarz equality case states that $|x \cdot (-y)| = \|x\| \cdot \|-y\|$ if and only if $x$ and $-y$ are linearly dependent, meaning there exists a scalar $t$ such that $x = t \cdot (-y)$

- We use the properties $\|-y\| = \|y\|$ and $x \cdot (-y) = -(x \cdot y) = \|x\| \cdot \|y\|$ (from our earlier derivation)

- This confirms that $x$ and $-y$ are linearly dependent, which means $x = t \cdot (-y)$ for some scalar $t$

- From vector arithmetic, we can determine that $\|x\| \cdot y + \|y\| \cdot x = \vec{0}$

### Mathematical insight
This theorem captures a fundamental property of vectors at angle $\pi$: when two vectors point in exactly opposite directions, a specific weighted combination of them (weighted by the other's norm) yields the zero vector.

The result is intuitive when considered geometrically - when vectors point in opposite directions, they can perfectly cancel each other out when scaled appropriately. The precise scaling factors (the norms of the respective vectors) ensure this perfect cancellation.

This theorem is also related to the equality case of the Cauchy-Schwarz inequality when the vectors are negatively proportional to each other, representing the extreme scenario of maximum negative correlation between two vectors.

### Dependencies
#### Theorems
- `VANGLE`: Relates the vector angle to the dot product using cosine
- `COS_PI`: States that $\cos(\pi) = -1$
- `NORM_CAUCHY_SCHWARZ_EQ`: The equality case of the Cauchy-Schwarz inequality

#### Definitions
- `pi`: Defined as the smallest positive number where sine equals zero

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate definitions for vector angles, especially how they relate to the dot product
2. Verify that the target system handles the normalization of vectors consistently
3. The proof relies heavily on the Cauchy-Schwarz inequality's equality case, so make sure this is available in your target system

---

## ANGLE_EQ_PI

### Name of formal statement
ANGLE_EQ_PI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_EQ_PI = prove
 (`!A B C:real^N. angle(A,B,C) = pi ==> dist(A,C) = dist(A,B) + dist(B,C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VANGLE_EQ_PI) THEN
  REWRITE_TAC[VECTOR_ARITH `a + x % (b - c) = vec 0 <=> a = x % (c - b)`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV) [NORM_SUB] THEN
  REWRITE_TAC[GSYM NORM_TRIANGLE_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `(B - A) + (C - B):real^N = C - A`] THEN
  REWRITE_TAC[dist; NORM_SUB]);;
```

### Informal statement
For any three points $A$, $B$, and $C$ in $\mathbb{R}^N$, if the angle $\angle(A,B,C) = \pi$, then the distance from $A$ to $C$ equals the sum of the distances from $A$ to $B$ and from $B$ to $C$:

$$\forall A, B, C \in \mathbb{R}^N.\ \angle(A,B,C) = \pi \Rightarrow \text{dist}(A,C) = \text{dist}(A,B) + \text{dist}(B,C)$$

### Informal proof
The theorem states that when three points form an angle of $\pi$ radians (a straight line), the distance from the first point to the third equals the sum of the distances between consecutive points.

The proof proceeds as follows:
- We begin by expanding the definition of `angle` and applying the theorem `VANGLE_EQ_PI`, which relates an angle of $\pi$ to vector properties.
- The vector equality is rewritten to show that $a = x \cdot (c - b)$ when $a + x \cdot (b - c) = 0$.
- The left side of the equation is rewritten using `NORM_SUB`, which states that $\|a - b\| = \|b - a\|$.
- We apply `NORM_TRIANGLE_EQ`, which provides the condition for equality in the triangle inequality: $\|a + b\| = \|a\| + \|b\|$ if and only if $a$ and $b$ are positively proportional.
- The vector sum $(B - A) + (C - B)$ simplifies to $C - A$.
- Finally, we use the definition of distance: $\text{dist}(X,Y) = \|X - Y\|$.

This chain of reasoning establishes that when the angle is $\pi$, the points are collinear with $B$ between $A$ and $C$, which implies that the distance from $A$ to $C$ equals the sum of the distances from $A$ to $B$ and from $B$ to $C$.

### Mathematical insight
This theorem formalizes the intuitive geometric fact that when three points lie on a straight line (with the middle point between the other two), the distance between the endpoints equals the sum of the distances to the middle point. It is equivalent to the statement that the angle $\angle(A,B,C) = \pi$ means that $B$ lies directly between $A$ and $C$ on a straight line.

In Euclidean geometry, this property characterizes collinearity of three points where the middle point is between the other two. It's a fundamental result that connects angular measure with distance relationships in Euclidean space.

### Dependencies
#### Definitions:
- `pi`: Defined as the smallest positive number $p$ where $\sin(p) = 0$ and $\sin(x) \neq 0$ for all $x \in (0,p)$

#### Theorems (inferred from the proof):
- `VANGLE_EQ_PI`: Relating an angle of $\pi$ to vector properties
- `NORM_SUB`: Stating that $\|a - b\| = \|b - a\|$
- `NORM_TRIANGLE_EQ`: Providing conditions for equality in the triangle inequality
- `angle`: Definition of the angle between three points

### Porting notes
When porting this theorem:
- Ensure the definition of `angle` is consistent with HOL Light's definition
- The vector arithmetic simplifications might need explicit justification in other systems
- The use of `NORM_TRIANGLE_EQ` is critical - this provides the condition for equality in the triangle inequality, which is essential to the proof

---

## SIN_ANGLE_POS

### Name of formal statement
SIN_ANGLE_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_ANGLE_POS = prove
 (`!A B C. &0 <= sin(angle(A,B,C))`,
  SIMP_TAC[SIN_POS_PI_LE; angle; VANGLE_RANGE]);;
```

### Informal statement
For all points $A$, $B$, and $C$, the sine of the angle formed by these three points, denoted as $\sin(\angle(A,B,C))$, is always non-negative.

Formally: $\forall A, B, C. 0 \leq \sin(\angle(A,B,C))$

### Informal proof
The proof relies on two key facts:
- From `VANGLE_RANGE`: the angle between three points is always in the range $[0, \pi]$
- From `SIN_POS_PI_LE`: for any $x$ where $0 \leq x \leq \pi$, we have $0 \leq \sin(x)$

The proof is straightforward:
1. We first simplify the goal using the theorem `SIN_POS_PI_LE` and the definition of `angle`.
2. Since the result of `angle(A,B,C)` is always in the range $[0, \pi]$ (as established by `VANGLE_RANGE`), we can apply `SIN_POS_PI_LE` directly.
3. The `SIMP_TAC` tactic combines these steps automatically to complete the proof.

### Mathematical insight
This theorem establishes a fundamental property of the sine of angles in geometry: when measuring the angle between three points, the sine of that angle is always non-negative.

This is consistent with the geometric understanding that angles in a standard configuration (measured counterclockwise) between three points are typically considered to be in the range $[0, \pi]$, which corresponds to the first and second quadrants of the unit circle where sine is non-negative.

The result is important for calculations involving angles in computational geometry, trigonometric applications, and vector analysis, ensuring that certain expressions involving $\sin(\angle(A,B,C))$ maintain their expected sign.

### Dependencies
- **Theorems**:
  - `SIN_POS_PI_LE`: For any $x$ where $0 \leq x \leq \pi$, we have $0 \leq \sin(x)$
  - `VANGLE_RANGE` (implicit): Establishes that angles between three points are in the range $[0, \pi]$

- **Definitions**:
  - `sin`: Defined as $\sin(x) = \text{Re}(\text{csin}(\text{Cx } x))$, where $\text{Re}$ extracts the real part of a complex number, $\text{csin}$ is the complex sine function, and $\text{Cx}$ converts a real number to a complex number
  - `angle` (implicit): Defines the angle measure between three points

### Porting notes
When porting this theorem to other systems:
1. Ensure the definition of angle between three points is consistent with HOL Light's definition
2. Verify that the range of angles in the target system matches HOL Light's $[0, \pi]$ convention
3. The proof is straightforward once the angle range and sine properties are established, so it should translate easily to other proof assistants

---

## ANGLE

### Name of formal statement
ANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE = prove
 (`!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`,
  REWRITE_TAC[angle; dist; GSYM VANGLE]);;
```

### Informal statement
For all points $A$, $B$, and $C$ in a Euclidean space, the dot product of vectors $A - C$ and $B - C$ equals the product of the distances $dist(A,C)$ and $dist(B,C)$ multiplied by the cosine of the angle formed at $C$ between points $A$ and $B$:

$$\forall A,B,C.\ (A - C) \cdot (B - C) = dist(A,C) \cdot dist(B,C) \cdot \cos(\angle ACB)$$

### Informal proof
The proof is straightforward, using rewriting tactics:

1. The theorem is proved by rewriting using the definition of `angle`, `dist`, and applying the generalized vector angle theorem `VANGLE`.

2. The definition of `angle` relates the geometric angle at point $C$ to the mathematical angle between vectors.

3. The `dist` function computes the Euclidean distance between two points.

4. The `VANGLE` theorem relates dot products of vectors to the cosine of angles between them.

5. Applying these rewritings transforms the goal into a form that follows directly from the properties of vector geometry.

### Mathematical insight
This theorem expresses the law of cosines in vector form, showing how dot products relate to angles and distances in Euclidean geometry. The result is fundamental in coordinate geometry and has applications in:

- Computational geometry
- Computer graphics
- Physics simulations
- Distance calculations

It provides a convenient way to calculate angles between points using only dot products and distances, which is computationally efficient. This formulation is particularly useful for algorithms that need to compute angles in Euclidean spaces.

### Dependencies
- **Definitions:**
  - `cos`: Cosine function defined as `cos(x) = Re(ccos(Cx x))`, where `Re` extracts the real part and `Cx` converts a real number to a complex number
  - `angle`: Definition of the angle between three points
  - `dist`: Euclidean distance function
  
- **Theorems:**
  - `VANGLE`: The generalized theorem about angles between vectors

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the vector operations (dot product, vector subtraction) are properly defined
- Make sure the `angle` function has the same mathematical meaning (the angle at point C between points A and B)
- The definition of cosine may differ in other systems, but the mathematical meaning should be preserved
- The distance function should be the standard Euclidean distance

---

## ANGLE_REFL

### Name of formal statement
ANGLE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_REFL = prove
 (`!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_REFL]);;
```

### Informal statement
For any points $A$ and $B$: 
- $\angle(A, A, B) = \frac{\pi}{2}$
- $\angle(B, A, A) = \frac{\pi}{2}$

Where $\angle(P, Q, R)$ denotes the angle between vectors $\overrightarrow{QP}$ and $\overrightarrow{QR}$.

### Informal proof
This theorem states that when a vertex of an angle coincides with one of its endpoints, the angle is a right angle ($\frac{\pi}{2}$).

The proof follows directly by:
- Expanding the definitions of `angle`, `vangle`, and using the property of vector subtraction
- When $A = A$ in $\angle(A, A, B)$, we get $\overrightarrow{AA} = \vec{0}$
- Similarly, for $\angle(B, A, A)$, we have $\overrightarrow{AA} = \vec{0}$
- Since `vangle` is defined as the angle between two vectors, when one vector is zero, the angle is $\frac{\pi}{2}$ by definition

The proof applies `REWRITE_TAC` to expand the definitions and simplify using `VECTOR_SUB_REFL`, which states that $\vec{v} - \vec{v} = \vec{0}$.

### Mathematical insight
This theorem handles the degenerate case of angles where one point appears twice at the vertex or an endpoint. While such angles are geometrically not well-defined in Euclidean geometry, the formal definition in HOL Light assigns them the value of $\frac{\pi}{2}$ (right angle).

This convention allows for clean handling of edge cases in geometric theorems without requiring separate treatment of degenerate cases. The choice of $\frac{\pi}{2}$ maintains consistency with perpendicularity, since a zero vector can be considered perpendicular to any non-zero vector.

### Dependencies
#### Definitions
- `pi` - The constant π defined as the smallest positive number where sin(π) = 0
- `angle` - Angle between three points in Euclidean space
- `vangle` - Angle between two vectors
- `VECTOR_SUB_REFL` - A theorem stating that subtracting a vector from itself results in a zero vector

### Porting notes
When porting this theorem:
- Ensure the angle function in the target system handles degenerate cases similarly
- Verify that angles between vectors are defined consistently, especially the convention that an angle involving a zero vector equals π/2
- Be aware that some systems might forbid degenerate angles rather than assigning them values

---

## ANGLE_REFL_MID

### Name of formal statement
ANGLE_REFL_MID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_REFL_MID = prove
 (`!A B. ~(A = B) ==> angle(A,B,A) = &0`,
  SIMP_TAC[angle; vangle; VECTOR_SUB_EQ; GSYM NORM_POW_2; GSYM REAL_POW_2;
           REAL_DIV_REFL; ACS_1; REAL_POW_EQ_0; ARITH; NORM_EQ_0]);;
```

### Informal statement
For any points $A$ and $B$ in a Euclidean space, if $A \neq B$, then the angle $\angle(A,B,A) = 0$.

This theorem states that if we consider a degenerate triangle where a vertex $A$ appears twice, then the angle at the middle vertex $B$ is zero.

### Informal proof
The proof proceeds by simplification of the definition of angle:

- The function `angle(A,B,A)` computes the angle between the vectors $\overrightarrow{BA}$ and $\overrightarrow{BA}$ at vertex $B$.
- When the two vectors are identical (as they are in this case), their dot product equals the product of their norms, making $\cos(\theta) = 1$.
- The angle is computed as $\arccos$ of this value, which is $\arccos(1) = 0$.

Specifically, the proof applies simplification tactics using:
- The definition of `angle` which reduces to the `vangle` between two vectors
- Since we're computing the angle between identical vectors, the dot product equals the squared norm
- Using the fact that $\arccos(1) = 0$ (from `ACS_1`)
- Various arithmetic and normalization properties

### Mathematical insight
This theorem handles the edge case when calculating angles in geometric configurations. It confirms the intuitive fact that when we have two identical rays from a point, the angle between them is zero.

While this may seem trivial, explicitly proving such basic properties is important in a formal system to ensure that all edge cases are handled correctly. This theorem would be useful in proofs about geometric constructions and triangles.

### Dependencies
#### Theorems:
- `ACS_1`: Establishes that $\arccos(1) = 0$

#### Definition related:
- `angle`: Definition of angle between three points
- `vangle`: Definition of angle between two vectors

#### Other standard properties used:
- Vector subtraction and equality
- Norm properties
- Real number arithmetic properties

### Porting notes
When porting this theorem:
- Ensure your system has a definition of angles that handles identical vectors correctly
- Check that your arccos function is defined with arccos(1) = 0
- Be prepared to handle the case distinction (A ≠ B) which is needed to ensure the vectors are non-zero

---

## ANGLE_SYM

### ANGLE_SYM
- angle(A,B,C) = angle(C,B,A)

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ANGLE_SYM = prove
 (`!A B C. angle(A,B,C) = angle(C,B,A)`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_EQ; DISJ_SYM; REAL_MUL_SYM; DOT_SYM]);;
```

### Informal statement
For all points $A$, $B$, and $C$, the angle $\angle ABC$ is equal to the angle $\angle CBA$.

In other words, the angle formed by three points is symmetric with respect to the order of the first and third points, keeping the middle point fixed.

### Informal proof
The proof is straightforward, using the definition of angle and basic properties of vector operations:

1. By the definition of `angle`, we need to show that `vangle(A-B, C-B) = vangle(C-B, A-B)`
2. The `vangle` function computes the angle between two vectors
3. For two vectors, the dot product is symmetric: $\vec{u} \cdot \vec{v} = \vec{v} \cdot \vec{u}$
4. The proof follows by applying:
   - The symmetry of disjunction (`DISJ_SYM`)
   - The symmetry of real multiplication (`REAL_MUL_SYM`)
   - The symmetry of the dot product (`DOT_SYM`)

These properties together establish that `vangle(A-B, C-B) = vangle(C-B, A-B)`, which proves the theorem.

### Mathematical insight
This theorem formalizes the basic geometric intuition that the measure of an angle doesn't depend on which ray we consider first - the angle is the same whether we view it from left-to-right or right-to-left. This is a fundamental property of angles in Euclidean geometry.

The result is important because it allows us to freely exchange the order of the first and third points when working with angles in proofs. This symmetry property is often taken for granted in informal mathematics but needs to be explicitly proven in a formal system.

### Dependencies
- Definitions:
  - `angle`: Definition of the angle formed by three points
  - `vangle`: Definition of the angle between two vectors

- Basic vector properties:
  - `VECTOR_SUB_EQ`: Vector subtraction equality
  - `DOT_SYM`: Symmetry of the dot product
  
- Basic logic and arithmetic:
  - `DISJ_SYM`: Symmetry of logical disjunction
  - `REAL_MUL_SYM`: Symmetry of real multiplication

### Porting notes
When porting this theorem:
- Ensure that your target system's definition of angles maintains the same semantic meaning as HOL Light's
- This theorem relies on the symmetry of the dot product and disjunction, which should be available in most theorem provers
- In systems with a different representation of angles, the proof might need adjustment while preserving the same mathematical content

---

## ANGLE_RANGE

### Name of formal statement
ANGLE_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_RANGE = prove
 (`!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`,
  REWRITE_TAC[angle; VANGLE_RANGE]);;
```

### Informal statement
For all points $A$, $B$, and $C$, the angle $\angle(A,B,C)$ is bounded between $0$ and $\pi$, i.e.,
$$\forall A, B, C.\ 0 \leq \angle(A,B,C) \leq \pi$$

### Informal proof
The proof is straightforward. The theorem is proved by rewriting the definition of `angle` and then applying the theorem `VANGLE_RANGE`. 

The function `angle(A,B,C)` represents the geometric angle between three points, where $B$ is the vertex. The definition of `angle` is expressed in terms of the function `vangle`, which computes the angle between vectors.

The theorem `VANGLE_RANGE` states that the angle between vectors is always between $0$ and $\pi$, and the rewriting step applies this result to the geometric angle between three points.

### Mathematical insight
This theorem establishes a fundamental property of angles in Euclidean geometry - they are always non-negative and never exceed $\pi$ radians (180 degrees). This property is essential for reasoning about geometric configurations and is used extensively in geometric theorems and constructions.

The result may seem obvious from a geometric perspective, but it's important to formalize this basic property to enable further geometric reasoning in a proof assistant.

### Dependencies
- Definitions:
  - `pi`: The mathematical constant $\pi$ defined as the smallest positive root of the sine function
  - `angle`: (not explicitly shown, but referenced) The function that computes the angle between three points
- Theorems:
  - `VANGLE_RANGE`: (not explicitly shown, but referenced) States that the angle between vectors is between 0 and $\pi$

### Porting notes
When porting this theorem, ensure that:
1. The angle function is defined consistently with the HOL Light definition
2. The constant $\pi$ is properly defined (as the smallest positive root of the sine function)
3. The corresponding theorem about vector angles (`VANGLE_RANGE`) is ported first

---

## LAW_OF_COSINES

### Name of formal statement
LAW_OF_COSINES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LAW_OF_COSINES = prove
 (`!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[angle; ONCE_REWRITE_RULE[NORM_SUB] dist; GSYM VANGLE;
              NORM_POW_2] THEN
  VECTOR_ARITH_TAC);;
```

### Informal statement
For any three points $A$, $B$, and $C$ in $\mathbb{R}^N$, the law of cosines states:

$$\|B - C\|^2 = \|A - B\|^2 + \|A - C\|^2 - 2\|A - B\|\|A - C\|\cos(\angle BAC)$$

where $\|B - C\|$ denotes the Euclidean distance between points $B$ and $C$, and $\angle BAC$ denotes the angle formed by the vectors $\overrightarrow{AB}$ and $\overrightarrow{AC}$ at point $A$.

### Informal proof
The proof proceeds by rewriting the statement in terms of vector operations:

1. First, we rewrite the distances in terms of vector norms: $\text{dist}(B,C) = \|B-C\|$
2. Then, we rewrite the angle in terms of vector angle (`VANGLE`) definition 
3. Finally, we apply vector arithmetic to verify the identity

The key step uses `VECTOR_ARITH_TAC`, which handles the algebraic manipulations automatically. This follows from the expansion of $\|B-C\|^2 = \|(B-A)-(C-A)\|^2$ and the dot product relation $\cos(\theta) = \frac{\vec{u} \cdot \vec{v}}{\|\vec{u}\|\|\vec{v}\|}$.

### Mathematical insight
The law of cosines generalizes the Pythagorean theorem to arbitrary triangles. When the angle is 90°, $\cos(\angle BAC) = 0$ and we recover the Pythagorean theorem. This theorem allows us to compute any side of a triangle if we know the other two sides and the included angle, making it a fundamental result in trigonometry, Euclidean geometry, and vector spaces.

This formulation is particularly elegant because it works in any dimension, not just the plane. It expresses a geometric relationship between distances that holds in $\mathbb{R}^N$ for any $N$.

### Dependencies
- **Definitions**:
  - `cos`: The cosine function defined as `cos(x) = Re(ccos(Cx x))`, where `Re` extracts the real part and `Cx` converts a real to a complex number
  - `angle`: The angle between three points
  - `dist`: The Euclidean distance function
  - `VANGLE`: The angle between vectors

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition for the angle between three points in n-dimensional space
2. The proof relies heavily on vector arithmetic automation (`VECTOR_ARITH_TAC`), so you may need to develop similar automation or expand the proof steps manually in systems with weaker automation
3. The definition of cosine may differ between systems, but the mathematical meaning should be consistent

---

## LAW_OF_SINES

### LAW_OF_SINES
- `LAW_OF_SINES`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LAW_OF_SINES = prove
 (`!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[SIN_ANGLE_POS; DIST_POS_LE; REAL_LE_MUL; ARITH] THEN
  REWRITE_TAC[REAL_POW_MUL; MATCH_MP
   (REAL_ARITH `x + y = &1 ==> x = &1 - y`) (SPEC_ALL SIN_CIRCLE)] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[ANGLE_REFL; COS_PI2] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NORM_EQ_0]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
   `~(a = &0) ==> a pow 2 * x = a pow 2 * y ==> x = y`)) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM dist] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN
  REWRITE_TAC[REAL_RING
   `a * (&1 - x) * b = c * (&1 - y) * d <=>
    a * b - a * b * x = c * d - c * d * y`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; GSYM ANGLE] THEN
  REWRITE_TAC[REAL_POW_MUL; dist; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;
```

### Informal statement
For any three points $A$, $B$, and $C$ in an $N$-dimensional Euclidean space $\mathbb{R}^N$:
$$\sin(\angle ABC) \cdot |BC| = \sin(\angle BAC) \cdot |AC|$$

where $\angle ABC$ denotes the angle at vertex $B$ formed by points $A$, $B$, and $C$, and $|BC|$ represents the Euclidean distance between points $B$ and $C$.

### Informal proof
The proof establishes the law of sines for points in $\mathbb{R}^N$ through these steps:

- We begin by squaring both sides of the equation, which is valid since both sides are non-negative.
- We use the Pythagorean identity $\sin^2(\theta) + \cos^2(\theta) = 1$ to rewrite $\sin^2(\theta) = 1 - \cos^2(\theta)$.
- We consider the case when $A = B$ separately:
  * When $A = B$, the angle $\angle ABC$ becomes $\pi/2$ (right angle), and $\cos(\pi/2) = 0$.
  * For the general case when $A \neq B$, we rewrite the equation in terms of vector operations.
- Using vector algebra, we express distances in terms of dot products: $|BC|^2 = (B-C)\cdot(B-C)$.
- We rewrite angles using the cosine formula: $\cos(\angle ABC) = \frac{(A-B)\cdot(C-B)}{|A-B||C-B|}$.
- After algebraic manipulations involving dot products and vector subtractions, we apply ring arithmetic to complete the proof.

### Mathematical insight
The law of sines is a fundamental result in trigonometry, usually stated for triangles in a plane. This theorem generalizes it to points in any $N$-dimensional Euclidean space. In the familiar 2D case, this law states that in a triangle, the ratio of the length of a side to the sine of the opposite angle is constant for all three sides.

This generalization is important because:
- It shows the law of sines is not just a planar property but a general property of angles and distances in Euclidean space.
- It relates the sines of angles to the distances between points in a way that preserves the essential geometric relationship regardless of dimension.
- It provides a tool for solving geometric problems in higher dimensions, just as it does in plane geometry.

### Dependencies
- **Theorems**:
  * `SIN_CIRCLE`: The Pythagorean identity $\sin^2(x) + \cos^2(x) = 1$
  * `COS_PI2`: $\cos(\pi/2) = 0$
- **Definitions**:
  * `sin`: The sine function defined as $\sin(x) = \text{Re}(\text{csin}(\text{Cx } x))$

### Porting notes
When porting this theorem:
- Ensure the definition of angle between vectors is consistent with HOL Light's definition.
- The proof relies on the geometric interpretation of dot products and vector norms, which should be available in most proof assistants.
- The algebraic manipulations are quite intricate, so a different proof strategy might be more suitable depending on the target system's libraries.
- Consider how your target system handles equality proofs using algebraic identities, as the ringed arithmetic used at the end may require different tactics in other systems.

---

## TRIANGLE_ANGLE_SUM_LEMMA

### Name of formal statement
TRIANGLE_ANGLE_SUM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_ANGLE_SUM_LEMMA = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`C:real^N`; `B:real^N`; `A:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] LAW_OF_SINES) THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; dist; NORM_SUB] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`angle(B:real^N,A,C)`; `angle(A:real^N,B,C)`; `angle(B:real^N,C,A)`] THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; ANGLE_SYM] THEN CONV_TAC REAL_RING);;
```

### Informal statement
For any three distinct points $A$, $B$, and $C$ in $\mathbb{R}^N$, the cosine of the sum of the three angles in the triangle formed by these points is equal to $-1$. Formally:

$$\forall A,B,C \in \mathbb{R}^N. A \neq B \land A \neq C \land B \neq C \implies \cos(\angle BAC + \angle ABC + \angle BCA) = -1$$

where $\angle BAC$ denotes the angle at vertex $A$ between the lines connecting $A$ to $B$ and $A$ to $C$.

### Informal proof
The proof establishes that the sum of angles in a triangle equals $\pi$ radians (or 180 degrees), since $\cos(\pi) = -1$. The proof proceeds as follows:

- The theorem is rewritten in terms of vector differences and norms to eliminate point equality conditions.
- The laws of cosines are applied to each of the three angles in the triangle:
  * The law of cosines for angle $BAC$
  * The law of cosines for angle $ABC$
  * The law of cosines for angle $BCA$
- The laws of sines are also applied to all three angles.
- The trigonometric identity $\sin^2(x) + \cos^2(x) = 1$ is applied to each angle.
- Additional trigonometric identities for $\cos(x+y)$ and $\sin(x+y)$ are used:
  * $\cos(x+y) = \cos(x)\cos(y) - \sin(x)\sin(y)$
  * $\sin(x+y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
- The symmetry of angles ($\angle XYZ = \angle ZYX$) is utilized where needed.
- Finally, algebraic manipulations using the real ring prove that $\cos(\angle BAC + \angle ABC + \angle BCA) = -1$.

### Mathematical insight
This theorem is a fundamental result in Euclidean geometry, establishing that the sum of the interior angles of a triangle is always equal to $\pi$ radians (180 degrees). This is evident from the fact that $\cos(\pi) = -1$, which means the sum of the angles equals $\pi$.

The result is particularly interesting because it's proven for triangles in any dimension $\mathbb{R}^N$, not just the plane. It represents one of the core properties of Euclidean geometry and is independent of the triangle's size or shape.

This theorem has numerous applications in trigonometry, coordinate geometry, and serves as a foundation for many other geometric results.

### Dependencies
- Trigonometric identities:
  * `SIN_CIRCLE`: The Pythagorean identity $\sin^2(x) + \cos^2(x) = 1$
  * `SIN_ADD`: The addition formula $\sin(x+y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
  * `COS_ADD`: The addition formula $\cos(x+y) = \cos(x)\cos(y) - \sin(x)\sin(y)$
- Geometric theorems:
  * `LAW_OF_COSINES`: Relates the sides of a triangle to the cosine of an angle
  * `LAW_OF_SINES`: Relates the sides of a triangle to the sines of the opposite angles
  * `ANGLE_SYM`: The symmetry property of angles
- Definitions:
  * `cos`: The cosine function
  * `angle`: The angle between vectors
  * `dist`: The distance function
  * `NORM_SUB`: The norm of vector difference

### Porting notes
When porting this theorem:
1. Ensure that your target system has appropriate definitions for angles between points in n-dimensional space
2. Verify that your system has the laws of sines and cosines properly defined for n-dimensional vectors
3. The proof relies heavily on algebraic manipulation of trigonometric expressions, so robust automation for trigonometric identities will be helpful
4. Note that HOL Light's `REAL_RING` tactic handles the final algebraic simplification - you may need to expand this step in systems with less powerful automation

---

## COS_MINUS1_LEMMA

### Name of formal statement
COS_MINUS1_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COS_MINUS1_LEMMA = prove
 (`!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. integer n /\ x = n * pi`
   (X_CHOOSE_THEN `nn:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[GSYM SIN_EQ_0] THENL
   [MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. nn = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_MUL_POS_LE]) THEN
    SIMP_TAC[PI_POS; REAL_ARITH `&0 < p ==> ~(p < &0) /\ ~(p = &0)`] THEN
    ASM_MESON_TAC[INTEGER_POS; REAL_LT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_RING `n = &1 ==> n * p = p`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE `n < 3 /\ ~(n = 0) /\ ~(n = 2) ==> n = 1`) THEN
  RULE_ASSUM_TAC(SIMP_RULE[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[COS_0; REAL_MUL_LZERO; COS_NPI] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers $x$, if $\cos(x) = -1$ and $0 \leq x < 3\pi$, then $x = \pi$.

### Informal proof
We need to prove that if $\cos(x) = -1$ and $0 \leq x < 3\pi$, then $x = \pi$. The proof proceeds as follows:

* First, we'll show that $x$ must be of the form $n\pi$ for some integer $n$.
  * From the identity $\sin^2(x) + \cos^2(x) = 1$ and our assumption that $\cos(x) = -1$, we get:
    * $\sin^2(x) + (-1)^2 = 1$
    * $\sin^2(x) + 1 = 1$
    * $\sin^2(x) = 0$
    * $\sin(x) = 0$
  * By the theorem `SIN_EQ_0`, which states that $\sin(x) = 0$ if and only if $x = n\pi$ for some integer $n$, we know that $x = n\pi$ for some integer $n$.

* Next, we show that $n$ must be a natural number.
  * Since $0 \leq x$ and $x = n\pi$, we have $0 \leq n\pi$.
  * Since $\pi > 0$ (from `PI_POS`), this means $n \geq 0$.
  * From the properties of integers, if $n$ is an integer and $n \geq 0$, then $n$ is a natural number.

* Finally, we determine which natural number $n$ must be.
  * Since $x < 3\pi$, we have $n\pi < 3\pi$, which means $n < 3$.
  * We need to eliminate other possibilities:
    * If $n = 0$, then $x = 0$, which means $\cos(x) = \cos(0) = 1$ (from `COS_0`). This contradicts our assumption that $\cos(x) = -1$.
    * If $n = 2$, then $x = 2\pi$, which means $\cos(x) = \cos(2\pi) = (-1)^2 = 1$ (using `COS_NPI`). This also contradicts our assumption that $\cos(x) = -1$.
  * Therefore, $n = 1$, which means $x = \pi$.

### Mathematical insight
This theorem identifies $\pi$ as the unique value in the interval $[0, 3\pi)$ where cosine equals $-1$. This result leverages the periodicity and symmetry properties of the cosine function.

The result is important because:
1. It precisely locates the first occurrence of $\cos(x) = -1$ on the positive real line
2. It's consistent with our understanding that cosine has a period of $2\pi$ and reaches $-1$ at odd multiples of $\pi$
3. It provides a fundamental characterization used in many trigonometric applications

### Dependencies
#### Theorems
- `COS_0`: $\cos(0) = 1$
- `SIN_CIRCLE`: $\sin^2(x) + \cos^2(x) = 1$ for all $x$
- `PI_POS`: $0 < \pi$
- `COS_NPI`: $\cos(n\pi) = (-1)^n$ for all natural numbers $n$
- `SIN_EQ_0`: $\sin(x) = 0$ if and only if there exists an integer $n$ such that $x = n\pi$

#### Definitions
- `cos`: Cosine function defined as $\cos(x) = \text{Re}(\cos_\mathbb{C}(\mathbb{C}x))$
- `pi`: Defined as the smallest positive number where sine equals zero

### Porting notes
When porting this theorem:
- Ensure your system has the standard trigonometric identities and properties established
- The proof relies on reasoning about integer and real arithmetic combined with trigonometric properties
- You may need to adjust the proof if your system has a different way of representing integer versus natural numbers
- The dependency on `SIN_CIRCLE` (the Pythagorean identity) is critical for the first part of the proof

---

## TRIANGLE_ANGLE_SUM

### TRIANGLE_ANGLE_SUM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TRIANGLE_ANGLE_SUM = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_MINUS1_LEMMA THEN
  ASM_SIMP_TAC[TRIANGLE_ANGLE_SUM_LEMMA; REAL_LE_ADD; ANGLE_RANGE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= p /\ &0 <= y /\ y <= p /\ &0 <= z /\ z <= p /\
    ~(x = p /\ y = p /\ z = p)
    ==> x + y + z < &3 * p`) THEN
  ASM_SIMP_TAC[ANGLE_RANGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ANGLE_EQ_PI)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [GSYM VECTOR_SUB_EQ])) THEN
  REWRITE_TAC[GSYM NORM_EQ_0; dist; NORM_SUB] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any three distinct points $A$, $B$, and $C$ in $\mathbb{R}^N$, the sum of the three angles in the triangle formed by these points is equal to $\pi$:

$$\forall A, B, C \in \mathbb{R}^N. A \neq B \land A \neq C \land B \neq C \implies \angle(B,A,C) + \angle(A,B,C) + \angle(B,C,A) = \pi$$

where $\angle(P,Q,R)$ denotes the angle at vertex $Q$ between the line segments $QP$ and $QR$.

### Informal proof
The proof establishes that the sum of angles in a triangle equals $\pi$ radians (180 degrees):

* First, we apply `COS_MINUS1_LEMMA` which relates the cosine of the sum of three angles to the condition that the sum equals $\pi$.

* We use `TRIANGLE_ANGLE_SUM_LEMMA` which provides the necessary relationship for the cosines of the angles in a triangle.

* We establish that each angle satisfies $0 \leq \angle \leq \pi$ using `ANGLE_RANGE`.

* We then need to prove that the three angles can't all simultaneously equal $\pi$, which would contradict the distinctness of the points.

* For this, we use `ANGLE_EQ_PI` which states that an angle equals $\pi$ if and only if the points are collinear in a specific order.

* By contradiction, if all angles were $\pi$, then the points would need to satisfy certain vector relationships that are incompatible with the assumption that they are distinct.

* Finally, we use arithmetic reasoning to complete the proof by showing that the sum of the three angles must be exactly $\pi$.

### Mathematical insight
This theorem states the fundamental property that the sum of angles in any triangle equals $\pi$ radians (or 180 degrees). While this result is well-known in Euclidean geometry for the plane, this formalization extends it to any dimension $\mathbb{R}^N$. The angles are defined using the dot product of vectors, which allows the concept of angle to be meaningfully defined in higher dimensions.

The theorem applies only to non-degenerate triangles (where all three points are distinct), and it represents one of the most basic and important results in Euclidean geometry. This result is often taught in elementary geometry and is a cornerstone for many more advanced theorems.

### Dependencies
- Definitions:
  - `pi`: The constant π, defined as the smallest positive number where sine equals zero
- Theorems (implied from proof):
  - `COS_MINUS1_LEMMA`: Relates the cosine of angle sums to π
  - `TRIANGLE_ANGLE_SUM_LEMMA`: Provides relationships between cosines of angles in a triangle
  - `ANGLE_RANGE`: States that angles are between 0 and π
  - `ANGLE_EQ_PI`: Characterizes when an angle equals π

### Porting notes
When porting this theorem:
1. Ensure that the angle definition in the target system is compatible with HOL Light's definition, which typically uses the dot product of vectors.
2. The proof relies on several specialized lemmas about angles and their cosines, which may need to be ported first.
3. The geometric reasoning might be handled differently in other systems, especially the manipulation of vector equations and angle relationships.
4. Check how the target system handles distinctness of points and non-degeneracy conditions for triangles.

---

