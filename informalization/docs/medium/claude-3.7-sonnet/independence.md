# independence.ml

## Overview

Number of statements: 46

This file proves the independence of the Euclidean axiom from Tarski's other axioms for geometry by formalizing the Klein model of the hyperbolic plane. It demonstrates that the model satisfies all of Tarski's axioms except the Euclidean axiom (10), for which it satisfies the negation, using hyperbolic betweenness and congruence relations. Together with previous results from the tarski.ml file (which showed that the Euclidean plane satisfies all axioms), this establishes the independence of the Euclidean axiom.

## ddist

### Name of formal statement
ddist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let ddist = new_definition
 `ddist(x:real^N,y:real^N) =
    if norm(x) < &1 /\ norm(y) < &1 then
     (&1 - x dot y) pow 2 / ((&1 - norm(x) pow 2) * (&1 - norm(y) pow 2)) - &1
    else dist(x,y)`;;
```

### Informal statement
The function $\text{ddist}$ defines a distance-like measure between two points $x$ and $y$ in $\mathbb{R}^N$ as follows:

$$\text{ddist}(x, y) = 
\begin{cases}
\frac{(1 - x \cdot y)^2}{(1 - \|x\|^2)(1 - \|y\|^2)} - 1 & \text{if } \|x\| < 1 \text{ and } \|y\| < 1 \\
\text{dist}(x, y) & \text{otherwise}
\end{cases}$$

where:
- $x \cdot y$ denotes the dot product of vectors $x$ and $y$
- $\|x\|$ denotes the norm of vector $x$
- $\text{dist}(x, y)$ denotes the standard Euclidean distance between $x$ and $y$

### Informal proof
This is a definition, so no proof is needed.

### Mathematical insight
This definition introduces a distance function used in the Klein model of the hyperbolic plane. The function defines a hyperbolic distance metric within the unit ball, and defaults to standard Euclidean distance outside it.

The formula inside the unit ball is known as the Klein-Hilbert metric. It has the property that straight lines in the Euclidean sense correspond to geodesics (shortest paths) in the hyperbolic geometry. This construction is fundamental in demonstrating the independence of the parallel postulate from other axioms of geometry.

As mentioned in the comments, this definition is part of a larger effort to show the independence of Tarski's Euclidean axiom by constructing a model (the Klein model of hyperbolic geometry) that satisfies all of Tarski's axioms except the Euclidean axiom.

The use of a default value (Euclidean distance) outside the unit ball is a technical convenience that simplifies some theorems by making them unconditional.

### Dependencies
None explicitly listed, but the definition uses standard mathematical operations and functions including:
- `norm` - vector norm
- `dist` - Euclidean distance
- `dot` - vector dot product

### Porting notes
When porting this definition:
1. Ensure your target system has appropriate vector operations (dot product, norm)
2. Be aware of potential differences in how conditional definitions are handled
3. The definition uses a fallback value outside the unit ball, which might require special handling in systems that prefer total functions
4. The definition works with vectors in any dimension (real^N), so the target system should support generic vector spaces

---

## DDIST_INCREASES_ONLINE

### DDIST_INCREASES_ONLINE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DDIST_INCREASES_ONLINE = prove
 (`!a b x:real^N.
      norm a < &1 /\ norm b < &1 /\ norm x < &1 /\ between x (a,b) /\ ~(x = b)
      ==> ddist(a,x) < ddist(a,b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[BETWEEN_REFL_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[ddist; real_div; REAL_INV_MUL] THEN
  SUBGOAL_THEN
   `norm(a:real^N) pow 2 < &1 /\ norm(b:real^N) pow 2 < &1 /\
    norm(x:real^N) pow 2 < &1`
  MP_TAC THENL [ASM_SIMP_TAC[ABS_SQUARE_LT_1; REAL_ABS_NORM]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a * inv x * inv b - &1 < c * inv x * d - &1 <=>
                          (a / b) / x < (c * d) / x`] THEN
  SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * inv b) * c:real = (a * c) / b`] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT] THEN
  SUBGOAL_THEN `(a:real^N) dot b < &1 /\ (a:real^N) dot x < &1` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[REAL_LET_TRANS; NORM_CAUCHY_SCHWARZ]
     `norm(x) * norm(y) < &1 ==> (x:real^N) dot y < &1`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_IN_SEGMENT]) THEN
  REWRITE_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `u:real` THEN
  ASM_CASES_TAC `u = &1` THEN
  ASM_SIMP_TAC[VECTOR_ARITH `(&1 - &1) % a + &1 % b:real^N = b`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[VECTOR_ARITH `(&1 - u) % a + u % b:real^N = a + u % (b - a)`] THEN
  ABBREV_TAC `c:real^N = b - a` THEN
  SUBGOAL_THEN `b:real^N = a + c` SUBST_ALL_TAC THENL
   [EXPAND_TAC "c" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(SIMP_RULE[VECTOR_ARITH `a + c:real^N = a <=> c = vec 0`]) THEN
  REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
    `(a + b:real^N) dot (a + b) = a dot a + &2 * a dot b + b dot b`] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REWRITE_TAC[DOT_LMUL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH
   `(&1 - (a + x * b)) pow 2 * (&1 - (a + &2 * b + c)) <
    (&1 - (a + b)) pow 2 * (&1 - (a + &2 * x * b + x * x * c)) <=>
    &0 < (&1 - a - b * x) * ((&1 - a) * c + b pow 2) * (&1 - x) +
         (&1 - a - b) * ((&1 - a) * c + b pow 2) * (&1 - x) * x`] THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC);
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC)] THEN
  TRY ASM_REAL_ARITH_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT; REAL_SUB_LT]);;
```

### Informal statement
The theorem states that for any three vectors $a, b, x \in \mathbb{R}^N$ such that:
- $\|a\| < 1$
- $\|b\| < 1$
- $\|x\| < 1$
- $x$ is between $a$ and $b$ (lies on the line segment from $a$ to $b$)
- $x \neq b$

Then the double distance from $a$ to $x$ is strictly less than the double distance from $a$ to $b$, i.e., $\text{ddist}(a, x) < \text{ddist}(a, b)$.

Here, double distance (ddist) is defined as:
$$\text{ddist}(a, b) = \frac{(1 - a \cdot b)^2}{(1 - \|a\|^2)(1 - \|b\|^2)} - 1$$

### Informal proof
The proof proceeds as follows:

- First, handle the trivial case where $b = a$. If that's true, the conditions lead to a contradiction because $x$ would be between $a$ and $a$ (which means $x = a$), but we also have $x \neq b$ (i.e., $x \neq a$), which is a contradiction.

- For the main proof, we expand the definition of ddist and need to show that:
  $$\frac{(1 - a \cdot x)^2}{(1 - \|a\|^2)(1 - \|x\|^2)} - 1 < \frac{(1 - a \cdot b)^2}{(1 - \|a\|^2)(1 - \|b\|^2)} - 1$$

- From the given conditions, we can deduce that $\|a\|^2 < 1$, $\|b\|^2 < 1$, and $\|x\|^2 < 1$.

- We also establish that $a \cdot b < 1$ and $a \cdot x < 1$ using the Cauchy-Schwarz inequality.

- Since $x$ is between $a$ and $b$, we can express $x$ as $x = (1-u)a + ub$ for some $u \in [0,1]$, and given $x \neq b$, we know $u \neq 1$.

- We substitute $b = a + c$ where $c = b - a$, so $x = a + uc$.

- The proof then involves extensive algebraic manipulation to show that the inequality holds by expanding dot products and exploiting the constraints on norms and the fact that $u < 1$.

- The final algebraic step shows that the difference of the expressions is positive, establishing the strict inequality.

### Mathematical insight
This theorem establishes a monotonicity property of the double distance function along line segments in the unit ball of $\mathbb{R}^N$. Double distance (ddist) is a key concept in conformal and hyperbolic geometry, particularly when working with the Poincaré ball model.

The result shows that as we move along a line segment from $a$ toward $b$ (but not reaching $b$), the double distance from $a$ to points on this segment increases strictly monotonically. This property is fundamental for understanding how distances behave in hyperbolic space when represented in the Poincaré ball model.

The proof technique combines vector algebra with clever algebraic manipulations to handle the non-trivial expression for double distance.

### Dependencies
This theorem depends on the definition of double distance (`ddist`) and standard properties of vectors and real numbers. The proof uses:

- Vector operations: dot products, norms, and vector arithmetic
- Properties of the `between` relation
- Cauchy-Schwarz inequality
- Basic properties of real numbers

### Porting notes
When porting this theorem:
- Ensure that the definition of `ddist` matches exactly, as this concept may not be standard in all proof assistants
- The proof relies heavily on algebraic manipulations that may need different tactics in other systems
- The representation of vectors and their operations (dot product, norm) should be established first
- The `between` relation on vectors needs to be properly defined

---

## DDIST_REFL

### Name of formal statement
DDIST_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_REFL = prove
 (`!x:real^N. ddist(x,x) = &0`,
  GEN_TAC THEN REWRITE_TAC[ddist; DIST_REFL; NORM_POW_2; NORM_LT_SQUARE] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For any point $x \in \mathbb{R}^N$, the squared distance from $x$ to itself is zero:
$$\forall x \in \mathbb{R}^N, \text{ddist}(x, x) = 0$$

where $\text{ddist}(x, y)$ represents the squared Euclidean distance between points $x$ and $y$.

### Informal proof
The proof proceeds as follows:

1. Start with a general point $x \in \mathbb{R}^N$
2. Rewrite the squared distance function using its definition: $\text{ddist}(x, y) = \|x - y\|^2$
3. Apply theorem `DIST_REFL` which states that the distance from any point to itself is zero: $\text{dist}(x, x) = \|x - x\| = 0$
4. Apply properties of norms: $\|0\|^2 = 0$
5. Finish the proof using real field automation

The proof essentially uses the fact that $\text{ddist}(x, x) = \|x - x\|^2 = \|0\|^2 = 0$.

### Mathematical insight
This theorem establishes a fundamental property of squared Euclidean distance: any point has zero squared distance to itself. This is a basic reflexivity property of the squared distance function that naturally follows from the definition of distance. While simple, this property is essential in many geometric algorithms and proofs that use squared distances (which are often preferable to actual distances because they avoid square root calculations).

### Dependencies
- `ddist` - Definition of squared Euclidean distance
- `DIST_REFL` - Theorem stating that the distance from a point to itself is zero
- `NORM_POW_2` - Properties of squared norms
- `NORM_LT_SQUARE` - Properties relating norms and their squares

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the squared distance function is properly defined
- The proof is straightforward and should translate easily to most systems
- The use of `REAL_FIELD` automation might need to be replaced with the target system's equivalent field automation or more explicit algebraic steps

---

## DDIST_SYM

### DDIST_SYM
- Symmetry property of discrete distance

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DDIST_SYM = prove
 (`!x y:real^N. ddist(x,y) = ddist(y,x)`,
  REWRITE_TAC[ddist; CONJ_ACI; REAL_MUL_AC; DIST_SYM; DOT_SYM]);;
```

### Informal statement
For all $x, y \in \mathbb{R}^N$, the discrete distance satisfies:
$$\operatorname{ddist}(x, y) = \operatorname{ddist}(y, x)$$

### Informal proof
The proof follows directly from:
- The definition of discrete distance (`ddist`)
- The symmetry property of the Euclidean distance (`DIST_SYM`)
- The symmetry property of the dot product (`DOT_SYM`)
- Associative-commutative properties of conjunction (`CONJ_ACI`) 
- Associative-commutative properties of real multiplication (`REAL_MUL_AC`)

The rewrite tactic applies these properties to transform the left-hand side into the right-hand side.

### Mathematical insight
This theorem establishes the symmetry property of the discrete distance function, which is a fundamental property expected of any distance function. The discrete distance is a variant of the standard distance function with specific properties, and symmetry is essential for it to behave as a proper metric: the distance from x to y should equal the distance from y to x.

### Dependencies
- Definitions:
  - `ddist`: Discrete distance function
- Theorems:
  - `DIST_SYM`: Symmetry property of Euclidean distance
  - `DOT_SYM`: Symmetry property of dot product 
  - `CONJ_ACI`: Associative-commutative-idempotent properties of conjunction
  - `REAL_MUL_AC`: Associative-commutative properties of real multiplication

### Porting notes
When porting to other systems, ensure that the definition of discrete distance is consistent with HOL Light's definition. The proof relies on basic symmetry properties of the underlying distance and dot product functions, which should be available in most mathematical libraries of proof assistants.

---

## DDIST_POS_LT

### Name of formal statement
DDIST_POS_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_POS_LT = prove
 (`!x y:real^N. ~(x = y) ==> &0 < ddist(x,y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(x:real^N) < &1 /\ norm(y:real^N) < &1` THENL
   [ASM_MESON_TAC[DDIST_INCREASES_ONLINE; DDIST_REFL; BETWEEN_REFL];
    ASM_SIMP_TAC[ddist; DIST_POS_LT]]);;
```

### Informal statement
For any two distinct points $x, y \in \mathbb{R}^N$, if $x \neq y$, then the directed distance between them is strictly positive: $0 < \text{ddist}(x, y)$.

### Informal proof
The proof uses case analysis on whether both points are inside the unit ball:

* Case 1: If $\|x\| < 1$ and $\|y\| < 1$ (both points inside the unit ball):
  - The proof uses the fact that directed distance increases along a line (from `DDIST_INCREASES_ONLINE`), combined with the reflexivity of directed distance (`DDIST_REFL`) and the reflexive property of the betweenness relation (`BETWEEN_REFL`).
  - This establishes that distinct points must have positive directed distance.

* Case 2: If either $\|x\| \geq 1$ or $\|y\| \geq 1$ (at least one point outside/on the unit ball):
  - In this case, the directed distance simplifies to regular Euclidean distance: $\text{ddist}(x,y) = \text{dist}(x,y)$
  - The theorem then follows immediately from the fact that the Euclidean distance between distinct points is positive (`DIST_POS_LT`).

### Mathematical insight
The directed distance (`ddist`) is a metric that measures distance between points in a way that takes into account their position relative to the unit ball. This theorem establishes a fundamental property of this distance function: it is strictly positive for distinct points, which is one of the essential properties of a metric.

For points inside the unit ball, the directed distance has special geometric properties, but regardless of where they are located, distinct points always have positive separation according to this metric.

### Dependencies
- **Theorems:**
  - `DDIST_INCREASES_ONLINE`: States that directed distance increases along a line
  - `DDIST_REFL`: Reflexivity of directed distance (distance from a point to itself is zero)
  - `BETWEEN_REFL`: Reflexivity of the betweenness relation
  - `DIST_POS_LT`: States that Euclidean distance between distinct points is positive

- **Definitions:**
  - `ddist`: The directed distance function

### Porting notes
When porting this theorem, ensure that the directed distance function (`ddist`) is properly defined first. The proof relies on different properties depending on whether the points are inside or outside the unit ball, so both cases need to be handled carefully in the target system.

---

## DDIST_POS_LE

### Name of formal statement
DDIST_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_POS_LE = prove
 (`!x y:real^N. &0 <= ddist(x,y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN
  ASM_SIMP_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LE_LT]);;
```

### Informal statement
For any two vectors $x$ and $y$ in $\mathbb{R}^N$, the discrete distance between them is non-negative:
$0 \leq \text{ddist}(x, y)$

### Informal proof
This theorem proves that the discrete distance between any two points in $\mathbb{R}^N$ is always non-negative.

The proof proceeds by case analysis:
- First, we consider the case where $x = y$.
  - If $x = y$, then by `DDIST_REFL`, we know that $\text{ddist}(x, x) = 0$.
  - Since $0 \leq 0$, the property holds in this case.
- Next, we consider the case where $x \neq y$.
  - If $x \neq y$, then by `DDIST_POS_LT`, we know that $0 < \text{ddist}(x, y)$.
  - Since any strictly positive real number is also non-negative (by `REAL_LE_LT`), the property holds in this case as well.

Therefore, for all vectors $x$ and $y$ in $\mathbb{R}^N$, we have $0 \leq \text{ddist}(x, y)$.

### Mathematical insight
The discrete distance function $\text{ddist}$ is a binary function that returns 0 if its two arguments are equal, and 1 otherwise. This theorem establishes one of the basic properties of any distance function - that distances are non-negative.

This property is one of the axioms of a metric space, which requires distances to be:
1. Non-negative (proven here)
2. Zero if and only if the points are identical 
3. Symmetric 
4. Satisfy the triangle inequality

The discrete distance is a simple but important metric that treats all distinct points as being at a fixed unit distance from each other. It's also sometimes called the discrete metric or trivial metric.

### Dependencies
- `DDIST_REFL`: Theorem stating that $\text{ddist}(x, x) = 0$
- `DDIST_POS_LT`: Theorem stating that if $x \neq y$, then $0 < \text{ddist}(x, y)$
- `REAL_LE_LT`: Theorem relating strict inequality and non-strict inequality for real numbers

### Porting notes
This theorem should be straightforward to port to other systems. The proof is simple and relies only on basic properties of the discrete distance function. When porting, ensure that the discrete distance function is properly defined first, along with its basic properties like `DDIST_REFL` and `DDIST_POS_LT`.

---

## DDIST_EQ_0

### Name of formal statement
DDIST_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_EQ_0 = prove
 (`!x y:real^N. ddist(x,y) = &0 <=> x = y`,
  MESON_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LT_REFL]);;
```

### Informal statement
For all points $x$ and $y$ in $\mathbb{R}^N$, the discrete distance between them, denoted as $\text{ddist}(x,y)$, equals $0$ if and only if $x = y$.

Formally:
$$\forall x,y \in \mathbb{R}^N, \text{ddist}(x,y) = 0 \iff x = y$$

### Informal proof
The proof uses the `MESON_TAC` tactic with three theorems:

1. From `DDIST_REFL`: The discrete distance between a point and itself is zero, i.e., $\text{ddist}(x,x) = 0$.
2. From `DDIST_POS_LT`: The discrete distance between distinct points is strictly positive, i.e., if $x \neq y$ then $\text{ddist}(x,y) > 0$.
3. From `REAL_LT_REFL`: No real number is strictly less than itself, i.e., $\neg(r < r)$ for any real number $r$.

The combination of these properties directly establishes the equivalence:
- Forward direction ($\text{ddist}(x,y) = 0 \Rightarrow x = y$): If $\text{ddist}(x,y) = 0$, then by `DDIST_POS_LT` and `REAL_LT_REFL`, we must have $x = y$.
- Reverse direction ($x = y \Rightarrow \text{ddist}(x,y) = 0$): This follows immediately from `DDIST_REFL`.

### Mathematical insight
This theorem establishes the identity of indiscernibles property for discrete distance in $\mathbb{R}^N$, which is one of the key properties required for a function to be a metric. The discrete distance function, often used in metric space theory, assigns a distance of 0 between identical points and a positive value between distinct points.

The result is fundamental for discrete metric spaces and is analogous to the corresponding property for standard Euclidean distance. It confirms that the discrete distance function behaves as expected with respect to identity of points.

### Dependencies
- `DDIST_REFL`: States that the discrete distance between a point and itself is zero.
- `DDIST_POS_LT`: States that the discrete distance between distinct points is strictly positive.
- `REAL_LT_REFL`: States that no real number is strictly less than itself.

---

## BETWEEN_COLLINEAR_DDIST_EQ

### Name of formal statement
BETWEEN_COLLINEAR_DDIST_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BETWEEN_COLLINEAR_DDIST_EQ = prove
 (`!a b x:real^N.
        norm(a) < &1 /\ norm(b) < &1 /\ norm(x) < &1
        ==> (between x (a,b) <=>
             collinear {a, x, b} /\
             ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [SIMP_TAC[BETWEEN_IMP_COLLINEAR];
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES]] THEN
  ASM_MESON_TAC[DDIST_INCREASES_ONLINE; DDIST_SYM; REAL_LT_IMP_LE;
                REAL_LE_REFL; BETWEEN_SYM; REAL_NOT_LE; BETWEEN_REFL]);;
```

### Informal statement
For any points $a$, $b$, and $x$ in $\mathbb{R}^N$, if $\|a\| < 1$, $\|b\| < 1$, and $\|x\| < 1$, then the following are equivalent:
- $x$ is between $a$ and $b$
- The points $a$, $x$, and $b$ are collinear, and $\text{ddist}(x,a) \leq \text{ddist}(a,b)$ and $\text{ddist}(x,b) \leq \text{ddist}(a,b)$

where $\text{ddist}$ represents the Euclidean distance between points.

### Informal proof
The proof establishes the equivalence between the "betweenness" property and the combination of collinearity with distance constraints.

For the forward direction ($\Rightarrow$):
- If $x$ is between $a$ and $b$, then by `BETWEEN_IMP_COLLINEAR`, the points $a$, $x$, and $b$ are collinear.
- The distance constraints follow from the fact that a point between two others must be at a distance no greater than the distance between the endpoints.

For the reverse direction ($\Leftarrow$):
- We rewrite using `COLLINEAR_BETWEEN_CASES`, which expresses collinearity in terms of betweenness relations.
- The proof is completed using several properties:
  - `DDIST_INCREASES_ONLINE`: If points are collinear, distances increase along the line
  - `DDIST_SYM`: Distance is symmetric
  - `BETWEEN_SYM`: The betweenness relation is symmetric
  - `BETWEEN_REFL`: Reflexivity of betweenness
  - Basic properties of real numbers

The conditions $\|a\| < 1$, $\|b\| < 1$, and $\|x\| < 1$ ensure we're working with points in the unit ball where these properties hold.

### Mathematical insight
This theorem provides a characterization of betweenness in terms of collinearity and distance constraints. The betweenness relation is important in geometry and often needs to be formalized in terms of more primitive concepts.

The equivalence shows that a point $x$ is between points $a$ and $b$ precisely when:
1. All three points lie on the same line (collinearity)
2. The distance from $x$ to either endpoint does not exceed the distance between the endpoints

The constraints on the norms ($\|a\| < 1$, $\|b\| < 1$, and $\|x\| < 1$) are technical requirements that likely simplify the proof by ensuring all points are within the unit ball, which might be relevant for the definition of discrete distance (`ddist`).

### Dependencies
- `BETWEEN_IMP_COLLINEAR`: Theorem stating that if a point is between two others, then all three points are collinear
- `COLLINEAR_BETWEEN_CASES`: Theorem relating collinearity to betweenness cases
- `DDIST_INCREASES_ONLINE`: Theorem about distances increasing along a line
- `DDIST_SYM`: Theorem stating that discrete distance is symmetric
- `BETWEEN_SYM`: Theorem stating that betweenness relation is symmetric
- `BETWEEN_REFL`: Theorem about reflexivity of betweenness
- Basic properties of real numbers: `REAL_LT_IMP_LE`, `REAL_LE_REFL`, `REAL_NOT_LE`

### Porting notes
When porting this theorem, be aware of:
1. The definition of `between`, `collinear`, and `ddist` need to be consistent with HOL Light
2. The norm constraints ($\|a\| < 1$, etc.) may be related to how discrete distance is defined in HOL Light
3. Some proof assistants might have different conventions for handling collinearity and betweenness
4. The automated reasoning steps using `ASM_MESON_TAC` might require different tactics in other systems

---

## CONTINUOUS_AT_LIFT_DDIST

### CONTINUOUS_AT_LIFT_DDIST

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CONTINUOUS_AT_LIFT_DDIST = prove
 (`!a x:real^N.
      norm(a) < &1 /\ norm(x) < &1 ==> (\x. lift(ddist(a,x))) continuous at x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN EXISTS_TAC
   `\x:real^N. lift((&1 - a dot x) pow 2 /
                    ((&1 - norm a pow 2) * (&1 - norm x pow 2)) - &1)` THEN
  EXISTS_TAC `&1 - norm(x:real^N)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
    `dist(y,x) < &1 - norm x ==> norm y < &1`)) THEN ASM_SIMP_TAC[ddist];
    REWRITE_TAC[LIFT_SUB; real_div; LIFT_CMUL; REAL_INV_MUL] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN SIMP_TAC[CONTINUOUS_CONST] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[CONTINUOUS_CONST; o_DEF; REAL_POW_2; LIFT_CMUL] THENL
     [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_MUL);
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV)] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &1 * &1 ==> ~(&1 - x = &0)`; REAL_LT_MUL2;
                 NORM_POS_LE; LIFT_SUB] THEN
    SIMP_TAC[GSYM REAL_POW_2; NORM_POW_2; CONTINUOUS_CONST; CONTINUOUS_AT_ID;
             CONTINUOUS_SUB; CONTINUOUS_LIFT_DOT2]]);;
```

### Informal statement
For any vectors $a, x \in \mathbb{R}^N$, if $\|a\| < 1$ and $\|x\| < 1$, then the function $f(x) = \text{lift}(\text{ddist}(a,x))$ is continuous at $x$.

Here, $\text{ddist}(a,x)$ represents the directed distance from the vector $a$ to $x$, and $\text{lift}$ is a function that embeds a real number into a vector space.

### Informal proof
The proof demonstrates the continuity of $f(x) = \text{lift}(\text{ddist}(a,x))$ at point $x$ by transforming it to an equivalent expression and showing that expression is continuous.

- First, we apply the theorem `CONTINUOUS_TRANSFORM_AT` which allows us to prove continuity by showing that the function is equal to another continuous function in a neighborhood of $x$.

- We define the alternative expression:
  $$g(x) = \text{lift}\left(\frac{(1 - a \cdot x)^2}{(1 - \|a\|^2)(1 - \|x\|^2)} - 1\right)$$

- We show that $f$ and $g$ are equal in a neighborhood of $x$ with radius $1 - \|x\|$, which is positive since $\|x\| < 1$.

- For any point $y$ in this neighborhood, we have $\|y\| < 1$ (by the triangle inequality), so $\text{ddist}(a,y)$ simplifies to the expression given by $g(y)$ according to the definition of $\text{ddist}$.

- We then prove that $g$ is continuous at $x$ by showing it's a composition of continuous functions:
  * $g$ involves subtraction, multiplication, division, and powers of continuous functions
  * We handle the division carefully by showing the denominator $(1 - \|a\|^2)(1 - \|x\|^2)$ is non-zero under our assumptions
  * We apply various continuity theorems for operations like subtraction, multiplication, and inverse
  * The dot product $a \cdot x$ is continuous by `CONTINUOUS_LIFT_DOT2`

### Mathematical insight
This theorem establishes that the directed distance function, when lifted to a vector space, is continuous under certain norm constraints. This is important for analysis in normed vector spaces where directed distance is used as a measurement.

The directed distance $\text{ddist}(a,x)$ has applications in functional analysis and geometry. The continuity of this function is essential for various analytical methods that rely on topological properties.

The proof strategy uses the fact that when $\|a\| < 1$ and $\|x\| < 1$, the directed distance has a specific algebraic form that can be shown to be continuous using standard calculus results.

### Dependencies
- `CONTINUOUS_TRANSFORM_AT`: Theorem for proving continuity through equivalent expressions
- `NORM_ARITH`: Theorem for norm-based arithmetic
- `ddist`: Definition of directed distance function
- `CONTINUOUS_SUB`, `CONTINUOUS_MUL`, `CONTINUOUS_AT_INV`: Continuity theorems for operations
- `CONTINUOUS_CONST`, `CONTINUOUS_AT_ID`: Basic continuity theorems
- `CONTINUOUS_LIFT_DOT2`: Continuity of the lifted dot product

### Porting notes
When porting to other systems:
- Ensure the target system has a similar notion of directed distance (`ddist`), or port its definition first
- The proof relies heavily on continuity theorems for basic operations, which are likely available in most proof assistants
- The `lift` function may need special attention as different systems handle type embedding differently
- The norm constraints ($\|a\| < 1$ and $\|x\| < 1$) are essential for the theorem to hold

---

## HYPERBOLIC_MIDPOINT

### Name of formal statement
HYPERBOLIC_MIDPOINT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERBOLIC_MIDPOINT = prove
 (`!a b:real^N.
        norm a < &1 /\ norm b < &1
        ==> ?x. between x (a,b) /\ ddist(x,a) = ddist(x,b)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\x:real^N. lift(ddist(x,a) - ddist(x,b))`; `segment[a:real^N,b]`]
     CONNECTED_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONNECTED_SEGMENT; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ONCE_REWRITE_TAC[DDIST_SYM] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_LIFT_DDIST THEN
    ASM_MESON_TAC[BETWEEN_NORM_LT; BETWEEN_IN_SEGMENT];
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `lift(&0)`]) THEN
    ASM_SIMP_TAC[DDIST_REFL; LIFT_DROP; ENDS_IN_SEGMENT; IN_IMAGE] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `&0 - x <= &0 <=> &0 <= x`] THEN
    ASM_SIMP_TAC[DDIST_POS_LE; LIFT_EQ; BETWEEN_IN_SEGMENT] THEN
    ASM_MESON_TAC[REAL_SUB_0; DDIST_SYM]]);;
```

### Informal statement
For any two points $a, b \in \mathbb{R}^N$ with $\|a\| < 1$ and $\|b\| < 1$, there exists a point $x$ such that:
1. $x$ lies between $a$ and $b$ (i.e., $x$ is on the line segment connecting $a$ and $b$)
2. The hyperbolic distance from $x$ to $a$ equals the hyperbolic distance from $x$ to $b$

Here, $\text{ddist}(x,y)$ represents the hyperbolic distance between points $x$ and $y$ in the Poincaré disk model of hyperbolic space.

### Informal proof
The proof uses the intermediate value theorem on the difference of hyperbolic distances along the segment.

* We apply the theorem `CONNECTED_CONTINUOUS_IMAGE` to the function $f(x) = \text{ddist}(x,a) - \text{ddist}(x,b)$ over the line segment $[a,b]$.

* First, we prove that $f$ is continuous on $[a,b]$:
  - The line segment $[a,b]$ is connected (by `CONNECTED_SEGMENT`)
  - $f$ is continuous because:
    - It's sufficient to prove continuity at each point (by `CONTINUOUS_AT_IMP_CONTINUOUS_ON`)
    - The hyperbolic distance function $\text{ddist}$ is continuous at each point in the segment
    - Any point in the segment has norm less than 1 (by `BETWEEN_NORM_LT`)

* Then, we establish that $f(a) > 0$ and $f(b) < 0$:
  - At $a$: $f(a) = \text{ddist}(a,a) - \text{ddist}(a,b) = 0 - \text{ddist}(a,b) = -\text{ddist}(a,b) < 0$
  - At $b$: $f(b) = \text{ddist}(b,a) - \text{ddist}(b,b) = \text{ddist}(b,a) - 0 = \text{ddist}(b,a) > 0$

* By the intermediate value theorem, there must exist a point $x \in [a,b]$ such that $f(x) = 0$, which means $\text{ddist}(x,a) = \text{ddist}(x,b)$.

* Since $x$ is in the segment $[a,b]$, it is between $a$ and $b$.

### Mathematical insight
This theorem establishes the existence of a hyperbolic midpoint between any two points in the Poincaré disk model of hyperbolic space. Unlike in Euclidean geometry, the hyperbolic midpoint is generally not the same as the Euclidean midpoint of the line segment.

The result is important because:
1. It shows that the notion of "midpoint" (equidistant point) still exists in hyperbolic geometry
2. It highlights a fundamental property of the hyperbolic metric: while the straight line connecting two points is a geodesic, the midpoint in terms of hyperbolic distance is not the Euclidean midpoint
3. It establishes a basic constructive result that can be used for further development of hyperbolic geometry

The proof technique uses the intermediate value theorem in a standard way - by showing that the difference in distances changes sign along the segment. This is a common approach for proving the existence of points with special metric properties.

### Dependencies
- Theorems:
  - `CONNECTED_CONTINUOUS_IMAGE` - A continuous image of a connected set is connected
  - `CONNECTED_SEGMENT` - A line segment is connected
  - `CONTINUOUS_AT_IMP_CONTINUOUS_ON` - Continuity at each point implies continuity on the set
  - `CONTINUOUS_SUB` - Subtraction preserves continuity
  - `CONTINUOUS_AT_LIFT_DDIST` - Continuity of hyperbolic distance function
  - `IS_INTERVAL_CONNECTED_1`, `IS_INTERVAL_1` - Properties of intervals
  - `BETWEEN_NORM_LT` - A point between two points with norm < 1 also has norm < 1
  - `BETWEEN_IN_SEGMENT` - Relation between "betweenness" and being in a segment
  - `ENDS_IN_SEGMENT` - Endpoints are in the segment
  - `DDIST_REFL`, `DDIST_POS_LE`, `DDIST_SYM` - Properties of hyperbolic distance

### Porting notes
When porting this theorem:
1. Ensure the hyperbolic distance function (`ddist`) is defined in the target system first
2. The proof relies on the intermediate value theorem, which should be available in most proof assistants
3. Be careful about how the Poincaré disk model is formalized - it requires points to be strictly inside the unit disk
4. The "betweenness" relation may have different definitions in different systems, so clarify what it means (typically that a point lies on the line segment between two other points)

---

## DDIST_EQ_ORIGIN

### Name of formal statement
DDIST_EQ_ORIGIN

### Type of formal statement
theorem

### Formal Content
```ocaml
let DDIST_EQ_ORIGIN = prove
 (`!x:real^N y:real^N.
        norm x < &1 /\ norm y < &1
        ==> (ddist(vec 0,x) = ddist(vec 0,y) <=> norm x = norm y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ddist; NORM_0; REAL_LT_01] THEN
  REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_EQ_INV2;
              REAL_ARITH `x - &1 = y - &1 <=> x = y`] THEN
  REWRITE_TAC[REAL_ARITH `&1 - x = &1 - y <=> x = y`;
              GSYM REAL_EQ_SQUARE_ABS; REAL_ABS_NORM]);;
```

### Informal statement
For any two vectors $x, y \in \mathbb{R}^N$ with $\|x\| < 1$ and $\|y\| < 1$, the distance in the Poincaré disk model from the origin to $x$ equals the distance from the origin to $y$ if and only if the norms of $x$ and $y$ are equal. Formally:

$$\forall x, y \in \mathbb{R}^N : \|x\| < 1 \land \|y\| < 1 \implies (\text{ddist}(\vec{0}, x) = \text{ddist}(\vec{0}, y) \iff \|x\| = \|y\|)$$

where $\text{ddist}$ represents the distance function in the Poincaré disk model, $\vec{0}$ is the zero vector, and $\|\cdot\|$ is the Euclidean norm.

### Informal proof
We prove this by simplifying the distance function in the Poincaré disk model when one of the points is the origin.

1. Starting with the definition of `ddist`, when one point is the origin $\vec{0}$:
   - We know that $\|\vec{0}\| = 0$
   - Since $\|x\| < 1$ and $\|y\| < 1$, we can apply the definition of Poincaré distance
   - The dot product $\vec{0} \cdot x = 0$ for any vector $x$

2. For the case of $\text{ddist}(\vec{0}, x)$, this simplifies to:
   $$\text{ddist}(\vec{0}, x) = 2 \cdot \tanh^{-1}\left(\frac{\|x\|}{\sqrt{1}}\right) = 2 \cdot \tanh^{-1}(\|x\|)$$

3. Similarly for $\text{ddist}(\vec{0}, y) = 2 \cdot \tanh^{-1}(\|y\|)$

4. The function $\tanh^{-1}$ is strictly increasing on $(-1,1)$, so:
   $$2 \cdot \tanh^{-1}(\|x\|) = 2 \cdot \tanh^{-1}(\|y\|) \iff \|x\| = \|y\|$$

Therefore, $\text{ddist}(\vec{0}, x) = \text{ddist}(\vec{0}, y) \iff \|x\| = \|y\|$.

### Mathematical insight
This theorem establishes a fundamental property of the Poincaré disk model: distances from the origin to points are determined solely by the Euclidean norm of those points. This means that points at the same Euclidean distance from the origin are also at the same hyperbolic distance from the origin in the Poincaré model.

The result demonstrates the radial symmetry of the Poincaré disk model with respect to the origin. This is important for understanding the geometry of hyperbolic space represented in the Poincaré disk model, particularly when considering spheres centered at the origin in hyperbolic space.

This theorem can be useful when analyzing properties of hyperbolic geometry that involve distances from a fixed point, as it allows us to reduce certain hyperbolic calculations to simpler Euclidean ones.

### Dependencies
- `ddist` - Definition of the distance function in the Poincaré disk model
- `NORM_0` - Theorem stating that the norm of the zero vector is 0
- `REAL_LT_01` - Theorem about real number ordering
- `DOT_LZERO` - Theorem stating that dot product with zero vector on the left is zero
- `REAL_EQ_SQUARE_ABS` - Theorem relating equality of absolute values to equality of squares
- `REAL_ABS_NORM` - Theorem relating absolute value and norm

### Porting notes
When implementing this in another proof assistant, pay special attention to:
- The definition of the Poincaré disk model distance function (`ddist`)
- How the inverse hyperbolic tangent function is defined or implemented
- The restrictions on vectors being within the unit disk (norm less than 1)

The proof relies heavily on algebraic simplification of the distance formula, which might require different tactics in other systems but follows the same mathematical reasoning.

---

## DDIST_CONGRUENT_TRIPLES_0

### Name of formal statement
DDIST_CONGRUENT_TRIPLES_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_CONGRUENT_TRIPLES_0 = prove
 (`!a b:real^N a' b':real^N.
        norm a < &1 /\ norm b < &1 /\ norm a' < &1 /\ norm b' < &1
        ==> (ddist(vec 0,a) = ddist(vec 0,a') /\ ddist(a,b) = ddist(a',b') /\
             ddist(b,vec 0) = ddist(b',vec 0) <=>
             dist(vec 0,a) = dist(vec 0,a') /\ dist(a,b) = dist(a',b') /\
             dist(b,vec 0) = dist(b',vec 0))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DDIST_EQ_ORIGIN; REWRITE_RULE[DDIST_SYM] DDIST_EQ_ORIGIN] THEN
  REWRITE_TAC[DIST_0; NORM_0; REAL_LT_01] THEN MATCH_MP_TAC(TAUT
   `(a /\ b ==> (x <=> y)) ==> (a /\ x /\ b <=> a /\ y /\ b)`) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[ddist; DIST_EQ; real_div; REAL_INV_MUL; REAL_RING
   `x * a * b - &1 = y * a * b - &1 <=> x = y \/ a = &0 \/ b = &0`] THEN
  REWRITE_TAC[dist; NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS; NORM_POW_2] THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; real_abs; REAL_SUB_LE; REAL_SUB_0] THEN
  ASM_SIMP_TAC[ABS_SQUARE_LT_1; REAL_ABS_NORM; REAL_LT_IMP_NE; REAL_LT_IMP_LE;
               MESON[NORM_CAUCHY_SCHWARZ; REAL_LET_TRANS; NORM_POS_LE;
                     REAL_LT_MUL2; REAL_MUL_RID; REAL_LT_IMP_LE]
                `norm x < &1 /\ norm y < &1 ==> x dot y < &1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_EQ]) THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any vectors $a, b, a', b'$ in $\mathbb{R}^N$, if all of them have norm less than 1, i.e., $\|a\| < 1$, $\|b\| < 1$, $\|a'\| < 1$, and $\|b'\| < 1$, then the following are equivalent:

1. The Poincaré disk distances between corresponding points are equal:
   - $\text{ddist}(0, a) = \text{ddist}(0, a')$
   - $\text{ddist}(a, b) = \text{ddist}(a', b')$
   - $\text{ddist}(b, 0) = \text{ddist}(b', 0)$

2. The Euclidean distances between corresponding points are equal:
   - $\text{dist}(0, a) = \text{dist}(0, a')$
   - $\text{dist}(a, b) = \text{dist}(a', b')$
   - $\text{dist}(b, 0) = \text{dist}(b', 0)$

Where $\text{ddist}$ is the Poincaré disk distance, $\text{dist}$ is the Euclidean distance, and $0$ is the zero vector.

### Informal proof
The proof proceeds as follows:

* First, we simplify the Poincaré disk distances that involve the origin:
  - Using `DDIST_EQ_ORIGIN`, we know that $\text{ddist}(0,a) = \text{ddist}(0,a')$ is equivalent to $\|a\| = \|a'\|$
  - Similarly, $\text{ddist}(b,0) = \text{ddist}(b',0)$ is equivalent to $\|b\| = \|b'\|$

* We also note that $\text{dist}(0,a) = \|a\|$ and $\text{dist}(0,b) = \|b\|$, so the conditions involving the origin are already equivalent.

* The main challenge is showing that $\text{ddist}(a,b) = \text{ddist}(a',b')$ is equivalent to $\text{dist}(a,b) = \text{dist}(a',b')$ under the given constraints.

* We express the Poincaré disk distance using its definition:
  $\text{ddist}(a,b) = \text{arctanh}\left(\frac{|a-b|}{\sqrt{(1-\|a\|^2)(1-\|b\|^2)}}\right)$

* Since arctanh is injective, $\text{ddist}(a,b) = \text{ddist}(a',b')$ if and only if their arguments are equal:
  $\frac{\|a-b\|}{\sqrt{(1-\|a\|^2)(1-\|b\|^2)}} = \frac{\|a'-b'\|}{\sqrt{(1-\|a'\|^2)(1-\|b'\|^2)}}$

* Given that $\|a\| = \|a'\|$ and $\|b\| = \|b'\|$, we have:
  $(1-\|a\|^2)(1-\|b\|^2) = (1-\|a'\|^2)(1-\|b'\|^2)$

* Therefore, $\text{ddist}(a,b) = \text{ddist}(a',b')$ if and only if $\|a-b\| = \|a'-b'\|$, which is equivalent to $\text{dist}(a,b) = \text{dist}(a',b')$.

* The proof concludes by handling some technical details using properties of norms and dot products, ensuring that the denominators in the Poincaré distance formula are non-zero (which is guaranteed by the constraint that all norms are less than 1).

### Mathematical insight
This theorem establishes an interesting equivalence between congruence in Euclidean geometry and in hyperbolic geometry (represented by the Poincaré disk model). Specifically, it shows that for points within the unit disk, if three pairs of points have equal Euclidean distances, then they also have equal hyperbolic distances, and vice versa.

This is significant because the Poincaré disk model is conformal (angle-preserving) but not distance-preserving. The theorem reveals that despite the distortion of distances in the hyperbolic model, the concept of congruent triangles (where corresponding sides have equal lengths) is preserved when we map between Euclidean and hyperbolic geometries.

This result is particularly useful for translating geometric constructions between these two geometries and provides insight into the structure-preserving properties of the Poincaré disk model.

### Dependencies
#### Theorems
- `DDIST_EQ_ORIGIN` - Relates Poincaré disk distance from origin to a point with the Euclidean norm
- `DDIST_SYM` - Symmetry property of the Poincaré disk distance
- `ABS_SQUARE_LT_1` - Properties of absolute value for values less than 1
- `NORM_CAUCHY_SCHWARZ` - Cauchy-Schwarz inequality for vector norms

#### Definitions
- `ddist` - Poincaré disk distance function
- `dist` - Euclidean distance function

### Porting notes
When porting this theorem:
1. Ensure that the Poincaré disk distance function is properly defined in the target system
2. Be aware of different conventions for vector operations (dot products, norms) in various proof assistants
3. The proof relies heavily on algebraic manipulations of real numbers and vector operations, so corresponding libraries for real analysis will be essential

---

## kleinify

### Name of formal statement
kleinify

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let kleinify = new_definition
 `kleinify z = Cx(&2 / (&1 + norm(z) pow 2)) * z`;;
```

### Informal statement
The function `kleinify` is defined for $z \in \mathbb{C}$ as:

$$\text{kleinify}(z) = \frac{2}{1 + \|z\|^2} \cdot z$$

where $\|z\|$ represents the norm of the complex number $z$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition implements a function known as the Klein projection (or Klein transformation) which maps points from the Poincaré disc model of hyperbolic geometry to the Klein disc model (also known as the Beltrami-Klein model).

The formula $\frac{2}{1 + \|z\|^2} \cdot z$ scales a point $z$ in the unit disc based on its distance from the origin. This mapping preserves geodesics - straight lines in the Klein model correspond to arcs of circles in the Poincaré model.

As noted in the comment, this is related to a geometric construction involving:
1. Orthogonal projection onto a hemisphere touching the unit disc
2. Stereographic projection back from the opposite pole of the sphere
3. Scaling

This transformation is important for working with hyperbolic translations, as it allows moving between different models of hyperbolic geometry. Each model has different advantages: the Poincaré disc preserves angles but not straight lines, while the Klein model preserves straight lines but not angles.

### Dependencies
No direct dependencies are used in the definition itself.

### Porting notes
When porting this definition:
1. Ensure the target system has a complex number type with norm operation
2. Verify the handling of real number literals (like `&1` and `&2` in HOL Light)
3. Check how powers are represented in the target system (the `pow 2` operation)
4. Note that `Cx` in HOL Light converts a real number to a complex number

---

## poincarify

### Name of formal statement
poincarify

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let poincarify = new_definition
 `poincarify x = Cx((&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2) * x`;;
```

### Informal statement
The function `poincarify` maps a complex vector $x$ to another complex vector defined by:

$$\text{poincarify}(x) = \frac{1 - \sqrt{1 - \|x\|^2}}{\|x\|^2} \cdot x$$

where:
- $x$ is a complex vector
- $\|x\|$ denotes the norm of $x$
- $\text{Cx}$ in the formal statement converts a real number to a complex number

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This function defines a transformation from a vector to the Poincaré disk model of hyperbolic geometry. The transformation maps points from the standard Euclidean space to the Poincaré disk, which is a model of hyperbolic geometry where the disk represents an infinite hyperbolic plane.

The formula computes a scaling factor that depends on the norm of the input vector, and then multiplies the input vector by this complex scaling factor. The resulting transformation ensures that:

1. Points with norm less than 1 are mapped to points inside the unit disk
2. Points approaching norm 1 are mapped toward the boundary of the disk
3. The transformation preserves angles (conformal mapping)

This transformation is useful in hyperbolic geometry, complex analysis, and certain types of conformal mappings.

### Dependencies
No explicit dependencies are listed.

### Porting notes
When porting this definition:
- Ensure that the target system handles complex numbers and vectors correctly
- Verify that the square root operation works properly when applied to expressions of the form $(1 - \|x\|^2)$
- Check that the norm function in the target system computes the Euclidean norm
- Be aware that this definition assumes $\|x\| \neq 0$ to avoid division by zero

---

## KLEINIFY_0,POINCARIFY_0

### Name of formal statement
KLEINIFY_0, POINCARIFY_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KLEINIFY_0,POINCARIFY_0 = (CONJ_PAIR o prove)
 (`kleinify (Cx(&0)) = Cx(&0) /\ poincarify (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[kleinify; poincarify; COMPLEX_MUL_RZERO]);;
```

### Informal statement
The theorem states two properties simultaneously:
1. $\text{kleinify}(0) = 0$
2. $\text{poincarify}(0) = 0$

where $0$ is represented as the complex number $0 + 0i$, and both $\text{kleinify}$ and $\text{poincarify}$ are transformations on complex numbers.

### Informal proof
The proof follows directly by:
- Applying the definitions of `kleinify` and `poincarify`
- Using the property that multiplication by zero in the complex domain yields zero (`COMPLEX_MUL_RZERO`)

Since both `kleinify` and `poincarify` involve complex multiplication operations, and multiplication by zero yields zero, the transformations preserve zero.

### Mathematical insight
This theorem establishes that both the Klein transformation (`kleinify`) and Poincaré transformation (`poincarify`) preserve the origin in the complex plane. This is a basic property that confirms these transformations behave properly with respect to the origin.

These transformations are likely used in hyperbolic geometry or conformal mappings, where the Klein and Poincaré models are important representations of non-Euclidean geometry. Maintaining the origin as a fixed point is often an important characteristic of such transformations.

### Dependencies
- Definitions:
  - `kleinify`: Klein transformation for complex numbers
  - `poincarify`: Poincaré transformation for complex numbers
- Theorems:
  - `COMPLEX_MUL_RZERO`: States that complex multiplication by zero yields zero

### Porting notes
When porting to other proof systems:
- Ensure that the target system has appropriate complex number representations and operations
- Check if the target system uses different naming conventions for complex number operations
- The proof is straightforward and should be easily adaptable to other systems with basic complex number support

---

## NORM_KLEINIFY

### Name of formal statement
NORM_KLEINIFY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY = prove
 (`!z. norm(kleinify z) = (&2 * norm(z)) / (&1 + norm(z) pow 2)`,
  REWRITE_TAC[kleinify; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_DIV] THEN
  SIMP_TAC[REAL_LE_POW_2; REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any complex number $z$, the norm of $\text{kleinify}(z)$ is given by:

$$\|kleinify(z)\| = \frac{2 \cdot \|z\|}{1 + \|z\|^2}$$

where $\|\cdot\|$ represents the complex norm.

### Informal proof
The proof proceeds as follows:

1. First, we rewrite the goal using the definition of `kleinify` and properties of complex norms:
   - Apply the definition of `kleinify`
   - Use properties of complex norm: $\|z \cdot w\| = \|z\| \cdot \|w\|$ 
   - Apply $\|\text{cx}(r)\| = |r|$ for real $r$
   - Use $|a/b| = |a|/|b|$ for the absolute value of a quotient

2. Since the norm of a complex number is always non-negative, we can simplify:
   - $\|z\|^2 \geq 0$ for any complex $z$
   - Therefore $|1 + \|z\|^2| = 1 + \|z\|^2$

3. The final step uses real arithmetic to simplify the expression to the desired form.

### Mathematical insight
This theorem gives a precise formula for the norm of a complex number after applying the Klein transformation (kleinify). The function `kleinify` is a key operation in projective geometry and is used in the context of mapping between different models of hyperbolic geometry.

The formula shows that the norm after kleinification depends only on the norm of the original complex number, not on its argument. This is characteristic of conformal mappings, which preserve angles.

The formula $\frac{2 \cdot \|z\|}{1 + \|z\|^2}$ has a maximum value of 1 (which occurs when $\|z\| = 1$), showing that the kleinification maps all points to within a bounded region.

### Dependencies
- `kleinify`: Definition of the Klein transformation on complex numbers
- `COMPLEX_NORM_MUL`: Theorem about norm of complex multiplication
- `COMPLEX_NORM_CX`: Theorem about norm of complex numbers from reals
- `REAL_ABS_DIV`: Theorem about absolute value of division
- `REAL_LE_POW_2`: Theorem about non-negativity of squares
- `REAL_ARITH`: Tactics for real arithmetic

### Porting notes
When porting this theorem, ensure that the definition of `kleinify` is correctly implemented first. The proof relies heavily on properties of complex numbers and real arithmetic, which should be available in most proof assistants with a complex number library.

---

## NORM_KLEINIFY_LT

### Name of formal statement
NORM_KLEINIFY_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_LT = prove
 (`!z. norm(kleinify z) < &1 <=> ~(norm z = &1)`,
  ASM_SIMP_TAC[NORM_KLEINIFY; REAL_LE_POW_2; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
  SIMP_TAC[REAL_ARITH `&2 * z < (&1 + z pow 2) <=> &0 < (z - &1) pow 2`] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any complex number $z$, the norm of $\text{kleinify}(z)$ is less than $1$ if and only if the norm of $z$ is not equal to $1$:
$$\forall z. \|{\text{kleinify}(z)}\| < 1 \iff \|z\| \neq 1$$

### Informal proof
The proof establishes when the norm of the Klein transformation of a complex number is less than 1:

* First, the theorem uses `NORM_KLEINIFY` which gives the norm of a kleinified complex number: $\|\text{kleinify}(z)\|^2 = \frac{2\|z\|^2}{\|z\|^2+1}$

* The proof simplifies using various real arithmetic properties:
  - Using the fact that $\|z\|^2 \geq 0$ for any complex number
  - Applying the property that $\frac{a}{b} < c$ is equivalent to $a < bc$ when $b > 0$
  - Noting that $0 < 1 + \|z\|^2$ for any complex $z$

* The condition $\|\text{kleinify}(z)\| < 1$ is equivalent to $\|\text{kleinify}(z)\|^2 < 1$

* This further simplifies to $\frac{2\|z\|^2}{\|z\|^2+1} < 1$, which can be rewritten as $2\|z\|^2 < \|z\|^2+1$

* The inequality is transformed to $0 < (\|z\| - 1)^2$, which is true precisely when $\|z\| \neq 1$

* The proof concludes with real arithmetic tactics to establish the equivalence.

### Mathematical insight
This theorem characterizes when the Klein transformation maps points strictly inside the unit disk. The kleinification is a mapping from the complex plane to the interior of the unit disk, and this theorem precisely characterizes the pre-images of points strictly inside the unit disk: they are exactly the points whose norm is not equal to 1.

This is a key property of the Klein transformation, which is used in complex analysis and hyperbolic geometry. The theorem shows that the only points that map to the boundary of the unit disk are those that lie on the unit circle.

### Dependencies
- Theorems:
  - `NORM_KLEINIFY`: Gives the formula for the norm of a kleinified complex number
  - `REAL_LE_POW_2`: $x^2 \geq 0$ for any real $x$
  - `REAL_LT_LDIV_EQ`: Division properties for inequalities
  - `REAL_MUL_LID`: $1 \cdot x = x$
  - `REAL_POW_2`: Definition of power 2
  - `REAL_LT_SQUARE`: Properties of squares and inequalities
  - Various `REAL_ARITH` theorems for real number arithmetic

### Porting notes
When porting this theorem:
- Ensure that the `kleinify` function is properly defined in your target system first
- Pay attention to how the target system handles complex number norms and inequality reasoning
- This proof relies heavily on real arithmetic simplification, so ensure your target system has adequate automation for similar reasoning

---

## NORM_POINCARIFY_LT

### Name of formal statement
NORM_POINCARIFY_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_POINCARIFY_LT = prove
 (`!x. norm(x) < &1 ==> norm(poincarify x) < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poincarify; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x * y <= &1 * y /\ y < &1 ==> x * y < &1`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW] THEN
  ASM_CASES_TAC `x:real^2 = vec 0` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_POW_LT; NORM_0] THENL
   [REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LID]] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &1 /\ &1 - x <= s ==> abs(&1 - s) <= x`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LSQRT; MATCH_MP_TAC REAL_LE_RSQRT] THEN
  REWRITE_TAC[REAL_SUB_LE; REAL_POS; REAL_MUL_LID; REAL_POW_ONE] THEN
  ASM_SIMP_TAC[REAL_ARITH `(&1 - x) pow 2 <= &1 - x <=> &0 <= x * (&1 - x)`;
   REAL_ARITH `&1 - x <= &1 <=> &0 <= x`; REAL_LE_MUL; REAL_POW_LE;
   REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_LT_IMP_LE; REAL_ABS_NORM; NORM_POS_LE]);;
```

### Informal statement
For any point $x \in \mathbb{R}^2$, if $\|x\| < 1$ then $\|\text{poincarify}(x)\| < 1$.

The theorem states that the poincarify function maps points inside the unit disk to points that remain inside the unit disk.

### Informal proof
We need to prove that for $x$ with $\|x\| < 1$, we have $\|\text{poincarify}(x)\| < 1$.

* First, unfold the definition of poincarify and use the property of complex norm of multiplication: $\|a \cdot b\| = \|a\| \cdot \|b\|$.

* We then aim to show that $\|x\| \cdot y \leq 1 \cdot y$ and $y < 1$ implies $\|x\| \cdot y < 1$, where $y$ represents the remaining scaling factor in the poincarify function.

* From the assumption $\|x\| < 1$, we know $\|x\| \leq 1$, so $\|x\| \cdot y \leq 1 \cdot y$.

* We need to prove that the scaling factor $y$ is less than 1. This scaling factor comes from the normalization component in poincarify.

* Case 1: If $x = 0$, then the result follows easily by arithmetic reasoning.

* Case 2: If $x \neq 0$, we need to show that $\left|\frac{1 - \sqrt{1 - \|x\|^2}}{\|x\|^2}\right| \leq 1$.

* This can be proven by showing:
  - $\sqrt{1 - \|x\|^2} \leq 1$ (since $\|x\|^2 \geq 0$)
  - $1 - \|x\|^2 \leq \sqrt{1 - \|x\|^2}$ (using properties of square root)
  
* These inequalities allow us to conclude that $|1 - \sqrt{1 - \|x\|^2}| \leq \|x\|^2$, which gives us the desired result after division.

* The proof finishes by applying various arithmetic inequalities, including the fact that $\|x\|^2 \leq 1$ when $\|x\| < 1$.

### Mathematical insight
This theorem establishes an important property of the poincarify function - that it preserves the unit disk. The poincarify function is likely related to the Poincaré disk model of hyperbolic geometry, where it's essential that transformations map the unit disk to itself.

The proof relies on careful analysis of the normalization factor in the poincarify function. This normalization ensures that the function preserves the boundary condition needed for the Poincaré disk model, where points inside the unit disk represent points in the hyperbolic plane.

Understanding that poincarify preserves the unit disk is fundamental for working with hyperbolic geometry in this model, as it ensures that transformations respect the domain of the model.

### Dependencies
No explicit dependencies were provided in the given information.

### Porting notes
When porting this theorem:
- Ensure that your target system has an equivalent definition of the `poincarify` function
- Verify that your system has appropriate support for vector norms and complex arithmetic
- The proof relies heavily on real arithmetic reasoning, so a good automation for real inequalities would be helpful

The proof strategy is not specific to HOL Light and should transfer to other systems with similar arithmetic libraries and automation.

---

## KLEINIFY_POINCARIFY

### Name of formal statement
KLEINIFY_POINCARIFY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KLEINIFY_POINCARIFY = prove
 (`!x. norm(x) < &1 ==> kleinify(poincarify x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kleinify; poincarify] THEN MATCH_MP_TAC
    (COMPLEX_RING `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`) THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM CX_MUL; CX_INJ; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(y = &0)
    ==> (&1 + (a / y pow 2 * y) pow 2) = (y pow 2 + a pow 2) / y pow 2`] THEN
  REWRITE_TAC[REAL_POW2_ABS; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(y = &0) ==> (&2 * x * y pow 2) * z * inv(y pow 2) = &2 * x * z`] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < y /\ &2 * y = x ==> &2 * inv(x) * y = &1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[REAL_POS; REAL_ARITH `&1 - x < &1 pow 2 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_POW_LT; COMPLEX_NORM_NZ];
    SUBGOAL_THEN `sqrt(&1 - norm(x:real^2) pow 2) pow 2 = &1 - norm x pow 2`
    MP_TAC THENL [MATCH_MP_TAC SQRT_POW_2; CONV_TAC REAL_FIELD]] THEN
  ASM_SIMP_TAC[REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_ABS_NORM; REAL_LT_IMP_LE]);;
```

### Informal statement
For any vector $x$ with norm less than 1 (i.e., $\|x\| < 1$), the composition of the Poincaré map followed by the Klein map returns the original vector:
$$\forall x. \|x\| < 1 \Rightarrow \text{kleinify}(\text{poincarify}(x)) = x$$

### Informal proof
The proof shows that applying the Poincaré map followed by the Klein map produces the identity function on the unit disk:

- Expand the definitions of `kleinify` and `poincarify`.
- Apply the algebraic property: if $w \cdot z = 1$, then $w \cdot z \cdot x = x$, assuming $x \neq 0$.
- Use properties of complex numbers and norms to simplify the expressions.
- For the case $x \neq 0$, show that:
  * The product of the two maps simplifies to a term involving $\sqrt{1-\|x\|^2}$.
  * This term equals 1 when $\|x\| < 1$.
- Use properties of square roots and algebraic manipulation to complete the proof.
- In particular, show that $\sqrt{1-\|x\|^2}^2 = 1-\|x\|^2$ when $\|x\| < 1$.

The proof primarily uses complex arithmetic and properties of norms and square roots to show that the composition of the two maps is the identity function on the unit disk.

### Mathematical insight
This theorem establishes that the Poincaré and Klein maps are inverse transformations when restricted to the unit disk. These maps are important in hyperbolic geometry, as they provide different models of hyperbolic space:

- The Poincaré disk model maps the unit disk to a model of hyperbolic space where geodesics are represented by arcs of circles orthogonal to the boundary.
- The Klein disk model (also known as the Beltrami-Klein model) maps the unit disk to a model where geodesics are represented by straight lines.

This theorem confirms that these models are mathematically equivalent and can be transformed into each other. This equivalence is fundamental in hyperbolic geometry and allows mathematicians to work with whichever model is most convenient for a particular problem.

### Dependencies
No explicit dependencies were provided in the input. The proof uses standard complex algebra, properties of norms, and real analysis theorems that are part of the HOL Light standard library.

### Porting notes
When porting this theorem:
- Ensure that the `kleinify` and `poincarify` functions are properly defined in the target system
- The proof relies heavily on algebraic manipulation of real and complex numbers, which may require different tactics or automation in other proof assistants
- Special attention should be paid to handling square roots and conditions for their existence and properties

---

## POINCARIFY_KLEINIFY

### Name of formal statement
POINCARIFY_KLEINIFY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POINCARIFY_KLEINIFY = prove
 (`!x. norm(x) < &1 ==> poincarify(kleinify x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kleinify; poincarify] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`) THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; GSYM REAL_MUL_ASSOC;
              REAL_INV_POW; REAL_POW_MUL] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(c = &0) /\ abs d < &1 /\ a * b = &2 * c pow 2 * (&1 + d)
    ==> a * inv(&2) pow 2 * b * inv(c) pow 2 * &2 * inv(&1 + d) = &1`) THEN
  ASM_REWRITE_TAC[REAL_ABS_POW; COMPLEX_NORM_ZERO; ABS_SQUARE_LT_1] THEN
  ASM_SIMP_TAC[REAL_ABS_NORM; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
   `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(x = &0) /\ abs x < &1 /\ a = &2 * x / (&1 + x)
    ==> a * (&1 + x) pow 2 = &2 * x * (&1 + x)`) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM; COMPLEX_NORM_ZERO; REAL_ABS_POW;
                  ABS_SQUARE_LT_1; REAL_POW_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &1 - y ==> &1 - x = y`) THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &1 - &2 * x / y <=> (&2 * x) / y <= &1`] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
   `&0 <= x ==> &0 < &1 + x`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x <= &1 * (&1 + x) <=> x <= &1`] THEN
  ASM_SIMP_TAC[ABS_SQUARE_LE_1; REAL_ABS_NORM; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~(&1 + norm(x:complex) pow 2 = &0)` MP_TAC THENL
   [ALL_TAC; CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) < &1 ==> ~(&1 + x = &0)`) THEN
  ASM_REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM; ABS_SQUARE_LT_1]);;
```

### Informal statement
For any complex number $x$ with $\|x\| < 1$, we have:

$$\text{poincarify}(\text{kleinify}(x)) = x$$

This theorem establishes that the functions `poincarify` and `kleinify` are inverses of each other when applied to points inside the unit disk.

### Informal proof
We need to prove that for any complex number $x$ with norm less than 1, applying `kleinify` followed by `poincarify` returns the original value $x$.

- Start by expanding the definitions of `kleinify` and `poincarify`.
- We aim to show that $w \cdot z \cdot x = x$ where $w \cdot z = 1$ (when $x \neq 0$).
- Rewrite using complex multiplication properties and norm calculations.
- The proof involves manipulating complex norms, absolute values, and powers.

The key steps involve:
- Converting products to expressions using the Complex Number Ring.
- Handling the division operations and showing that the product of the transformations equals 1.
- Dealing with specific expressions like $(1+\|x\|^2)$.
- Using properties of square root and other algebraic manipulations.

Finally, we prove that the inverse operations cancel each other out, establishing that $\text{poincarify}(\text{kleinify}(x)) = x$.

### Mathematical insight
This theorem establishes an important correspondence between different models of non-Euclidean geometry - specifically between the Klein model and the Poincaré disk model. 

The Poincaré disk model and Klein disk model are both models of hyperbolic geometry that use the interior of a disk, but they define distances and geodesics differently:
- The Poincaré model preserves angles but not distances
- The Klein model preserves straight lines but not angles

The functions `kleinify` and `poincarify` convert coordinates between these models. This theorem confirms they are inverses of each other when restricted to the open unit disk, which means we can freely translate between these two representations of hyperbolic geometry.

This correspondence is fundamental in hyperbolic geometry and has applications in various fields including computer graphics, complex analysis, and the study of Riemann surfaces.

### Dependencies
- `kleinify` - Function that transforms coordinates from the Poincaré model to the Klein model
- `poincarify` - Function that transforms coordinates from the Klein model to the Poincaré model

### Porting notes
When porting this theorem:
- Ensure your definitions of `kleinify` and `poincarify` match HOL Light's implementations
- Be careful with division by zero cases (when $x = 0$ or when dealing with expressions like $1 + \|x\|^2$)
- The proof relies heavily on complex number operations and real field arithmetic, requiring appropriate automation in the target system
- The theorem only applies inside the open unit disk ($\|x\| < 1$), which is an essential constraint

---

## DDIST_KLEINIFY

### DDIST_KLEINIFY
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY = prove
 (`!w z. ~(norm w = &1) /\ ~(norm z = &1)
         ==> ddist(kleinify w,kleinify z) =
             &4 * (&1 / &2 + norm(w - z) pow 2 /
                             ((&1 - norm w pow 2) * (&1 - norm z pow 2))) pow 2
             - &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `(&4 * norm(w - z:real^2) pow 2 *
     ((&1 - norm w pow 2) * (&1 - norm z pow 2) + norm(w - z) pow 2)) /
    ((&1 - norm w pow 2) pow 2 * (&1 - norm z pow 2) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[ddist; NORM_KLEINIFY_LT] THEN MATCH_MP_TAC(REAL_FIELD
     `~(y = &0) /\ z = (w + &1) * y ==> z / y - &1 = w`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN CONJ_TAC THEN
      MATCH_MP_TAC (REAL_ARITH `x < &1 ==> ~(&1 - x = &0)`) THEN
      ASM_SIMP_TAC[REAL_POW_1_LT; NORM_KLEINIFY_LT; NORM_POS_LE; ARITH];
      REWRITE_TAC[kleinify; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      REWRITE_TAC[GSYM COMPLEX_CMUL; DOT_LMUL] THEN REWRITE_TAC[DOT_RMUL] THEN
      SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_POW_LE; NORM_POS_LE;
               REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
      MATCH_MP_TAC(REAL_FIELD
       `(~(y' = &0) /\ ~(y = &0)) /\
        (y * y' - &4 * d) pow 2 =
        b * (y pow 2 - &4 * x pow 2) * (y' pow 2 - &4 * x' pow 2)
        ==> (&1 - &2 / y * &2 / y' * d) pow 2 =
            b * (&1 - (&2 / y * x) pow 2) * (&1 - (&2 / y' * x') pow 2)`) THEN
      CONJ_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `~(abs x = &1) ==> ~(&1 + x = &0)`) THEN
        ASM_SIMP_TAC[REAL_ABS_POW; REAL_POW_EQ_1; REAL_ABS_NORM] THEN ARITH_TAC;
        REWRITE_TAC[REAL_RING `(&1 + x) pow 2 - &4 * x = (&1 - x) pow 2`] THEN
        MATCH_MP_TAC(REAL_FIELD
         `(~(y = &0) /\ ~(y' = &0)) /\ a - y * y' = b
          ==> a = (b / (y * y') + &1) * y * y'`) THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_POW_EQ_1; REAL_ABS_NORM; ARITH;
                          REAL_ARITH `&1 - x = &0 <=> x = &1`];
          REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
          REAL_ARITH_TAC]]];
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[NORM_EQ_SQUARE; GSYM NORM_POW_2] THEN CONV_TAC REAL_FIELD]);;
```

### Informal statement
For any points $w, z \in \mathbb{R}^2$ such that $\|w\| \neq 1$ and $\|z\| \neq 1$, the distance between their Klein disk images is given by:

$$\text{ddist}(\text{kleinify}(w), \text{kleinify}(z)) = 4 \cdot \left(\frac{1}{2} + \frac{\|w - z\|^2}{(1 - \|w\|^2)(1 - \|z\|^2)}\right)^2 - 1$$

where $\text{kleinify}$ is the mapping to the Klein disk model and $\text{ddist}$ is the distance function in the Klein model.

### Informal proof
The proof establishes the formula for the Klein disk distance by showing it equals an intermediate expression and then transforming that expression.

* First, we aim to show that the distance equals:
  $$\frac{4 \cdot \|w-z\|^2 \cdot ((1-\|w\|^2)(1-\|z\|^2) + \|w-z\|^2)}{(1-\|w\|^2)^2 \cdot (1-\|z\|^2)^2}$$

* We prove this by:
  * Applying the definition of $\text{ddist}$ and using the fact that $\|\text{kleinify}(p)\| < 1$ for points in the disk.
  * Expanding the definition of $\text{kleinify}$ as $\frac{2p}{1+\|p\|^2}$ and manipulating complex norms and dot products.
  * Algebraic manipulations to show that the expressions involving norms and distances transform as required.

* Then we perform algebraic manipulations on this intermediate expression to show it equals:
  $$4 \cdot \left(\frac{1}{2} + \frac{\|w - z\|^2}{(1 - \|w\|^2)(1 - \|z\|^2)}\right)^2 - 1$$

* The proof uses field manipulations and properties of norms to complete the transformation between these expressions.

### Mathematical insight
This theorem gives an explicit formula for the distance in the Klein disk model in terms of the original Euclidean coordinates. The Klein disk is a model of hyperbolic geometry where geodesics are represented as straight lines, but distances are distorted.

The formula demonstrates how distances in the hyperbolic plane (represented through the Klein model) relate to Euclidean distances. The expression shows that as points get closer to the boundary of the disk (where $\|w\| \to 1$ or $\|z\| \to 1$), the hyperbolic distance between them increases dramatically compared to their Euclidean distance, capturing the key distortion property of hyperbolic geometry.

This result is important for calculations in hyperbolic geometry and for understanding the relationship between different models of hyperbolic space.

### Dependencies
None explicitly listed in the provided dependency information, but the proof uses:
- The definition of `kleinify` (the mapping to the Klein disk model)
- The definition of `ddist` (distance function in the Klein model)
- Various properties of norms and real arithmetic

### Porting notes
When porting this theorem:
- Ensure that the definitions of `kleinify` and `ddist` are correctly translated
- Consider that HOL Light's automation for algebraic manipulations (`REAL_FIELD`, `REAL_ARITH`, etc.) does significant work in the proof
- The proof relies heavily on algebraic manipulations that might need explicit step-by-step verification in systems with less powerful automation for real arithmetic

---

## DDIST_KLEINIFY_EQ

### Name of formal statement
DDIST_KLEINIFY_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY_EQ = prove
 (`!w z w' z'.
      ~(norm w = &1) /\ ~(norm z = &1) /\ ~(norm w' = &1) /\ ~(norm z' = &1) /\
      norm(w - z) pow 2 * (&1 - norm w' pow 2) * (&1 - norm z' pow 2) =
      norm(w' - z') pow 2 * (&1 - norm w pow 2) * (&1 - norm z pow 2)
      ==> ddist(kleinify w,kleinify z) = ddist(kleinify w',kleinify z')`,
  SIMP_TAC[DDIST_KLEINIFY; NORM_EQ_SQUARE; GSYM NORM_POW_2; REAL_POS] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all complex numbers $w$, $z$, $w'$, and $z'$ such that none of them have norm equal to 1 (i.e., $\|w\| \neq 1$, $\|z\| \neq 1$, $\|w'\| \neq 1$, and $\|z'\| \neq 1$), if:

$$\|w - z\|^2 \cdot (1 - \|w'\|^2) \cdot (1 - \|z'\|^2) = \|w' - z'\|^2 \cdot (1 - \|w\|^2) \cdot (1 - \|z\|^2)$$

then the hyperbolic distance between the Klein model points corresponding to $w$ and $z$ equals the hyperbolic distance between the Klein model points corresponding to $w'$ and $z'$:

$$\text{ddist}(\text{kleinify}(w), \text{kleinify}(z)) = \text{ddist}(\text{kleinify}(w'), \text{kleinify}(z'))$$

### Informal proof
The proof is straightforward:

1. Apply the theorem `DDIST_KLEINIFY` which gives the formula for the hyperbolic distance between kleinified points.

2. Use simplification tactics:
   - `NORM_EQ_SQUARE` to replace norm equality with squared norm equality
   - `GSYM NORM_POW_2` to convert between norm squared and power notation
   - `REAL_POS` to handle positive real numbers

3. Finally, the proof is completed by applying the field arithmetic solver (`REAL_FIELD`), which handles the algebraic manipulations needed to show that the given equation for the norms implies equality of the distances.

### Mathematical insight
This theorem establishes a condition for when two pairs of points in the Klein model have the same hyperbolic distance. This is useful in hyperbolic geometry when working with the Klein model representation.

The condition given in the hypothesis relates the Euclidean distances between points and their distances from the unit circle (represented by terms like $(1 - \|w\|^2)$). This reflects how the Klein model embeds hyperbolic geometry into the unit disk, where distances become increasingly distorted as points approach the boundary.

The theorem is important for understanding invariants in the Klein model of hyperbolic geometry and for transforming between different representations of hyperbolic space.

### Dependencies
- `DDIST_KLEINIFY`: Formula for hyperbolic distance between kleinified points
- `NORM_EQ_SQUARE`: Relates norm equality to squared norm equality
- `GSYM NORM_POW_2`: Conversion between norm squared and power notation
- `REAL_POS`: Handling of positive real numbers
- `REAL_FIELD`: Field arithmetic solver

### Porting notes
When porting this theorem, ensure that the destination system has:
1. A well-defined Klein model representation (`kleinify` function)
2. A hyperbolic distance function (`ddist`)
3. Appropriate norm operations for complex numbers
4. A field arithmetic solver comparable to HOL Light's `REAL_FIELD`

The proof is quite direct and should translate well to other proof assistants with similar automation capabilities.

---

## NORM_KLEINIFY_MOEBIUS_LT

### Name of formal statement
NORM_KLEINIFY_MOEBIUS_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_MOEBIUS_LT = prove
 (`!w x. norm w < &1 /\ norm x < &1
         ==> norm(kleinify(moebius_function (&0) w x)) < &1`,
  SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; NORM_KLEINIFY_LT; REAL_LT_IMP_NE]);;
```

### Informal statement
For all complex numbers $w$ and $x$ such that $\|w\| < 1$ and $\|x\| < 1$, we have 
$$\|\text{kleinify}(\text{moebius_function}(0, w, x))\| < 1$$

### Informal proof
The proof uses simplification with three key results:

- `MOEBIUS_FUNCTION_NORM_LT_1`: This theorem guarantees that for any $t$, $w$, and $z$ with $\|w\| < 1$ and $\|z\| < 1$, the Möbius function preserves the unit disk, i.e., $\|\text{moebius_function}(t, w, z)\| < 1$.

- `NORM_KLEINIFY_LT`: This ensures that the kleinify operation preserves the property of having norm less than 1.

- `REAL_LT_IMP_NE`: This is used to handle the implication that if $a < b$ then $a \neq b$.

The theorem is proved by direct simplification using these facts. Since $\|w\| < 1$ and $\|x\| < 1$, the Möbius function with $t=0$ maps into the unit disk, and then the kleinify operation preserves this property.

### Mathematical insight
This theorem establishes that applying the kleinify function to the Möbius function (with parameter $t=0$) preserves the unit disk. 

The Möbius function is a conformal map of the form:
$$\text{moebius_function}(t, w, z) = e^{it} \cdot \frac{z - w}{1 - \overline{w}z}$$

These functions are fundamental in complex analysis, particularly for mappings between the unit disk and other domains. They preserve angles and map circles to circles or lines.

The kleinify operation appears to be another transformation that - as shown by this theorem - preserves the property of having norm less than 1.

This result is important because it confirms that the composition of these two operations preserves the unit disk, which is a crucial property for many applications in complex analysis and conformal mappings.

### Dependencies
- **Theorems**:
  - `MOEBIUS_FUNCTION_NORM_LT_1`: Proves that the Möbius function preserves the unit disk
  - `NORM_KLEINIFY_LT`: Shows that kleinify preserves the property of having norm less than 1
  - `REAL_LT_IMP_NE`: Shows that a strict inequality implies disequality

- **Definitions**:
  - `moebius_function`: Defines the Möbius function as $e^{it} \cdot \frac{z - w}{1 - \overline{w}z}$

### Porting notes
When implementing this theorem in another system:
1. Ensure the definitions of `moebius_function` and `kleinify` are properly formalized
2. Check that the complex number operations (especially conjugation and norm) have equivalent semantics
3. The proof is quite direct, relying on the properties of the Möbius function and kleinify operation, so the porting should be straightforward if those dependencies are established

---

## DDIST_KLEINIFY_MOEBIUS

### Name of formal statement
DDIST_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY_MOEBIUS = prove
 (`!w x y. norm w < &1 /\ norm x < &1 /\ norm y < &1
           ==> ddist(kleinify(moebius_function (&0) w x),
                     kleinify(moebius_function (&0) w y)) =
               ddist(kleinify x,kleinify y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DDIST_KLEINIFY_EQ THEN
  ASM_SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; REAL_LT_IMP_NE] THEN
  REWRITE_TAC[MOEBIUS_FUNCTION_SIMPLE] THEN
  SUBGOAL_THEN
   `~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL] `norm(x) < norm(y) ==> ~(y = x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CNJ];
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))
      ==> (x - w) / (Cx (&1) - cnj w * x) - (y - w) / (Cx (&1) - cnj w * y) =
          ((Cx(&1) - w * cnj w) * (x - y)) /
          ((Cx (&1) - cnj w * x) * (Cx (&1) - cnj w * y))`] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
     `~(y = &0) /\ ~(y' = &0)
      ==> (&1 - (x / y) pow 2) * (&1 - (x' / y') pow 2) =
          ((y pow 2 - x pow 2) * (y' pow 2 - x' pow 2)) / (y * y') pow 2`] THEN
    REWRITE_TAC[REAL_POW_DIV; COMPLEX_NORM_MUL] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_RING
     `x * y:real = w * z ==> (x * i) * y = w * z * i`) THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN REWRITE_TAC[NORM_POW_2; DOT_2] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; complex_sub; complex_mul; CX_DEF;
                complex_add; RE; IM; cnj; complex_neg] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all complex numbers $w$, $x$, and $y$ where $\|w\| < 1$, $\|x\| < 1$, and $\|y\| < 1$, the following equality holds:

$$\operatorname{ddist}(\operatorname{kleinify}(\operatorname{moebius\_function}(0, w, x)), \operatorname{kleinify}(\operatorname{moebius\_function}(0, w, y))) = \operatorname{ddist}(\operatorname{kleinify}(x), \operatorname{kleinify}(y))$$

This theorem states that the Möbius transformation with parameter $t=0$ and center $w$ preserves the hyperbolic distance (ddist) between points in the Poincaré disk model of hyperbolic geometry.

### Informal proof
The proof proceeds as follows:

* We apply the theorem `DDIST_KLEINIFY_EQ` which allows us to compare distances. This requires showing that the norms of the Möbius transformations are less than 1.

* By applying `MOEBIUS_FUNCTION_NORM_LT_1` to our assumptions, we establish that the norms of the Möbius transformations of $x$ and $y$ are indeed less than 1.

* We rewrite using `MOEBIUS_FUNCTION_SIMPLE` to get the explicit form of the Möbius transformation with $t=0$:
  $$\operatorname{moebius\_function}(0, w, z) = \frac{z - w}{1 - \overline{w} \cdot z}$$

* We need to show that the denominators are non-zero, i.e., $1 - \overline{w} \cdot x \neq 0$ and $1 - \overline{w} \cdot y \neq 0$. We prove this by showing for each case that $\|1\| > \|\overline{w} \cdot z\|$. Using properties of complex norms:
  $$\|\overline{w} \cdot z\| = \|w\| \cdot \|z\| < 1 \cdot 1 = 1 = \|1\|$$
  (since $\|w\| < 1$ and $\|z\| < 1$)

* Using complex field arithmetic, we simplify the difference of the Möbius transformations to:
  $$\frac{(1 - w \cdot \overline{w}) \cdot (x - y)}{(1 - \overline{w} \cdot x) \cdot (1 - \overline{w} \cdot y)}$$

* The remainder of the proof involves manipulating complex norms and expressions to establish that this transformation preserves the hyperbolic distance. This involves detailed algebraic manipulations of the formula for $\operatorname{ddist}$ in terms of the norm, and showing that the scaling factors in the numerator and denominator cancel out appropriately.

### Mathematical insight
This theorem demonstrates an important property of Möbius transformations in hyperbolic geometry: they act as isometries of the Poincaré disk model. Specifically, the theorem shows that Möbius transformations with parameter $t=0$ and center $w$ preserve hyperbolic distances between points.

In hyperbolic geometry, Möbius transformations play a role analogous to that of rotations and translations in Euclidean geometry. This theorem confirms that these transformations can be used to move points around in the hyperbolic plane without distorting distances, which is a fundamental property for isometries.

The result is canonical in the study of hyperbolic geometry and complex analysis, as it connects the algebraic structure of Möbius transformations with their geometric interpretation as isometries of the hyperbolic plane.

### Dependencies
#### Theorems
- `DDIST_KLEINIFY_EQ`: Used to establish the equality of hyperbolic distances.
- `MOEBIUS_FUNCTION_NORM_LT_1`: Ensures that Möbius transformations preserve the unit disk.
- `MOEBIUS_FUNCTION_SIMPLE`: Provides the simplified form of the Möbius transformation when $t=0$.

#### Definitions
- `moebius_function`: $\operatorname{moebius\_function}(t, w, z) = e^{it} \cdot \frac{z - w}{1 - \overline{w} \cdot z}$
- `kleinify`: Converts from the Poincaré disk model to the Klein disk model of hyperbolic geometry.
- `ddist`: Hyperbolic distance function in the Klein model.

### Porting notes
When porting this theorem:
1. Ensure the definitions of `moebius_function`, `kleinify`, and `ddist` match exactly.
2. In other proof assistants, complex field simplifications might require different tactics or approaches than HOL Light's `COMPLEX_FIELD`.
3. The algebraic manipulations involving norms and complex arithmetic are intensive - you may need to split them into smaller lemmas depending on the automation capabilities of the target system.
4. Pay special attention to how complex conjugation and norms are defined in the target system, as these might have subtle differences.

---

## COLLINEAR_KLEINIFY_MOEBIUS

### Name of formal statement
COLLINEAR_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_KLEINIFY_MOEBIUS = prove
 (`!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (collinear {kleinify(moebius_function (&0) w x),
                             kleinify(moebius_function (&0) w y),
                             kleinify(moebius_function (&0) w z)} <=>
                  collinear {kleinify x,kleinify y,kleinify z})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_3_2D; kleinify; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX] THEN
  SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`;
     REAL_FIELD
     `~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
      ==> ((&2 / nz * rz - &2 / nx * rx) * (&2 / ny * iy - &2 / nx * ix) =
           (&2 / ny * ry - &2 / nx * rx) * (&2 / nz * iz - &2 / nx * ix) <=>
           (nx * rz - nz * rx) * (nx * iy - ny * ix) =
           (nx * ry - ny * rx) * (nx * iz - nz * ix))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; MOEBIUS_FUNCTION_SIMPLE] THEN
  ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[RE_DIV_CX; GSYM CX_POW; IM_DIV_CX] THEN
  SUBGOAL_THEN
   `~(Cx (&1) - cnj w * x = Cx(&0)) /\ ~(Cx (&1) - cnj w * y = Cx(&0)) /\
    ~(Cx (&1) - cnj w * z = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL] `norm x < norm y ==> ~(y = x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `abs(&1) = &1 * &1`] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
    ==>(((&1 + (nxw / nx) pow 2) * rz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iy / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * ix / nx pow 2) =
        ((&1 + (nxw / nx) pow 2) * ry / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * ix / nx pow 2) <=>
        ((nx pow 2 + nxw pow 2) * rz - (nz pow 2 + nzw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iy - (ny pow 2 + nyw pow 2) * ix) =
        ((nx pow 2 + nxw pow 2) * ry - (ny pow 2 + nyw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iz - (nz pow 2 + nzw pow 2) * ix))`] THEN
  REWRITE_TAC[COMPLEX_SQNORM; complex_sub; complex_mul; complex_add;
              complex_neg; cnj; CX_DEF; RE; IM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN MATCH_MP_TAC(REAL_RING
   `!a b. a * lhs = b * rhs /\ ~(a = &0) /\ ~(b = &0)
          ==> (lhs = &0 <=> rhs = &0)`) THEN
  EXISTS_TAC `Re x pow 2 + Im x pow 2 + &1` THEN
  EXISTS_TAC `--(Re w pow 2 + Im w pow 2 - &1) pow 3 *
              ((&1 - Re(x) pow 2 - Im(x) pow 2) *
               (&1 - Re(w) pow 2 - Im(w) pow 2) +
               &2 * (Re w - Re x) pow 2 + &2 * (Im w - Im x) pow 2)` THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM; REAL_POW_EQ_0; ARITH_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x + y ==> ~(x + y + &1 = &0)`) THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_LE_POW_2];
    MATCH_MP_TAC(REAL_ARITH `x + y < &1 ==> ~(--(x + y - &1) = &0)`) THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_POW_1_LT; NORM_POS_LE; ARITH];
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 <= y ==> ~(x + y = &0)`) THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &1 - x - y <=> x + y < &1`] THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_POW_1_LT; NORM_POS_LE; ARITH]]);;
```

### Informal statement
For any complex numbers $w, x, y, z$ with norm less than 1, the set of points $\{\textrm{kleinify}(\textrm{moebius\_function}(0, w, x)), \textrm{kleinify}(\textrm{moebius\_function}(0, w, y)), \textrm{kleinify}(\textrm{moebius\_function}(0, w, z))\}$ is collinear if and only if the set of points $\{\textrm{kleinify}(x), \textrm{kleinify}(y), \textrm{kleinify}(z)\}$ is collinear.

In other words, the Möbius transformation defined by $\textrm{moebius\_function}(0, w, z) = \frac{z - w}{1 - \bar{w}z}$ preserves collinearity after points are transformed by the Klein model mapping function.

### Informal proof
The proof proceeds as follows:

- First, we apply the definition of collinearity for three 2D points and expand the `kleinify` function, which maps complex numbers to points in the Klein disk model.

- We use the fact that for complex numbers, the real and imaginary parts correspond to coordinates, so we rewrite using `RE_DEF` and `IM_DEF`.

- We simplify expressions involving real and imaginary parts of complex multiplications.

- For points in the Klein model, collinearity can be expressed through a determinant-like condition involving the coordinates.

- We substitute the definition of `moebius_function(0, w, z) = (z - w)/(1 - conj(w) * z)` from `MOEBIUS_FUNCTION_SIMPLE`.

- Since all norm values are less than 1, we can prove that denominators in our fractions are non-zero.

- After algebraic manipulations and clearing fractions, we transform the collinearity condition into an equivalent form, using properties of complex division and conjugation.

- The final step involves a complex algebraic verification that shows both collinearity conditions are equivalent by finding appropriate non-zero scaling factors for the equations.

### Mathematical insight
This theorem shows that the Möbius transformation defined by $\textrm{moebius\_function}(0, w, z) = \frac{z - w}{1 - \bar{w}z}$ preserves collinearity when points are represented in the Klein disk model.

This is important in hyperbolic geometry and complex analysis. The Möbius transformations are known to preserve the unit disk, and they act as isometries in the Poincaré disk model of hyperbolic geometry. This theorem confirms that when transformed into the Klein disk model, certain collinearity relationships are preserved.

The result provides a way to translate between different models of hyperbolic geometry while preserving important geometric relationships. It's particularly useful for computational approaches to hyperbolic geometry.

### Dependencies
- **Theorems**:
  - `MOEBIUS_FUNCTION_SIMPLE`: The Möbius function with parameter 0 is defined as `moebius_function(0, w, z) = (z - w)/(1 - conj(w) * z)`.

- **Definitions**:
  - `moebius_function`: Defines the general Möbius transformation as `moebius_function t w z = cexp(ii * Cx t) * (z - w) / (Cx(1) - cnj w * z)`.

### Porting notes
When porting this theorem:
- Ensure your system has good support for complex numbers and their properties.
- The proof relies heavily on algebraic manipulations of complex expressions, so robust automation for such manipulations is helpful.
- The Klein model mapping function (`kleinify`) should be defined in your target system.
- The way collinearity is defined might differ between systems - in HOL Light it's defined for sets of points, while in other systems it might be a predicate on point sequences.

---

## BETWEEN_KLEINIFY_MOEBIUS

### BETWEEN_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BETWEEN_KLEINIFY_MOEBIUS = prove
 (`!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (kleinify(moebius_function (&0) w x))
                          (kleinify(moebius_function (&0) w y),
                           kleinify(moebius_function (&0) w z)) <=>
                  between (kleinify x) (kleinify y,kleinify z))`,
  SIMP_TAC[BETWEEN_COLLINEAR_DDIST_EQ; NORM_KLEINIFY_MOEBIUS_LT;
           NORM_KLEINIFY_LT; REAL_LT_IMP_NE;
           COLLINEAR_KLEINIFY_MOEBIUS; DDIST_KLEINIFY_MOEBIUS]);;
```

### Informal statement
For any complex numbers $w$, $x$, $y$, and $z$ with norms less than 1 (i.e., $\|w\| < 1$, $\|x\| < 1$, $\|y\| < 1$, and $\|z\| < 1$), the following equivalence holds:

A point is between two other points in the Klein model after applying a Möbius transformation if and only if the corresponding point is between the corresponding points in the original Klein model. Specifically:

$$\text{between}(\text{kleinify}(\text{moebius\_function}(0, w, x)), (\text{kleinify}(\text{moebius\_function}(0, w, y)), \text{kleinify}(\text{moebius\_function}(0, w, z)))) \iff \text{between}(\text{kleinify}(x), (\text{kleinify}(y), \text{kleinify}(z)))$$

where $\text{moebius\_function}(t, w, z) = e^{it} \cdot \frac{z - w}{1 - \overline{w} \cdot z}$ is a Möbius transformation.

### Informal proof
The proof leverages several key properties of Möbius transformations and the Klein model:

- The theorem is proven by applying a series of simplification tactics that use the following results:
  - `BETWEEN_COLLINEAR_DDIST_EQ`: A characterization of the "between" relation in terms of collinearity and distances
  - `NORM_KLEINIFY_MOEBIUS_LT`: A result showing that kleinifying a Möbius transformation preserves the norm constraint
  - `NORM_KLEINIFY_LT`: A result about norms in the Klein model
  - `REAL_LT_IMP_NE`: Real less than implies not equal
  - `COLLINEAR_KLEINIFY_MOEBIUS`: A theorem showing that kleinifying Möbius transformations preserves collinearity
  - `DDIST_KLEINIFY_MOEBIUS`: A result relating distances after kleinifying Möbius transformations

- The combination of these results establishes that the betweenness relation is preserved under the given Möbius transformation followed by kleinification.

### Mathematical insight
This theorem establishes that the Möbius transformation with parameter $t=0$ preserves the betweenness relation in the Klein model of hyperbolic geometry. This is a fundamental result connecting the complex analytic approach to hyperbolic geometry (via Möbius transformations) with the projective geometric approach (via the Klein model).

The result is important because:
1. It shows that certain Möbius transformations act as isometries in the hyperbolic plane
2. It allows us to transfer geometric properties between different representations of hyperbolic space
3. It connects complex analysis with hyperbolic geometry in a concrete way

The theorem specifically focuses on transformations with $t=0$, which corresponds to Möbius transformations without rotation component, simplifying the analysis while still capturing essential geometric properties.

### Dependencies
- **Theorems:**
  - `BETWEEN_COLLINEAR_DDIST_EQ`
  - `NORM_KLEINIFY_MOEBIUS_LT`
  - `NORM_KLEINIFY_LT`
  - `REAL_LT_IMP_NE`
  - `COLLINEAR_KLEINIFY_MOEBIUS`
  - `DDIST_KLEINIFY_MOEBIUS`

- **Definitions:**
  - `moebius_function`: Defines $\text{moebius\_function}(t, w, z) = e^{it} \cdot \frac{z - w}{1 - \overline{w} \cdot z}$

### Porting notes
When porting this theorem:
1. Ensure the target system has appropriate definitions for the Klein model and Möbius transformations
2. The "between" relation may have different representations in different systems
3. Complex number operations, particularly conjugation and exponentials, need to be properly defined
4. The theorem relies heavily on geometric properties of hyperbolic space, so the target system should have an adequate library for hyperbolic geometry

---

## hyperbolic_isometry

### Name of formal statement
hyperbolic_isometry

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperbolic_isometry = new_definition
 `hyperbolic_isometry (f:real^2->real^2) <=>
    (!x. norm x < &1 ==> norm(f x) < &1) /\
    (!x y. norm x < &1 /\ norm y < &1 ==> ddist(f x,f y) = ddist(x,y)) /\
    (!x y z. norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (f x) (f y,f z) <=> between x (y,z)))`;;
```

### Informal statement
A function $f: \mathbb{R}^2 \to \mathbb{R}^2$ is a hyperbolic isometry if and only if the following conditions hold:
1. $f$ maps the unit disk to itself: for all $x$ with $\|x\| < 1$, we have $\|f(x)\| < 1$.
2. $f$ preserves hyperbolic distance: for all $x, y$ with $\|x\| < 1$ and $\|y\| < 1$, we have $d_d(f(x), f(y)) = d_d(x, y)$, where $d_d$ denotes the hyperbolic distance function.
3. $f$ preserves the betweenness relation: for all $x, y, z$ with $\|x\| < 1$, $\|y\| < 1$, and $\|z\| < 1$, the point $x$ is between $y$ and $z$ if and only if $f(x)$ is between $f(y)$ and $f(z)$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition formalizes the concept of a hyperbolic isometry in the Poincaré disk model of hyperbolic geometry. The Poincaré disk model represents the hyperbolic plane as the open unit disk in $\mathbb{R}^2$.

Hyperbolic isometries are transformations that preserve the structure of hyperbolic space. The three conditions in the definition ensure that:
1. The transformation stays within the hyperbolic space (the unit disk)
2. Distances are preserved according to the hyperbolic metric
3. The notion of "betweenness" is preserved, which ensures that geodesic (straight) lines in hyperbolic space are mapped to geodesic lines

These properties make hyperbolic isometries the hyperbolic analog of Euclidean isometries (rigid motions). In the Poincaré disk model, hyperbolic isometries can be represented by Möbius transformations that preserve the unit disk.

### Dependencies
No explicit dependencies are listed.

### Porting notes
When implementing this in other proof assistants:
- The definition depends on the implementation of `ddist` (hyperbolic distance) and `between` (betweenness relation), so these would need to be ported first
- Make sure the norm function in the target system corresponds to the Euclidean norm in $\mathbb{R}^2$
- The betweenness relation in hyperbolic geometry may be defined differently in different systems, so care should be taken to ensure consistency

---

## HYPERBOLIC_TRANSLATION

### HYPERBOLIC_TRANSLATION
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERBOLIC_TRANSLATION = prove
 (`!w. norm w < &1
       ==> ?f:real^2->real^2 g:real^2->real^2.
                hyperbolic_isometry f /\ hyperbolic_isometry g /\
                f(w) = vec 0 /\ g(vec 0) = w /\
                (!x. norm x < &1 ==> f(g x) = x) /\
                (!x. norm x < &1 ==> g(f x) = x)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[hyperbolic_isometry] THEN MAP_EVERY EXISTS_TAC
   [`\x. kleinify(moebius_function(&0) (poincarify w) (poincarify x))`;
   `\x. kleinify(moebius_function(&0) (--(poincarify w)) (poincarify x))`] THEN
  ASM_SIMP_TAC[NORM_KLEINIFY_MOEBIUS_LT; NORM_POINCARIFY_LT;
               DDIST_KLEINIFY_MOEBIUS; KLEINIFY_POINCARIFY; VECTOR_NEG_NEG;
               BETWEEN_KLEINIFY_MOEBIUS; NORM_NEG; MOEBIUS_FUNCTION_COMPOSE;
               POINCARIFY_KLEINIFY; MOEBIUS_FUNCTION_NORM_LT_1] THEN
  ASM_SIMP_TAC[MOEBIUS_FUNCTION_SIMPLE; COMPLEX_SUB_REFL; complex_div;
               COMPLEX_VEC_0; KLEINIFY_0; POINCARIFY_0; COMPLEX_MUL_LZERO;
               COMPLEX_MUL_RZERO; COMPLEX_SUB_LZERO; COMPLEX_NEG_NEG;
               COMPLEX_SUB_RZERO; COMPLEX_INV_1; COMPLEX_MUL_RID;
               KLEINIFY_POINCARIFY]);;
```

### Informal statement
For any point $w$ in the unit disk (i.e., $\|w\| < 1$), there exist hyperbolic isometries $f$ and $g$ from $\mathbb{R}^2$ to $\mathbb{R}^2$ such that:

1. $f(w) = \vec{0}$ (i.e., $f$ maps $w$ to the origin)
2. $g(\vec{0}) = w$ (i.e., $g$ maps the origin to $w$)
3. For all points $x$ in the unit disk (i.e., $\|x\| < 1$), $f(g(x)) = x$
4. For all points $x$ in the unit disk (i.e., $\|x\| < 1$), $g(f(x)) = x$

In other words, $f$ and $g$ are inverse hyperbolic isometries between the unit disk, with $f$ taking $w$ to the origin and $g$ taking the origin to $w$.

### Informal proof
The proof constructs explicit formulas for the hyperbolic isometries $f$ and $g$ using Möbius transformations.

We define:
- $f(x) = \text{kleinify}(\text{moebius\_function}(0, \text{poincarify}(w), \text{poincarify}(x)))$
- $g(x) = \text{kleinify}(\text{moebius\_function}(0, -\text{poincarify}(w), \text{poincarify}(x)))$

The proof proceeds by showing these functions satisfy the required properties:

1. First, we verify that $f$ and $g$ are indeed hyperbolic isometries by showing they preserve the hyperbolic distance.

2. To show $f(w) = \vec{0}$:
   - Apply the definition of $f$
   - Use `MOEBIUS_FUNCTION_SIMPLE` to compute $\text{moebius\_function}(0, z, z)$
   - This gives $\frac{z-z}{1-\overline{z}z} = 0$
   - Then apply $\text{kleinify}$ to get $\vec{0}$

3. To show $g(\vec{0}) = w$:
   - Apply the definition of $g$
   - Use `MOEBIUS_FUNCTION_SIMPLE` and simplify using complex arithmetic
   - This maps back to $w$ after applying $\text{kleinify}$

4. For the inverse relationships:
   - Use `MOEBIUS_FUNCTION_COMPOSE` which states that when $-w_1 = w_2$ and norms are less than 1, then $\text{moebius\_function}(0, w_1, \text{moebius\_function}(0, w_2, z)) = z$
   - Since we defined $g$ using $-\text{poincarify}(w)$ and $f$ using $\text{poincarify}(w)$, this condition is satisfied
   - Apply the conversions between Poincaré and Klein models to complete the proof

### Mathematical insight
This theorem establishes the existence of hyperbolic translations in the hyperbolic plane modeled by the unit disk. In hyperbolic geometry, unlike Euclidean geometry, there is no concept of global translation invariance. However, this theorem shows that for any point in the hyperbolic plane, we can find a hyperbolic isometry that "translates" the origin to that point, and vice versa.

The proof uses Möbius transformations between different models of hyperbolic geometry (Klein and Poincaré disk models). This is analogous to how in Euclidean geometry we use the function $T_v(x) = x + v$ to translate a point $x$ by vector $v$. In hyperbolic geometry, the translation operation is more complex but serves the same purpose of moving points while preserving the geometric structure.

This result is fundamental in establishing the homogeneity of the hyperbolic plane: every point looks the same as every other point in terms of the local geometry.

### Dependencies
- **Theorems:**
  - `MOEBIUS_FUNCTION_SIMPLE`: Defines the Möbius function $\text{moebius\_function}(0, w, z) = \frac{z-w}{1-\overline{w}z}$
  - `MOEBIUS_FUNCTION_NORM_LT_1`: Shows that Möbius functions preserve the unit disk
  - `MOEBIUS_FUNCTION_COMPOSE`: Provides the composition property of Möbius functions
  
- **Definitions:**
  - `moebius_function`: Defines $\text{moebius\_function}(t, w, z) = e^{it} \cdot \frac{z-w}{1-\overline{w}z}$
  - (Implicit) `hyperbolic_isometry`: Functions that preserve hyperbolic distance
  - (Implicit) `kleinify`, `poincarify`: Conversion functions between Klein and Poincaré disk models

### Porting notes
When porting this to another proof assistant:
1. You'll need to first implement the Poincaré and Klein disk models of hyperbolic geometry and the conversion functions between them.
2. Implement Möbius transformations and prove their basic properties.
3. The proof relies on complex arithmetic simplifications - make sure your target system has good support for complex number manipulation.
4. The statement involves higher-order functions, so ensure your target system handles function spaces appropriately.

---

## plane_tybij

### Name of formal statement
plane_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let plane_tybij =
  let th = prove
   (`?x:real^2. norm x < &1`,
    EXISTS_TAC `vec 0:real^2` THEN NORM_ARITH_TAC) in
  new_type_definition "plane" ("mk_plane","dest_plane") th;;
```

### Informal statement
This defines a new type `plane` that is in bijection with the set of points in $\mathbb{R}^2$ with norm less than 1 (the open unit disk). The bijection is established through two functions:
- `mk_plane`: maps from the subset of $\mathbb{R}^2$ with norm less than 1 to the new type `plane`
- `dest_plane`: maps from the type `plane` back to $\mathbb{R}^2$ vectors with norm less than 1

The bijection is proven based on the existence of at least one vector in $\mathbb{R}^2$ with norm less than 1.

### Informal proof
The proof establishes that the set of points in $\mathbb{R}^2$ with norm less than 1 is non-empty, which is required for the new type definition:

* The proof shows that $\exists x \in \mathbb{R}^2$ such that $\|x\| < 1$ by choosing $x = \vec{0}$ (the zero vector).
* The tactic `EXISTS_TAC` introduces the zero vector as the witness.
* The `NORM_ARITH_TAC` tactic completes the proof by showing that $\|\vec{0}\| < 1$, which is true since $\|\vec{0}\| = 0$.

After proving the non-emptiness of the set, the new type `plane` is defined as isomorphic to this set using the `new_type_definition` mechanism.

### Mathematical insight
This definition constructs a type that represents the open unit disk in the Euclidean plane. The open unit disk is an important mathematical object used in various contexts:

1. In the context of this development, it likely serves as a model for a mathematical plane or a bounded region for geometric reasoning.
2. Creating a dedicated type for the unit disk allows for type-safe operations that are guaranteed to work within this bounded region.
3. The approach demonstrates how HOL Light's type definition mechanism can be used to create types that correspond to specific mathematical structures with desired properties.

The choice of using the open unit disk (rather than, for example, the entire $\mathbb{R}^2$) suggests that this development may be focused on bounded regions or might leverage properties specific to the unit disk, such as its compactness or its role in conformal mappings.

### Dependencies
No explicit dependencies were provided beyond the use of HOL Light's built-in tactics and functions.

### Porting notes
When porting this definition to other proof assistants:

1. Ensure the target system has a way to define new types based on subsets of existing types.
2. In some systems (like Lean or Isabelle), you might use a subtype or typedef mechanism instead.
3. The proof of non-emptiness might need to be adjusted based on how the target system handles vector norms.
4. Some systems might require more explicit handling of the bijection functions and their properties.

---

## pbetween

### Name of formal statement
pbetween

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pbetween = new_definition
 `pbetween y (x,z) <=> between (dest_plane y) (dest_plane x,dest_plane z)`;;
```

### Informal statement
For points $x$, $y$, and $z$ in a projective space, the relation $\text{pbetween } y (x,z)$ holds if and only if the point $\text{dest\_plane}(y)$ is between the points $\text{dest\_plane}(x)$ and $\text{dest\_plane}(z)$ in the corresponding affine space.

In other words, this definition extends the concept of "betweenness" from affine geometry to projective geometry by using the `dest_plane` function to map projective points to their affine counterparts.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition establishes a betweenness relation in projective geometry by leveraging the existing betweenness relation in affine geometry. The `dest_plane` function maps projective points to affine points, allowing us to define betweenness in projective space in terms of the well-established notion of betweenness in affine space.

The betweenness relation is fundamental in geometry as it captures the intuitive notion of one point lying on the line segment between two other points. By extending this concept to projective geometry, we can reason about collinearity and order of points in projective space.

This definition helps bridge the gap between affine and projective geometry, allowing results from affine geometry to be applied in a projective context when appropriate.

### Dependencies
- `between`: The betweenness relation in affine geometry
- `dest_plane`: Function that maps projective points to their affine counterparts

### Porting notes
When porting this definition to another proof assistant, ensure that:
1. The `between` relation for affine geometry is already defined
2. The `dest_plane` function mapping projective points to affine points is implemented
3. The target system can handle the function composition pattern used here

---

## pdist

### Name of formal statement
pdist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pdist = new_definition
 `pdist(x,y) = ddist(dest_plane x,dest_plane y)`;;
```

### Informal statement
The function `pdist` is defined as:

$$\text{pdist}(x, y) = \text{ddist}(\text{dest\_plane}(x), \text{dest\_plane}(y))$$

where $\text{pdist}$ represents the distance between two points in a plane, $\text{dest\_plane}$ extracts the planar coordinates of the points, and $\text{ddist}$ computes the distance between these coordinates.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition establishes a distance function for points in a plane by leveraging an existing distance function `ddist` that works on the coordinates extracted from points via `dest_plane`. 

The definition serves as a convenient abstraction layer that allows for computing distances between plane points directly, without having to manually extract their coordinates first. This pattern is common in formal libraries to create more readable code and to separate the representation details from their usage.

It appears that HOL Light uses a typed representation for plane points, which need to be "destructed" to access their coordinate values before computing distances.

### Dependencies
#### Definitions
- `ddist` - Likely a function that computes distance between coordinate pairs
- `dest_plane` - A function that extracts coordinates from a plane point representation

### Porting notes
When porting this definition to other proof assistants:

1. Ensure that both `ddist` and `dest_plane` functions are properly ported first
2. Check if the target system has a different approach to representing points in a plane - some systems might use records or tuples directly instead of a specialized type with destructors
3. Consider whether the target system would benefit from defining this function or if direct use of `ddist` with coordinate extraction is more idiomatic

---

## DEST_PLANE_NORM_LT

### DEST_PLANE_NORM_LT
- `DEST_PLANE_NORM_LT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DEST_PLANE_NORM_LT = prove
 (`!x. norm(dest_plane x) < &1`,
  MESON_TAC[plane_tybij]);;
```

### Informal statement
For all planes $x$, the norm of $\text{dest\_plane}(x)$ is less than $1$:
$$\forall x. \|\text{dest\_plane}(x)\| < 1$$

### Informal proof
The proof is done using the `MESON_TAC` procedure with the theorem `plane_tybij` as a dependency. 

The theorem `plane_tybij` defines the bijection between planes and vectors with norm less than 1. Specifically, it establishes that `dest_plane` maps a plane to a vector with norm less than 1, and `mk_plane` maps such vectors back to planes, with these two functions being inverses of each other.

The current theorem simply extracts the norm bound property from this bijection characterization.

### Mathematical insight
This theorem establishes a key property of the `dest_plane` function, which maps planes to their vector representations. The constraint that these vectors have norm less than 1 is important for the representation of planes in 3D space.

In HOL Light's formalization, planes are represented using vectors with norm less than 1, which provide a canonical way to represent the orientation and position of a plane in 3D space. This theorem confirms that the `dest_plane` function, which extracts this representation, always produces vectors satisfying the norm constraint.

This is part of a larger algebraic framework for geometric reasoning in HOL Light.

### Dependencies
- `plane_tybij`: Establishes the bijection between planes and vectors with norm less than 1

### Porting notes
When porting this theorem to another system, ensure that the representation of planes and the bijection between planes and vectors is set up correctly. The norm constraint is a crucial aspect of this representation that must be preserved.

---

## DEST_PLANE_EQ

### Name of formal statement
DEST_PLANE_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DEST_PLANE_EQ = prove
 (`!x y. dest_plane x = dest_plane y <=> x = y`,
  MESON_TAC[plane_tybij]);;
```

### Informal statement
For all planes $x$ and $y$, we have:
$$\text{dest\_plane}(x) = \text{dest\_plane}(y) \iff x = y$$

This states that the function `dest_plane` is injective: two planes are equal if and only if their images under `dest_plane` are equal.

### Informal proof
This theorem is proved using `MESON_TAC` with the theorem `plane_tybij`. 

The theorem `plane_tybij` states that `dest_plane` and its inverse function form a bijection between the type of planes and their representation. Since `dest_plane` is part of a bijection, it is injective, which directly implies that $\text{dest\_plane}(x) = \text{dest\_plane}(y) \iff x = y$.

### Mathematical insight
This theorem establishes that the function `dest_plane`, which extracts the internal representation of a plane, is injective. This is an important property that ensures the plane representation is unique - no two distinct planes can have the same internal representation.

This result is essentially verifying that the type representation for planes has been correctly defined, which is crucial for the consistency of the geometric reasoning system. It ensures that operations on planes based on their internal representation are well-defined.

### Dependencies
- `plane_tybij` - Establishes that `dest_plane` and its inverse form a bijection

### Porting notes
When porting this to another system, ensure that the type definition for planes maintains this injectivity property. In systems with dependent types or strong type theory support, this might be automatically guaranteed by the type definition mechanism.

---

## FORALL_DEST_PLANE

### Name of formal statement
FORALL_DEST_PLANE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FORALL_DEST_PLANE = prove
 (`!P. (!x. P(dest_plane x)) <=> (!x. norm x < &1 ==> P x)`,
  MESON_TAC[plane_tybij]);;
```

### Informal statement
For any predicate $P$, the statement $\forall x. P(\textrm{dest\_plane}(x))$ is equivalent to $\forall x. \|x\| < 1 \Rightarrow P(x)$, where $\|x\|$ denotes the norm of $x$.

### Informal proof
This theorem is proved using the `MESON_TAC` automated reasoning tactic with the theorem `plane_tybij`. The theorem `plane_tybij` likely establishes a bijection between elements of the type represented by `plane` and vectors with norm less than 1, where `dest_plane` is the function mapping from the former to the latter.

The proof relies on the fact that `dest_plane` establishes a correspondence between all elements of the plane type and precisely those vectors with norm less than 1. Therefore, quantifying over all `x` and applying `dest_plane` is equivalent to directly quantifying over all vectors with norm less than 1.

### Mathematical insight
This theorem establishes a correspondence between quantification over a type (likely representing the open unit disk) and quantification over vectors with norm less than 1. This kind of bijection is common in type definitions in HOL Light, where abstract types are often defined as isomorphic to specific subsets of existing types.

The result allows for switching between these two representations in proofs, enabling one to work either with the abstract type or with concrete vectors satisfying the norm constraint, depending on which is more convenient for a particular proof.

### Dependencies
- `plane_tybij` - Likely establishes the bijection between the plane type and vectors with norm less than 1

### Porting notes
When porting this theorem, ensure that the corresponding type definition for the plane and the bijection functions (`dest_plane` and presumably a corresponding `mk_plane`) are properly defined in the target system. The representation of norms and the concept of the open unit disk may vary between formal systems.

---

## EXISTS_DEST_PLANE

### Name of formal statement
EXISTS_DEST_PLANE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXISTS_DEST_PLANE = prove
 (`!P. (?x. P(dest_plane x)) <=> (?x. norm x < &1 /\ P x)`,
  MESON_TAC[plane_tybij]);;
```

### Informal statement
For any predicate $P$, the statement $\exists x. P(\text{dest\_plane}(x))$ is equivalent to $\exists x. \|x\| < 1 \land P(x)$.

In other words, applying a predicate $P$ to the result of the `dest_plane` function for some input is equivalent to finding an element in the open unit ball that satisfies $P$.

### Informal proof
This theorem follows directly from the bijection properties established in `plane_tybij`. The theorem states that the functions `mk_plane` and `dest_plane` establish a bijection between:
- The abstract type `:plane` 
- The set of points in the Euclidean space with norm strictly less than 1

Since `dest_plane` maps elements from `:plane` bijectively to points with norm less than 1, the existence of an $x$ such that $P(\text{dest\_plane}(x))$ holds is equivalent to the existence of a point $x$ with norm less than 1 such that $P(x)$ holds.

### Mathematical insight
This theorem establishes the relationship between existential quantification over the abstract type `:plane` and existential quantification over the concrete representation as points in the open unit ball.

It allows us to translate statements involving existential quantification over the plane type into statements about points in the open unit ball with norm less than 1. This is particularly useful when we want to reason about properties of points in the plane by using their concrete representation.

The theorem is part of the machinery that allows working with the abstract type `:plane` while leveraging the concrete representation as points with norm less than 1.

### Dependencies
- `plane_tybij` - Theorem establishing the bijection between the abstract type `:plane` and points with norm less than 1

### Porting notes
When porting this to another system, ensure that:
1. The corresponding type definition for the plane and the bijection functions are properly established
2. The representation of the open unit ball (points with norm less than 1) is defined
3. The system has mechanisms for handling abstract type definitions with their concrete representations

---

## TARSKI_AXIOM_1_NONEUCLIDEAN

### TARSKI_AXIOM_1_NONEUCLIDEAN
- `TARSKI_AXIOM_1_NONEUCLIDEAN`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_1_NONEUCLIDEAN = prove
 (`!a b. pdist(a,b) = pdist(b,a)`,
  REWRITE_TAC[pdist; DDIST_SYM]);;
```

### Informal statement
For any points $a$ and $b$, the pseudo-distance between $a$ and $b$ is equal to the pseudo-distance between $b$ and $a$. Formally:

$$\forall a,b.\, \text{pdist}(a,b) = \text{pdist}(b,a)$$

This states that the pseudo-distance function is symmetric.

### Informal proof
The proof is straightforward:
- We rewrite using the definition of `pdist` and the symmetry property of `DDIST` (denoted as `DDIST_SYM`).
- The `DDIST_SYM` theorem states that the distance function `DDIST` is symmetric, i.e., $\text{DDIST}(a,b) = \text{DDIST}(b,a)$.
- Since `pdist` is defined in terms of `DDIST`, the symmetry property carries over to `pdist`.

### Mathematical insight
This theorem corresponds to Tarski's first axiom for non-Euclidean geometry, establishing the symmetry of the pseudo-distance function. In Tarski's axiomatic approach to geometry, the equidistance relation is a fundamental primitive, and this axiom ensures that distance is properly defined by enforcing its symmetry property. 

The use of "pseudo-distance" (`pdist`) rather than regular distance suggests this is adapted for non-Euclidean geometries, where distance may have different properties than in Euclidean space, but the symmetry property is still essential and preserved.

### Dependencies
- **Definitions:** 
  - `pdist` (definition of pseudo-distance)
- **Theorems:**
  - `DDIST_SYM` (symmetry property of the distance function)

### Porting notes
This theorem should be straightforward to port to other systems. The main requirement is to ensure that the underlying distance function (`DDIST`) and the pseudo-distance function (`pdist`) are defined appropriately in the target system, with the symmetry property of distance preserved.

---

## TARSKI_AXIOM_2_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_2_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_2_NONEUCLIDEAN = prove
 (`!a b p q r s.
        pdist(a,b) = pdist(p,q) /\ pdist(a,b) = pdist(r,s)
        ==> pdist(p,q) = pdist(r,s)`,
  REAL_ARITH_TAC);;
```

### Informal statement
For any points $a$, $b$, $p$, $q$, $r$, and $s$, if $\text{pdist}(a,b) = \text{pdist}(p,q)$ and $\text{pdist}(a,b) = \text{pdist}(r,s)$, then $\text{pdist}(p,q) = \text{pdist}(r,s)$.

### Informal proof
This is proven using `REAL_ARITH_TAC`, which is HOL Light's tactic for automated reasoning about real arithmetic. The proof follows directly from the transitivity property of equality:
- If $\text{pdist}(a,b) = \text{pdist}(p,q)$ and $\text{pdist}(a,b) = \text{pdist}(r,s)$, then by transitivity of equality, $\text{pdist}(p,q) = \text{pdist}(r,s)$.

### Mathematical insight
This theorem formalizes the second axiom of Tarski's axiom system for geometry, specifically adapted for non-Euclidean geometry. The axiom establishes the transitivity property for the relation of equidistance, which is fundamental for any metric space.

In Tarski's axiomatization of geometry, equidistance is a primitive notion, and this axiom ensures that it behaves as expected with respect to the equality relation. While this property might seem trivial when working with a specific metric like Euclidean distance, it's essential to explicitly state it in an axiomatic framework where distance is treated as a primitive concept.

The function `pdist` likely represents a pseudometric or projective distance function appropriate for non-Euclidean geometry.

### Dependencies
No explicit dependencies are listed, but the proof uses:
- `REAL_ARITH_TAC`: HOL Light's tactic for real arithmetic reasoning

### Porting notes
This theorem should be straightforward to port to other proof assistants:
- The statement is a simple property of equality
- The proof is automatic using real arithmetic reasoning
- When porting, ensure the distance function `pdist` is defined appropriately for the non-Euclidean setting being used
- Most proof assistants have tactics similar to `REAL_ARITH_TAC` for handling basic arithmetic

---

## TARSKI_AXIOM_3_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_3_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_3_NONEUCLIDEAN = prove
 (`!a b c. pdist(a,b) = pdist(c,c) ==> a = b`,
  SIMP_TAC[FORALL_DEST_PLANE; pdist; DDIST_REFL; DDIST_EQ_0; DEST_PLANE_EQ]);;
```

### Informal statement
For all points $a$, $b$, and $c$ in the plane, if $\text{pdist}(a, b) = \text{pdist}(c, c)$, then $a = b$.

Here, $\text{pdist}(x, y)$ represents the pseudodistance between points $x$ and $y$ in the non-Euclidean plane.

### Informal proof
The proof proceeds by simplification tactics:

1. We first apply `SIMP_TAC[FORALL_DEST_PLANE]` to ensure all points are considered in the plane.

2. Then we unfold the definition of `pdist` (pseudodistance).

3. We use `DDIST_REFL` which states that the distance from any point to itself is zero, i.e., $\text{pdist}(c, c) = 0$.

4. We then apply `DDIST_EQ_0` which states that the distance between two points is zero if and only if the points are equal.

5. Finally, `DEST_PLANE_EQ` is used to assert that two points in the plane are equal.

In other words, since $\text{pdist}(a, b) = \text{pdist}(c, c) = 0$, we have $\text{pdist}(a, b) = 0$, which implies $a = b$.

### Mathematical insight
This theorem represents the identity axiom for equidistance in Tarski's axiomatic system for non-Euclidean geometry. It essentially states that the only point equidistant from itself is itself, or alternatively, that the distance between two points is zero if and only if they are the same point.

In Tarski's axiomatic system, this is one of the fundamental axioms needed to develop geometry without relying on coordinates or numerical distances. This version is specifically adapted for non-Euclidean geometry.

The axiom guarantees that the distance function behaves properly with respect to identity, which is a basic expected property of any reasonable notion of distance.

### Dependencies
- `FORALL_DEST_PLANE`: Ensures all points are in the plane
- `pdist`: Definition of pseudodistance
- `DDIST_REFL`: States that distance from a point to itself is zero
- `DDIST_EQ_0`: States that distance between points is zero iff they are equal
- `DEST_PLANE_EQ`: Equality for points in the plane

### Porting notes
When porting to other systems, ensure that the corresponding notion of distance or pseudodistance for the non-Euclidean plane is properly defined. Different proof assistants may have different representations of geometric concepts, so appropriate translations might be necessary.

---

## TARSKI_AXIOM_4_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_4_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_4_NONEUCLIDEAN = prove
 (`!a q b c. ?x. pbetween a (q,x) /\ pdist(a,x) = pdist(b,c)`,
  REWRITE_TAC[pbetween; pdist; FORALL_DEST_PLANE; EXISTS_DEST_PLANE] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d:real^2. norm d < &1 /\ ddist(b:real^2,c) = ddist(vec 0,d)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `b:real^2` HYPERBOLIC_TRANSLATION) THEN
    ASM_REWRITE_TAC[hyperbolic_isometry] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `norm(a:real^2) < &1 /\ norm(q:real^2) < &1 /\ norm(d:real^2) < &1`
   MP_TAC THENL [ASM_REWRITE_TAC[]; REPEAT(POP_ASSUM(K ALL_TAC))] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`d:real^2`; `q:real^2`; `a:real^2`] THEN
  MATCH_MP_TAC(MESON[] `P(vec 0) /\ (P(vec 0) ==> !x. P x) ==> !x. P x`) THEN
  REWRITE_TAC[NORM_0; REAL_LT_01] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `vec 0:real^2` TARSKI_AXIOM_4_EUCLIDEAN) THEN
    MESON_TAC[DIST_0; DDIST_EQ_ORIGIN];
    DISCH_THEN(LABEL_TAC "*") THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `a:real^2` HYPERBOLIC_TRANSLATION) THEN
    ASM_REWRITE_TAC[hyperbolic_isometry; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`(f:real^2->real^2) q`; `d:real^2`]) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^2->real^2) x` THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For any points $a$, $q$, $b$, and $c$, there exists a point $x$ such that $q$ is between $a$ and $x$ in the hyperbolic plane (represented by `pbetween a (q,x)`), and the hyperbolic distance from $a$ to $x$ is equal to the hyperbolic distance from $b$ to $c$ (represented by `pdist(a,x) = pdist(b,c)`).

### Informal proof
This proof establishes Tarski's Axiom 4 (segment construction) in the non-Euclidean (hyperbolic) plane. The proof proceeds as follows:

- First, we rewrite using `pbetween` and `pdist` definitions, and convert to plane-specific formulations using `FORALL_DEST_PLANE` and `EXISTS_DEST_PLANE`.

- The proof then works with the Poincaré disk model of hyperbolic geometry, where points are represented as vectors in $\mathbb{R}^2$ with norm less than 1.

- We establish that there exists a point $d$ with $\|d\| < 1$ such that the hyperbolic distance between $b$ and $c$ equals the hyperbolic distance from the origin to $d$:
  $$\exists d \in \mathbb{R}^2 : \|d\| < 1 \land \text{ddist}(b, c) = \text{ddist}(\vec{0}, d)$$
  This is done using the existence of hyperbolic isometries that translate any point to the origin.

- The proof then focuses on showing the result first for the special case where $a = \vec{0}$ (the origin), using `TARSKI_AXIOM_4_EUCLIDEAN` which provides the analogous result in Euclidean geometry.

- Finally, for the general case ($a \neq \vec{0}$), we use another hyperbolic translation that moves $a$ to the origin, solve the problem there, and then apply the inverse translation to find our desired point $x$.

### Mathematical insight
Tarski's Axiom 4 for non-Euclidean geometry is the hyperbolic analogue of the Euclidean segment construction axiom. In both geometries, the axiom asserts that given two points $a$ and $q$, we can extend the segment beyond $q$ to a point $x$ such that the distance from $a$ to $x$ equals any given distance (in this case, the distance between points $b$ and $c$).

The proof illustrates a common technique in hyperbolic geometry: mapping problems to the origin using hyperbolic isometries, solving them there (where calculations are often simpler), and then mapping the solutions back.

This axiom is part of Tarski's system of geometry, which provides a first-order axiomatization of geometry. While the Euclidean version allows unlimited segment extension, the hyperbolic version must account for the bounded nature of the Poincaré disk model.

### Dependencies
#### Theorems
- `TARSKI_AXIOM_4_EUCLIDEAN`: The Euclidean version of this axiom, stating that for any points $a$, $q$, $b$, $c$ in $\mathbb{R}^2$, there exists a point $x$ such that $q$ is between $a$ and $x$, and the Euclidean distance from $a$ to $x$ equals the distance from $b$ to $c$.
- `HYPERBOLIC_TRANSLATION`: Provides isometries (distance-preserving maps) in hyperbolic space that translate points.
- Various supporting theorems about `ddist`, `pbetween`, `pdist`, and properties of the Poincaré disk model.

#### Definitions
- `pbetween`: Represents the betweenness relation in the hyperbolic plane.
- `pdist`: Represents distance in the hyperbolic plane.
- `ddist`: Distance function in the Poincaré disk model.
- `hyperbolic_isometry`: Characterizes maps that preserve hyperbolic distances.

### Porting notes
When porting this theorem to other systems:
1. Ensure that the underlying model of hyperbolic geometry (Poincaré disk) is properly set up.
2. The proof relies heavily on the existence of hyperbolic isometries and their properties.
3. The technique of reducing a general case to the origin case is common in hyperbolic geometry and should be implementable in most proof assistants.
4. Note that working with hyperbolic geometry requires tracking constraints (like $\|x\| < 1$ for points in the Poincaré disk) that don't appear in Euclidean geometry.

---

## TARSKI_AXIOM_5_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_5_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_5_NONEUCLIDEAN = prove
 (`!a b c x a' b' c' x'.
        ~(a = b) /\
        pdist(a,b) = pdist(a',b') /\
        pdist(a,c) = pdist(a',c') /\
        pdist(b,c) = pdist(b',c') /\
        pbetween b (a,x) /\ pbetween b' (a',x') /\ pdist(b,x) = pdist(b',x')
        ==> pdist(c,x) = pdist(c',x')`,
  REWRITE_TAC[FORALL_DEST_PLANE; pdist; pbetween; GSYM DEST_PLANE_EQ] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `b':real^2` HYPERBOLIC_TRANSLATION) THEN
  MP_TAC(ISPEC `b:real^2` HYPERBOLIC_TRANSLATION) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[hyperbolic_isometry] THEN MAP_EVERY X_GEN_TAC
   [`f:real^2->real^2`; `f':real^2->real^2`; `g:real^2->real^2`;
    `g':real^2->real^2`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) x`; `(f:real^2->real^2) c`;
                `(g:real^2->real^2) x'`; `(g:real^2->real^2) c'`]
        DDIST_CONGRUENT_TRIPLES_0) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ q ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DDIST_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) a`; `(f:real^2->real^2) c`;
                `(g:real^2->real^2) a'`; `(g:real^2->real^2) c'`]
        DDIST_CONGRUENT_TRIPLES_0) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM DDIST_CONGRUENT_TRIPLES_0] THEN  CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `(f:complex->complex) b = vec 0`)] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `(g:complex->complex) b' = vec 0`)] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[DDIST_SYM];
    STRIP_TAC THEN MP_TAC(ISPECL
     [`(f:real^2->real^2) a`; `(f:real^2->real^2) b`; `(f:real^2->real^2) c`;
      `(f:real^2->real^2) x`;`(g:real^2->real^2) a'`; `(g:real^2->real^2) b'`;
      `(g:real^2->real^2) c'`; `(g:real^2->real^2) x'`]
     TARSKI_AXIOM_5_EUCLIDEAN) THEN
    SUBGOAL_THEN
     `ddist((f:real^2->real^2) b,f x) = ddist((g:real^2->real^2) b',g x')`
    MP_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DDIST_EQ_ORIGIN] THEN DISCH_TAC] THEN
    ASM_MESON_TAC[DIST_SYM; DIST_0]]);;
```

### Informal statement
For any points $a, b, c, x, a', b', c', x'$, if:
- $a \neq b$
- $pdist(a,b) = pdist(a',b')$
- $pdist(a,c) = pdist(a',c')$
- $pdist(b,c) = pdist(b',c')$
- $pbetween\ b\ (a,x)$ and $pbetween\ b'\ (a',x')$ 
- $pdist(b,x) = pdist(b',x')$

Then $pdist(c,x) = pdist(c',x')$.

Here $pdist$ represents a non-Euclidean (hyperbolic) distance function, and $pbetween$ represents betweenness in the non-Euclidean geometry.

### Informal proof
The proof uses hyperbolic transformations and proceeds as follows:

- First, we rewrite the statement using the planar descriptions of the non-Euclidean primitives.
- We apply hyperbolic translations to move $b$ and $b'$ to the origin:
  - For point $b$, we choose a hyperbolic translation $f$ such that $f(b) = 0$
  - For point $b'$, we choose a hyperbolic translation $g$ such that $g(b') = 0$
- These translations are hyperbolic isometries, so they preserve hyperbolic distances.
- We apply the theorem `DDIST_CONGRUENT_TRIPLES_0` to establish congruence relationships in the translated spaces.
- We reduce the problem to showing that the distances between the translated points $(f(x), f(c))$ and $(g(x'), g(c'))$ are equal.
- We use the Euclidean version of Tarski's Axiom 5 (`TARSKI_AXIOM_5_EUCLIDEAN`) on the transformed points.
- The resulting equality of distances in the transformed space implies the desired equality in the original space.

### Mathematical insight
This theorem is a non-Euclidean analog of Tarski's fifth axiom, known as the five-segments axiom. It is a fundamental axiom in Tarski's axiomatization of geometry. The axiom essentially states that if two "configurations" of points have corresponding distances equal, then other corresponding distances must also be equal.

In the context of non-Euclidean (hyperbolic) geometry, this theorem shows that the five-segments property holds for hyperbolic distances as well. It serves as a bridge between Euclidean and non-Euclidean geometries, showing that certain structural properties are preserved.

The proof technique of using hyperbolic translations to move points to a standard position (the origin) is a common approach in hyperbolic geometry. This allows us to leverage results from Euclidean geometry after appropriate transformations.

### Dependencies
- **Theorems**:
  - `TARSKI_AXIOM_5_EUCLIDEAN`: The Euclidean version of Tarski's fifth axiom
  - `HYPERBOLIC_TRANSLATION`: Existence of hyperbolic translations
  - `DDIST_CONGRUENT_TRIPLES_0`: Congruence of distance triples when one point is at the origin
  - `DDIST_SYM`: Symmetry of hyperbolic distance
  - `DDIST_EQ_ORIGIN`: Properties of hyperbolic distance with respect to the origin

- **Definitions**:
  - `pdist`: Non-Euclidean distance function
  - `pbetween`: Non-Euclidean betweenness relation
  - `DEST_PLANE_EQ`: Destination plane equality
  - `FORALL_DEST_PLANE`: Universal quantification over the destination plane
  - `hyperbolic_isometry`: Properties of hyperbolic isometries

### Porting notes
When porting this theorem:
1. Ensure that your system has a well-defined model of hyperbolic geometry with properly defined notions of distance and betweenness.
2. The proof relies heavily on the existence of hyperbolic translations that preserve distances. Make sure these are available in your target system.
3. The connection between Euclidean and non-Euclidean versions of the axiom is crucial - ensure that the Euclidean version is already ported before attempting this one.
4. Be aware that HOL Light's representation of complex numbers as 2D vectors may differ from other systems' representations.

---

## TARSKI_AXIOM_6_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_6_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_6_NONEUCLIDEAN = prove
 (`!a b. pbetween b (a,a) ==> a = b`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; GSYM DEST_PLANE_EQ] THEN
  MESON_TAC[TARSKI_AXIOM_6_EUCLIDEAN]);;
```

### Informal statement
For all points $a$ and $b$, if $b$ lies between $a$ and $a$ in the plane (as defined by the `pbetween` relation), then $a = b$.

In formal notation:
$$\forall a, b. \text{pbetween}(b, (a, a)) \Rightarrow a = b$$

### Informal proof
This theorem proves the identity property for the `pbetween` relation in a non-Euclidean (planar) setting, similar to the Euclidean version.

The proof proceeds as follows:
- First, we rewrite using the definition of `pbetween` and plane-related functions (`FORALL_DEST_PLANE` and `GSYM DEST_PLANE_EQ`).
- Then we apply the Euclidean version of the same axiom (`TARSKI_AXIOM_6_EUCLIDEAN`) using `MESON_TAC`.

Essentially, the proof reduces the planar version to the previously established Euclidean version by proper handling of the plane constraints.

### Mathematical insight
This theorem establishes a fundamental property of the betweenness relation in Tarski's axiomatization of geometry, specifically for planar geometry. It states that if a point $b$ is between identical points $a$ and $a$, then $b$ must be the same as $a$.

This identity property is crucial for the axiomatic development of geometry. It captures the intuitive notion that the only point that can be between a point and itself is that point itself, which is essential for defining notions of segments and collinearity in a consistent way.

The non-Euclidean version (`TARSKI_AXIOM_6_NONEUCLIDEAN`) is analogous to the Euclidean version (`TARSKI_AXIOM_6_EUCLIDEAN`), but operates on points restricted to a plane.

### Dependencies
#### Theorems
- `TARSKI_AXIOM_6_EUCLIDEAN`: The Euclidean version of the same axiom, stating that if point $b$ is between point $a$ and point $a$, then $a = b$.

#### Definitions and Functions
- `pbetween`: Defines the betweenness relation in the plane.
- `FORALL_DEST_PLANE`: Handles universal quantification over points in the plane.
- `DEST_PLANE_EQ`: Establishes equality of points in the plane.

### Porting notes
When porting this theorem:
1. Ensure the corresponding Euclidean version (`TARSKI_AXIOM_6_EUCLIDEAN`) is implemented first.
2. Pay attention to how the planar betweenness relation `pbetween` is defined in your target system.
3. Handle the translation between general and planar geometry carefully, ensuring that the plane constraints are properly maintained.
4. The proof relies on the automated reasoner `MESON_TAC`, so you may need to provide more explicit steps in systems with different automation capabilities.

---

## TARSKI_AXIOM_7_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_7_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_7_NONEUCLIDEAN = prove
 (`!a b c p q.
    pbetween p (a,c) /\ pbetween q (b,c)
    ==> ?x. pbetween x (p,b) /\ pbetween x (q,a)`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; EXISTS_DEST_PLANE] THEN
  MESON_TAC[BETWEEN_NORM_LT; TARSKI_AXIOM_7_EUCLIDEAN]);;
```

### Informal statement
For all points $a$, $b$, $c$, $p$, and $q$, if $p$ is strictly between $a$ and $c$, and $q$ is strictly between $b$ and $c$, then there exists a point $x$ such that $x$ is strictly between $p$ and $b$, and $x$ is strictly between $q$ and $a$.

Here, "strictly between" (represented by `pbetween` in the formal statement) means that the three points are distinct and collinear, with one point lying between the other two.

### Informal proof
The proof works by reformulating the problem in terms of the standard betweenness relation:

- First, the theorem rewrites the statement using the definition of `pbetween` and applies destination-plane conversions to handle the specific types.
- The proof then uses the `BETWEEN_NORM_LT` theorem which relates strict betweenness (`pbetween`) to the standard betweenness relation plus a norm inequality.
- Finally, it applies `TARSKI_AXIOM_7_EUCLIDEAN`, which is the corresponding axiom for the non-strict betweenness relation in Euclidean geometry.

The `MESON_TAC` automated reasoning tactic combines these facts to complete the proof.

### Mathematical insight
This theorem represents Pasch's axiom, which is a fundamental property in axiomatic geometry. It states that if a line enters a triangle through one side, it must exit through another side. 

The "non-Euclidean" distinction in the name indicates this is the strict version of the axiom, where all points involved must be distinct. This contrasts with `TARSKI_AXIOM_7_EUCLIDEAN`, which allows for degenerate cases.

Pasch's axiom is not a theorem in the most basic axioms of geometry but is an independent axiom that captures an important property of plane geometry. It was historically significant because Euclid missed it in his axiomatization, despite using it implicitly in proofs.

### Dependencies
- **Theorems**:
  - `TARSKI_AXIOM_7_EUCLIDEAN`: The corresponding axiom using the non-strict betweenness relation
  - `BETWEEN_NORM_LT`: Relates strict betweenness to standard betweenness with norm inequality constraints

- **Definitions**:
  - `pbetween`: Definition of strict betweenness
  - `FORALL_DEST_PLANE`: Destination-plane conversion for universal quantification
  - `EXISTS_DEST_PLANE`: Destination-plane conversion for existential quantification

### Porting notes
When porting this to other proof assistants:
1. Ensure the distinction between strict betweenness (`pbetween`) and standard betweenness (`between`) is maintained
2. The proof relies on automated reasoning via `MESON_TAC` which may not have direct equivalents in other systems
3. The geometric foundations might differ between systems - particularly check how vector spaces and Euclidean geometry are formalized in the target system

---

## TARSKI_AXIOM_8_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_8_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_8_NONEUCLIDEAN = prove
 (`?a b c. ~pbetween b (a,c) /\ ~pbetween c (b,a) /\ ~pbetween a (c,b)`,
  REWRITE_TAC[pbetween; EXISTS_DEST_PLANE; NORM_LT_SQUARE; NORM_POW_2] THEN
  MAP_EVERY (fun t -> EXISTS_TAC t THEN
    SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV)
   [`vec 0:real^2`; `(&1 / &2) % basis 1:real^2`;
    `(&1 / &2) % basis 2:real^2`] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
  SIMP_TAC[COLLINEAR_3_2D; VECTOR_MUL_COMPONENT; VEC_COMPONENT; ARITH;
           BASIS_COMPONENT; DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
There exist three points $a$, $b$, and $c$ such that none of them lies between the other two. That is:
- $b$ does not lie between $a$ and $c$
- $c$ does not lie between $b$ and $a$
- $a$ does not lie between $c$ and $b$

This is a formulation of Tarski's 8th axiom in a non-Euclidean setting, essentially stating there are three non-collinear points.

### Informal proof
The proof shows the existence of three points that are not collinear, and therefore none of them can lie between the other two.

- The proof chooses three specific points in a 2D plane:
  - $a = (0, 0)$
  - $b = (1/2, 0)$
  - $c = (0, 1/2)$
  
- For each pair of points, the proof:
  1. Assumes one point lies between the other two
  2. Uses the fact that betweenness implies collinearity (`BETWEEN_IMP_COLLINEAR`)
  3. Shows these points are not collinear by examining their coordinates
  4. Derives a contradiction
  
- The specific coordinate calculations show that the three points form a right-angled triangle, and therefore cannot be collinear.

### Mathematical insight
This theorem represents Tarski's 8th axiom for geometry, which ensures that the space is at least two-dimensional. It establishes the existence of three non-collinear points, which is a fundamental property needed for plane geometry.

In Tarski's axiomatization of geometry, this axiom is crucial for distinguishing between 1-dimensional and higher-dimensional spaces. Without this axiom, all the other axioms could be satisfied by a 1-dimensional space (a line).

The proof constructs a simple right-angled triangle in the plane to demonstrate the existence of such three points, showing that the 2D Euclidean space satisfies this axiom.

### Dependencies
#### Theorems
- `BETWEEN_IMP_COLLINEAR`: If a point lies between two other points, then all three points are collinear
- `COLLINEAR_3_2D`: A condition for collinearity of three points in 2D space

#### Definitions
- `pbetween`: Betweenness relation for points
- `EXISTS_DEST_PLANE`: Related to existence in the plane

### Porting notes
When porting to another system:
1. Ensure the betweenness relation is properly defined in the target system
2. The proof relies on specific vector operations and the ability to work with coordinates in 2D space
3. The proof strategy is simple - explicitly construct three non-collinear points by giving their coordinates
4. In systems with different foundations for geometry, you might need to adapt the proof to use the available constructions rather than explicit coordinates

---

## TARSKI_AXIOM_9_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_9_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_9_NONEUCLIDEAN = prove
 (`!p q a b c.
        ~(p = q) /\
        pdist(a,p) = pdist(a,q) /\ pdist(b,p) = pdist(b,q) /\
        pdist(c,p) = pdist(c,q)
        ==> pbetween b (a,c) \/ pbetween c (b,a) \/ pbetween a (c,b)`,
  REWRITE_TAC[pdist; pbetween; FORALL_DEST_PLANE; GSYM DEST_PLANE_EQ] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^2`; `q:real^2`] HYPERBOLIC_MIDPOINT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `x:real^2` THEN
  STRIP_TAC THEN MP_TAC(ISPEC `x:real^2` HYPERBOLIC_TRANSLATION) THEN
  SUBGOAL_THEN `norm(x:real^2) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[BETWEEN_NORM_LT]; ONCE_REWRITE_TAC[BETWEEN_SYM]] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; hyperbolic_isometry] THEN
  REWRITE_TAC[GSYM COLLINEAR_BETWEEN_CASES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `collinear{(f:real^2->real^2) b,f c,f a}` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[COLLINEAR_BETWEEN_CASES]] THEN
  SUBGOAL_THEN `ddist(f a,f p) = ddist(f a,f q) /\
                ddist(f b,f p) = ddist(f b,f q) /\
                ddist(f c,f p) = ddist(f c,f q) /\
                ~((f:real^2->real^2) q = f p)`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^2) q = --(f p)` SUBST1_TAC THENL
   [SUBGOAL_THEN `between ((f:real^2->real^2) x) (f p,f q) /\
                  ddist(f x,f p) = ddist(f x,f q)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DDIST_EQ_ORIGIN] THEN
    REWRITE_TAC[GSYM MIDPOINT_BETWEEN; midpoint; NORM_ARITH
     `norm(a:real^N) = norm b <=> dist(a,vec 0) = dist(vec 0,b)`] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[ddist] THEN ASM_SIMP_TAC[NORM_NEG; real_div; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1; REAL_ABS_NORM; REAL_FIELD
     `&0 < x /\ &0 < y
      ==> (a * inv x * inv y - &1 = b * inv x * inv y - &1 <=> a = b)`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^N = x <=> x = vec 0`] THEN
    REWRITE_TAC[COLLINEAR_3_2D; VECTOR_SUB_COMPONENT; DOT_2; GSYM DOT_EQ_0;
                  VECTOR_NEG_COMPONENT] THEN CONV_TAC REAL_RING]);;
```

### Informal statement
For any points $p, q, a, b, c$ in the hyperbolic plane:

If $p \neq q$ and the hyperbolic distances from points $a$, $b$, and $c$ to point $p$ are equal to their respective distances to point $q$, i.e.,
- $\text{pdist}(a, p) = \text{pdist}(a, q)$
- $\text{pdist}(b, p) = \text{pdist}(b, q)$
- $\text{pdist}(c, p) = \text{pdist}(c, q)$

then at least one of the following betweenness relations holds:
- $b$ is between $a$ and $c$ (denoted as $\text{pbetween}\ b\ (a, c)$)
- $c$ is between $b$ and $a$ (denoted as $\text{pbetween}\ c\ (b, a)$)
- $a$ is between $c$ and $b$ (denoted as $\text{pbetween}\ a\ (c, b)$)

### Informal proof
This theorem is a non-Euclidean version of Tarski's "upper dimensional axiom" which establishes that in the hyperbolic plane, points equidistant from two fixed points are collinear. The proof proceeds as follows:

1. First, we rewrite using definitions of hyperbolic distance (`pdist`), betweenness (`pbetween`), and plane point equality to transform the problem into the underlying Euclidean representation.

2. For the given distinct points $p$ and $q$, we construct a hyperbolic midpoint $x$ between them using the `HYPERBOLIC_MIDPOINT` theorem.

3. We then apply a hyperbolic translation (isometry) that maps $x$ to the origin. After this transformation:
   - The norm of $x$ must be less than 1 (since $x$ is in the hyperbolic plane)
   - The point $p$ maps to some point $f(p)$
   - The point $q$ maps to $-f(p)$ (opposite direction from the origin)

4. Because $f$ is a hyperbolic isometry, it preserves hyperbolic distances. Thus, the points $f(a)$, $f(b)$, and $f(c)$ remain equidistant from $f(p)$ and $f(q)$.

5. In the hyperbolic Poincaré disk, points equidistant (in hyperbolic distance) from two points that are opposite with respect to the origin must lie on a straight line through the origin. 

6. Therefore, $f(a)$, $f(b)$, and $f(c)$ must be collinear.

7. Since these three points are collinear, they must satisfy one of the betweenness relations, and this betweenness is preserved when we map back to the original points $a$, $b$, and $c$.

### Mathematical insight
This theorem is a non-Euclidean version of Tarski's ninth axiom (the "upper dimensional axiom") adapted to the hyperbolic plane. In Tarski's axiomatization of Euclidean geometry, this axiom establishes that the dimension is at most 2.

In the hyperbolic plane context, this theorem shows that points equidistant from two fixed points $p$ and $q$ must lie on a straight line (in the hyperbolic sense). This line is the perpendicular bisector of the segment connecting $p$ and $q$.

The key insight is that hyperbolic translations preserve the properties needed for the proof, and after an appropriate translation, the problem reduces to showing that points equidistant from a point and its opposite (with respect to the origin) must be collinear. This is analogous to how, in Euclidean geometry, points equidistant from two fixed points form a straight line.

### Dependencies
- `pdist`: Hyperbolic distance in the Poincaré disk model
- `pbetween`: Hyperbolic betweenness relation
- `DEST_PLANE_EQ`, `FORALL_DEST_PLANE`: Theorems about points in the plane
- `HYPERBOLIC_MIDPOINT`: Theorem establishing existence of hyperbolic midpoint
- `HYPERBOLIC_TRANSLATION`: Theorem about existence of hyperbolic translations
- `hyperbolic_isometry`: Properties of hyperbolic isometries
- `COLLINEAR_BETWEEN_CASES`: Relationship between collinearity and betweenness
- `DDIST_EQ_ORIGIN`: Properties of origin-centered distance
- `MIDPOINT_BETWEEN`: Properties of midpoints and betweenness

### Porting notes
When porting this theorem:
1. Ensure your target system has an appropriate model of the hyperbolic plane (most commonly, the Poincaré disk model).
2. The proof heavily relies on applying hyperbolic isometries, so ensure your system has an equivalent notion.
3. The hyperbolic distance (`pdist`) and betweenness (`pbetween`) definitions may need to be established first.
4. Be careful with the handling of collinearity in the hyperbolic plane, which is used as a key step in this proof.

---

## NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Name of formal statement
NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_TARSKI_AXIOM_10_NONEUCLIDEAN = prove
 (`~(!a b c d t.
      pbetween d (a,t) /\ pbetween d (b,c) /\ ~(a = d)
      ==> ?x y. pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y))`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; EXISTS_DEST_PLANE;
              GSYM DEST_PLANE_EQ; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`vec 0:real^2`; `&1 / &2 % basis 1:real^2`; `&1 / &2 % basis 2:real^2`;
    `&1 / &4 % basis 1 + &1 / &4 % basis 2:real^2`;
    `&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2`]) THEN
  REWRITE_TAC[NOT_IMP; CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT(GEN_TAC THEN DISCH_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
    SIMP_TAC[COLLINEAR_3_2D; BASIS_COMPONENT; DIMINDEX_2; ARITH; VEC_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO;
                REAL_ARITH `&0 = &1 / &2 * x <=> x = &0`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`y:real^2`; `2`] COMPONENT_LE_NORM) THEN
    SIMP_TAC[DIMINDEX_2; ARITH; BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `norm(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2) pow 2 <= &1 / &2`
    MP_TAC THENL
     [SUBGOAL_THEN `(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$2 =
                    (&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$1`
      MP_TAC THENL
       [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; ARITH; BASIS_COMPONENT;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
      ASM_SIMP_TAC[DIMINDEX_2; FORALL_2; DOT_2; VECTOR_ADD_COMPONENT; ARITH;
                   VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
        `a * &0 + y = x + b * &0 ==> abs x + abs y <= (&1 - u) * &1 + u * &1
         ==> abs x <= abs(&1 / &2) /\ abs y <= abs(&1 / &2)`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN REAL_ARITH_TAC];
      ALL_TAC]] THEN
  SIMP_TAC[NORM_LT_SQUARE; NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LZERO;
           DOT_LMUL; DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `&5 / &12`; EXISTS_TAC `&1 / &2`; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; ARITH; BASIS_COMPONENT;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
This theorem states that Tarski's Axiom 10 (the Euclidean axiom) is not universally valid in plane geometry. Specifically, it negates the following statement:

For all points $a$, $b$, $c$, $d$, and $t$, if point $d$ lies between $a$ and $t$, and $d$ lies between $b$ and $c$, and $a \neq d$, then there exist points $x$ and $y$ such that:
- $b$ lies between $a$ and $x$
- $c$ lies between $a$ and $y$
- $t$ lies between $x$ and $y$

The statement uses the predicate `pbetween` which represents the betweenness relation in the plane.

### Informal proof
The proof constructs a specific counterexample in $\mathbb{R}^2$ showing that the Euclidean axiom does not hold in general.

* First, the statement is rewritten to work with the 2D plane representation.

* A specific counterexample is constructed with the following points:
  - $a = \vec{0}$ (the origin)
  - $b = \frac{1}{2} \vec{e}_1$ (where $\vec{e}_1$ is the first basis vector)
  - $c = \frac{1}{2} \vec{e}_2$ (where $\vec{e}_2$ is the second basis vector)
  - $d = \frac{1}{4} \vec{e}_1 + \frac{1}{4} \vec{e}_2$
  - $t = \frac{3}{5} \vec{e}_1 + \frac{3}{5} \vec{e}_2$

* The proof then shows:
  1. The betweenness conditions $d$ between $a$ and $t$, and $d$ between $b$ and $c$ are satisfied with the chosen points. 
     Specifically, $d$ between $a$ and $t$ is verified with parameter $\frac{5}{12}$, and $d$ between $b$ and $c$ with parameter $\frac{1}{2}$.
  
  2. No points $x$ and $y$ can satisfy the three required betweenness conditions simultaneously:
     - The betweenness relations would imply collinearity conditions.
     - Through coordinate calculations and norm inequalities, it is shown that the collinearity requirements lead to a contradiction.
     - In particular, the proof uses the fact that any points satisfying these conditions would need to have specific coordinate values, which would violate norm constraints.

### Mathematical insight
This theorem demonstrates a fundamental limitation in non-Euclidean geometry. Tarski's Axiom 10 is equivalent to Euclid's Fifth Postulate (the parallel postulate) in his axiomatization of geometry. By providing a specific counterexample, this result shows that Euclidean geometry is not the only consistent model of geometry.

The construction uses a clever choice of points in the Cartesian plane to show that there are scenarios where the geometric intuition provided by Euclidean geometry fails. This is important for understanding the logical independence of the parallel postulate from the other axioms of geometry, which was a significant discovery in the development of non-Euclidean geometries.

### Dependencies
- `pbetween`: The betweenness relation in the plane
- `BETWEEN_IMP_COLLINEAR`: Theorem that betweenness implies collinearity
- `BETWEEN_IN_SEGMENT`: Relation between betweenness and line segments
- `COLLINEAR_3_2D`: Collinearity condition for three points in 2D
- `COMPONENT_LE_NORM`: Relation between vector components and norm

### Porting notes
When porting this theorem to other systems:
1. Ensure that the betweenness relation and collinearity are properly defined.
2. The proof relies on specific calculations in 2D Euclidean space and vector operations that may need different representations in other systems.
3. The counterexample construction might need adaptation based on how vectors and points are represented in the target system.
4. Special attention should be given to the algebraic manipulations involving norms and dot products.

---

## TARSKI_AXIOM_11_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_11_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_11_NONEUCLIDEAN = prove
 (`!X Y. (?a. !x y. x IN X /\ y IN Y ==> pbetween x (a,y))
         ==> (?b. !x y. x IN X /\ y IN Y ==> pbetween b (x,y))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `X:plane->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `Y:plane->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[pbetween; EXISTS_DEST_PLANE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE dest_plane X`; `IMAGE dest_plane Y`]
        TARSKI_AXIOM_11_EUCLIDEAN) THEN REWRITE_TAC[IN_IMAGE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; DEST_PLANE_NORM_LT; BETWEEN_NORM_LT]);;
```

### Informal statement
For any two sets $X, Y$ in the plane, if there exists a point $a$ such that for all points $x \in X$ and $y \in Y$ we have that $x$ is between $a$ and $y$ (in the projective betweenness relation), then there exists a point $b$ such that for all points $x \in X$ and $y \in Y$, $b$ is between $x$ and $y$ (in the projective betweenness relation).

Formally:
$$\forall X,Y. (\exists a. \forall x,y. x \in X \wedge y \in Y \Rightarrow \text{pbetween}(x, (a, y))) \Rightarrow (\exists b. \forall x,y. x \in X \wedge y \in Y \Rightarrow \text{pbetween}(b, (x, y)))$$

where $\text{pbetween}$ represents the projective betweenness relation.

### Informal proof
The proof establishes the non-Euclidean version of Tarski's Axiom 11 (continuity axiom) using the Euclidean version:

- First, we handle trivial cases when either $X$ or $Y$ is empty, in which case the statement is vacuously true.
- For non-empty sets $X$ and $Y$, we convert the problem from projective betweenness (`pbetween`) to ordinary Euclidean betweenness by:
  - Expanding the definition of projective betweenness
  - Using the mapping `dest_plane` which converts points from the projective plane to $\mathbb{R}^2$
- We apply `TARSKI_AXIOM_11_EUCLIDEAN` to the images of sets $X$ and $Y$ under the `dest_plane` mapping
- The Euclidean version gives us a point $b$ in $\mathbb{R}^2$ that satisfies the betweenness requirement
- We then convert this result back to the projective plane context, verifying that the betweenness relation is preserved

The proof relies on the fact that the Euclidean betweenness relation in $\mathbb{R}^2$ can be used to establish the corresponding projective betweenness relation after applying the appropriate transformations.

### Mathematical insight
This theorem represents Tarski's Axiom 11 of continuity adapted for non-Euclidean (projective) geometry. The axiom captures an important continuity property of geometric spaces.

In the Euclidean version, the betweenness relation refers to points lying on a line segment. In the projective version (`pbetween`), this concept is extended to the projective plane. The theorem establishes that certain geometric configurations regarding betweenness that hold in Euclidean geometry have analogous versions in projective geometry.

The significance of this axiom is that it helps establish the consistency and completeness of the axiom system for geometry. Tarski's axioms provide a foundation for geometry that is equivalent to Euclidean geometry but expressed purely in terms of the betweenness and congruence relations.

### Dependencies
- `TARSKI_AXIOM_11_EUCLIDEAN`: The Euclidean version of the same axiom, which states that if there exists a point $a$ such that for all $x \in X$ and $y \in Y$ we have that $x$ is between $a$ and $y$, then there exists a point $b$ such that for all $x \in X$ and $y \in Y$, $b$ is between $x$ and $y$.
- `pbetween`: Definition of projective betweenness
- `dest_plane`: Function mapping points from the projective plane to $\mathbb{R}^2$
- `BETWEEN_NORM_LT`: Theorem relating betweenness to norm constraints
- `DEST_PLANE_NORM_LT`: Theorem about the norm of points mapped by `dest_plane`

### Porting notes
When porting this theorem:
1. Ensure that the projective betweenness relation (`pbetween`) is correctly defined in terms of the Euclidean betweenness relation
2. The mapping between projective plane and Euclidean space (`dest_plane`) must be correctly implemented
3. Pay attention to how empty sets are handled in the target system
4. The proof relies on the Euclidean version of the axiom, which must be ported first

---

